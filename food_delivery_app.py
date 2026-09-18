"""
=============================================================================
 BYTES & BITES -- a complete food delivery application in pure Python
=============================================================================

Zero third-party dependencies. Standard library only. Runs on Python 3.8+.

HOW TO RUN
----------
    python food_delivery_app.py              # interactive app (menu driven)
    python food_delivery_app.py --selftest   # run the built-in test suite
    python food_delivery_app.py --demo       # scripted end-to-end order, no input
    python food_delivery_app.py --reset      # wipe saved data and reseed
    python food_delivery_app.py --data X.json  # use a different data file

WHY IT IS BUILT THIS WAY
------------------------
1. Money is stored as integer paise, never as float. 0.1 + 0.2 != 0.3 in
   binary floating point, and a billing bug is the fastest way to lose a
   customer. Integers are exact; formatting happens only at display time.
2. Output is 100% ASCII. No rupee sign, no box-drawing characters. The
   Windows console (cp1252 / cp437) raises UnicodeEncodeError on those, so
   "Rs." is used instead. This is the single most common crash in Indian
   console apps.
3. Every dataclass owns its own to_dict() / from_dict(). dataclasses.asdict
   cannot serialise Enum or datetime, so hand-written converters keep the
   JSON round trip lossless.
4. All state lives in one DataStore that is saved to a single JSON file.
   Corrupt file -> it is backed up and the catalog is reseeded, never crashed.
5. Order status changes go through one transition table. An illegal jump
   (e.g. PLACED -> DELIVERED) raises instead of silently corrupting history.

SECURITY NOTES (the habits worth carrying into real systems)
------------------------------------------------------------
* Untrusted input is validated at the boundary: every menu choice, quantity,
  phone number and coupon code goes through a parser that rejects rather
  than assumes. This is the same discipline that stops injection bugs.
* The data file is opened with an explicit encoding and written atomically
  (temp file + replace) so a crash mid-write cannot leave a truncated store.
* The "payment gateway" is a simulation. It stores no card data at all --
  only a method name and a fake reference. Never log or persist a PAN.
* Coupon logic is server-side only. A client that says "discount = 100%"
  gets ignored; the engine recomputes every number from the catalog.

=============================================================================
"""

from __future__ import annotations

import argparse
import json
import os
import random
import re
import sys
import tempfile
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

# =============================================================================
# SECTION 1 -- CONSTANTS AND MONEY HELPERS
# =============================================================================

APP_NAME = "Bytes & Bites"
APP_VERSION = "1.0.0"
SCHEMA_VERSION = 2
DEFAULT_DATA_FILE = "bytes_and_bites_data.json"
CURRENCY = "Rs."

GST_PERCENT = 5                      # tax applied to food + packaging
PLATFORM_FEE_PAISE = 500             # flat Rs. 5.00 per order
DELIVERY_BASE_PAISE = 2000           # Rs. 20.00 covers the first 2 km
DELIVERY_BASE_KM = 2.0
DELIVERY_PER_KM_PAISE = 1000         # Rs. 10.00 for every extra km
DELIVERY_FEE_CAP_PAISE = 9000        # never charge more than Rs. 90.00
FREE_DELIVERY_THRESHOLD_PAISE = 49900  # free above Rs. 499.00
LOYALTY_PAISE_PER_POINT = 10000      # 1 point per Rs. 100.00 spent
LOYALTY_POINTS_PER_REDEEM = 100      # 100 points ...
LOYALTY_REDEEM_VALUE_PAISE = 5000    # ... converts to Rs. 50.00 of wallet
MINUTES_PER_KM = 4                   # rider speed model for the ETA
SCREEN_WIDTH = 74

PHONE_RE = re.compile(r"^[6-9]\d{9}$")     # Indian mobile numbers
PINCODE_RE = re.compile(r"^\d{6}$")
COUPON_RE = re.compile(r"^[A-Z0-9]{3,16}$")


def rupees(amount: float) -> int:
    """Convert a rupee amount to integer paise.

    Analogy: think of paise as millimetres and rupees as centimetres. You do
    all your measuring in the smaller unit so nothing gets lost to rounding,
    and you only convert back when a human needs to read it.

    >>> rupees(180)
    18000
    >>> rupees(99.5)
    9950
    """
    return int(round(float(amount) * 100))


def money(paise: int) -> str:
    """Format integer paise as a human readable amount.

    >>> money(18000)
    'Rs.180.00'
    >>> money(-750)
    '-Rs.7.50'
    """
    paise = int(paise)
    sign = "-" if paise < 0 else ""
    paise = abs(paise)
    return "{0}{1}{2}.{3:02d}".format(sign, CURRENCY, paise // 100, paise % 100)


def percent_of(paise: int, percent: int) -> int:
    """Take a percentage of an amount, rounded half-up, staying in integers."""
    return (int(paise) * int(percent) + 50) // 100


def new_id(prefix: str) -> str:
    """Short unique id. uuid4 is random, so ids never collide across runs."""
    return "{0}-{1}".format(prefix, uuid.uuid4().hex[:8].upper())


# =============================================================================
# SECTION 2 -- ENUMS AND THE ORDER STATE MACHINE
# =============================================================================


class OrderStatus(Enum):
    """The life of an order. Strings are stored in JSON, not the enum itself."""

    DRAFT = "draft"
    PLACED = "placed"
    CONFIRMED = "confirmed"
    PREPARING = "preparing"
    READY_FOR_PICKUP = "ready_for_pickup"
    OUT_FOR_DELIVERY = "out_for_delivery"
    DELIVERED = "delivered"
    CANCELLED = "cancelled"

    @property
    def label(self) -> str:
        return self.value.replace("_", " ").title()


class PaymentMethod(Enum):
    CASH = "cash_on_delivery"
    CARD = "card"
    UPI = "upi"
    WALLET = "wallet"

    @property
    def label(self) -> str:
        if self is PaymentMethod.CASH:
            return "Cash on Delivery"
        if self is PaymentMethod.UPI:
            return "UPI"
        return self.value.title()

    @property
    def is_prepaid(self) -> bool:
        return self is not PaymentMethod.CASH


class PaymentStatus(Enum):
    PENDING = "pending"
    PAID = "paid"
    FAILED = "failed"
    REFUNDED = "refunded"

    @property
    def label(self) -> str:
        return self.value.title()


# One table, one source of truth. Anything not listed here is illegal.
STATUS_FLOW: Dict[OrderStatus, Tuple[OrderStatus, ...]] = {
    OrderStatus.DRAFT: (OrderStatus.PLACED, OrderStatus.CANCELLED),
    OrderStatus.PLACED: (OrderStatus.CONFIRMED, OrderStatus.CANCELLED),
    OrderStatus.CONFIRMED: (OrderStatus.PREPARING, OrderStatus.CANCELLED),
    OrderStatus.PREPARING: (OrderStatus.READY_FOR_PICKUP, OrderStatus.CANCELLED),
    OrderStatus.READY_FOR_PICKUP: (OrderStatus.OUT_FOR_DELIVERY,),
    OrderStatus.OUT_FOR_DELIVERY: (OrderStatus.DELIVERED,),
    OrderStatus.DELIVERED: (),
    OrderStatus.CANCELLED: (),
}

CANCELLABLE = (OrderStatus.PLACED, OrderStatus.CONFIRMED, OrderStatus.PREPARING)


class AppError(Exception):
    """Every expected, recoverable problem. Caught and shown, never a traceback."""


class UserQuit(Exception):
    """Raised on Ctrl-C / Ctrl-D so the app can save state and exit politely."""


# =============================================================================
# SECTION 3 -- DOMAIN MODELS
# =============================================================================


@dataclass
class MenuItem:
    item_id: str
    name: str
    price_paise: int
    category: str
    veg: bool = True
    prep_minutes: int = 10
    spicy: bool = False
    available: bool = True

    def to_dict(self) -> Dict[str, Any]:
        return {
            "item_id": self.item_id,
            "name": self.name,
            "price_paise": self.price_paise,
            "category": self.category,
            "veg": self.veg,
            "prep_minutes": self.prep_minutes,
            "spicy": self.spicy,
            "available": self.available,
        }

    @staticmethod
    def from_dict(raw: Dict[str, Any]) -> "MenuItem":
        return MenuItem(
            item_id=str(raw["item_id"]),
            name=str(raw["name"]),
            price_paise=int(raw["price_paise"]),
            category=str(raw.get("category", "Other")),
            veg=bool(raw.get("veg", True)),
            prep_minutes=int(raw.get("prep_minutes", 10)),
            spicy=bool(raw.get("spicy", False)),
            available=bool(raw.get("available", True)),
        )

    @property
    def diet_tag(self) -> str:
        return "VEG" if self.veg else "NON-VEG"


@dataclass
class Restaurant:
    restaurant_id: str
    name: str
    cuisine: str
    area: str
    rating: float
    packaging_fee_paise: int
    menu: List[MenuItem] = field(default_factory=list)
    open_hour: int = 9
    close_hour: int = 23

    def to_dict(self) -> Dict[str, Any]:
        return {
            "restaurant_id": self.restaurant_id,
            "name": self.name,
            "cuisine": self.cuisine,
            "area": self.area,
            "rating": self.rating,
            "packaging_fee_paise": self.packaging_fee_paise,
            "open_hour": self.open_hour,
            "close_hour": self.close_hour,
            "menu": [m.to_dict() for m in self.menu],
        }

    @staticmethod
    def from_dict(raw: Dict[str, Any]) -> "Restaurant":
        return Restaurant(
            restaurant_id=str(raw["restaurant_id"]),
            name=str(raw["name"]),
            cuisine=str(raw.get("cuisine", "Mixed")),
            area=str(raw.get("area", "")),
            rating=float(raw.get("rating", 4.0)),
            packaging_fee_paise=int(raw.get("packaging_fee_paise", 0)),
            open_hour=int(raw.get("open_hour", 9)),
            close_hour=int(raw.get("close_hour", 23)),
            menu=[MenuItem.from_dict(m) for m in raw.get("menu", [])],
        )

    def find_item(self, item_id: str) -> Optional[MenuItem]:
        for item in self.menu:
            if item.item_id.lower() == item_id.lower():
                return item
        return None

    def available_items(self) -> List[MenuItem]:
        return [i for i in self.menu if i.available]

    def categories(self) -> List[str]:
        seen: List[str] = []
        for item in self.menu:
            if item.category not in seen:
                seen.append(item.category)
        return seen

    def is_open(self, when: Optional[datetime] = None) -> bool:
        hour = (when or datetime.now()).hour
        return self.open_hour <= hour < self.close_hour

    def cheapest_paise(self) -> int:
        items = self.available_items()
        return min((i.price_paise for i in items), default=0)


@dataclass
class Address:
    label: str
    line1: str
    area: str
    city: str
    pincode: str
    distance_km: float

    def to_dict(self) -> Dict[str, Any]:
        return {
            "label": self.label,
            "line1": self.line1,
            "area": self.area,
            "city": self.city,
            "pincode": self.pincode,
            "distance_km": self.distance_km,
        }

    @staticmethod
    def from_dict(raw: Dict[str, Any]) -> "Address":
        return Address(
            label=str(raw.get("label", "Home")),
            line1=str(raw.get("line1", "")),
            area=str(raw.get("area", "")),
            city=str(raw.get("city", "")),
            pincode=str(raw.get("pincode", "")),
            distance_km=float(raw.get("distance_km", 3.0)),
        )

    def one_line(self) -> str:
        return "{0}, {1}, {2} - {3}".format(self.line1, self.area, self.city, self.pincode)


@dataclass
class Customer:
    customer_id: str
    name: str
    phone: str
    addresses: List[Address] = field(default_factory=list)
    wallet_paise: int = 0
    loyalty_points: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "customer_id": self.customer_id,
            "name": self.name,
            "phone": self.phone,
            "wallet_paise": self.wallet_paise,
            "loyalty_points": self.loyalty_points,
            "addresses": [a.to_dict() for a in self.addresses],
        }

    @staticmethod
    def from_dict(raw: Dict[str, Any]) -> "Customer":
        return Customer(
            customer_id=str(raw["customer_id"]),
            name=str(raw["name"]),
            phone=str(raw.get("phone", "")),
            wallet_paise=int(raw.get("wallet_paise", 0)),
            loyalty_points=int(raw.get("loyalty_points", 0)),
            addresses=[Address.from_dict(a) for a in raw.get("addresses", [])],
        )

    def default_address(self) -> Optional[Address]:
        return self.addresses[0] if self.addresses else None


@dataclass
class Rider:
    rider_id: str
    name: str
    vehicle: str
    area: str
    rating: float = 4.5
    busy: bool = False
    deliveries: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "rider_id": self.rider_id,
            "name": self.name,
            "vehicle": self.vehicle,
            "area": self.area,
            "rating": self.rating,
            "busy": self.busy,
            "deliveries": self.deliveries,
        }

    @staticmethod
    def from_dict(raw: Dict[str, Any]) -> "Rider":
        return Rider(
            rider_id=str(raw["rider_id"]),
            name=str(raw["name"]),
            vehicle=str(raw.get("vehicle", "Bike")),
            area=str(raw.get("area", "")),
            rating=float(raw.get("rating", 4.5)),
            busy=bool(raw.get("busy", False)),
            deliveries=int(raw.get("deliveries", 0)),
        )


@dataclass
class Coupon:
    code: str
    description: str
    percent_off: int = 0
    flat_off_paise: int = 0
    min_order_paise: int = 0
    max_discount_paise: int = 0
    free_delivery: bool = False
    active: bool = True

    def to_dict(self) -> Dict[str, Any]:
        return {
            "code": self.code,
            "description": self.description,
            "percent_off": self.percent_off,
            "flat_off_paise": self.flat_off_paise,
            "min_order_paise": self.min_order_paise,
            "max_discount_paise": self.max_discount_paise,
            "free_delivery": self.free_delivery,
            "active": self.active,
        }

    @staticmethod
    def from_dict(raw: Dict[str, Any]) -> "Coupon":
        return Coupon(
            code=str(raw["code"]).upper(),
            description=str(raw.get("description", "")),
            percent_off=int(raw.get("percent_off", 0)),
            flat_off_paise=int(raw.get("flat_off_paise", 0)),
            min_order_paise=int(raw.get("min_order_paise", 0)),
            max_discount_paise=int(raw.get("max_discount_paise", 0)),
            free_delivery=bool(raw.get("free_delivery", False)),
            active=bool(raw.get("active", True)),
        )


@dataclass
class CartLine:
    item_id: str
    name: str
    unit_price_paise: int
    quantity: int
    notes: str = ""

    @property
    def line_total_paise(self) -> int:
        return self.unit_price_paise * self.quantity

    def to_dict(self) -> Dict[str, Any]:
        return {
            "item_id": self.item_id,
            "name": self.name,
            "unit_price_paise": self.unit_price_paise,
            "quantity": self.quantity,
            "notes": self.notes,
        }

    @staticmethod
    def from_dict(raw: Dict[str, Any]) -> "CartLine":
        return CartLine(
            item_id=str(raw["item_id"]),
            name=str(raw["name"]),
            unit_price_paise=int(raw["unit_price_paise"]),
            quantity=int(raw["quantity"]),
            notes=str(raw.get("notes", "")),
        )


@dataclass
class Cart:
    """Session-scoped basket. One cart belongs to exactly one restaurant."""

    customer_id: str
    restaurant_id: Optional[str] = None
    lines: List[CartLine] = field(default_factory=list)

    def find(self, item_id: str) -> Optional[CartLine]:
        for line in self.lines:
            if line.item_id == item_id:
                return line
        return None

    def add(self, item: MenuItem, quantity: int = 1, notes: str = "") -> CartLine:
        if quantity < 1:
            raise AppError("Quantity must be at least 1.")
        if not item.available:
            raise AppError("'{0}' is out of stock right now.".format(item.name))
        existing = self.find(item.item_id)
        if existing is not None:
            existing.quantity += quantity
            if notes:
                existing.notes = notes
            return existing
        line = CartLine(item.item_id, item.name, item.price_paise, quantity, notes)
        self.lines.append(line)
        return line

    def set_quantity(self, item_id: str, quantity: int) -> None:
        line = self.find(item_id)
        if line is None:
            raise AppError("That item is not in your cart.")
        if quantity <= 0:
            self.lines.remove(line)
            # Invariant: a cart with no lines belongs to no restaurant. Without
            # this, emptying the cart by hand still left the old restaurant id
            # behind, and the next restaurant wrongly asked "clear your cart?"
            if not self.lines:
                self.restaurant_id = None
        else:
            line.quantity = quantity

    def remove(self, item_id: str) -> None:
        self.set_quantity(item_id, 0)

    def clear(self) -> None:
        self.lines = []
        self.restaurant_id = None

    def subtotal_paise(self) -> int:
        return sum(line.line_total_paise for line in self.lines)

    def item_count(self) -> int:
        return sum(line.quantity for line in self.lines)

    def is_empty(self) -> bool:
        return not self.lines


@dataclass
class Bill:
    """An immutable snapshot of what the customer was charged and why."""

    subtotal_paise: int = 0
    discount_paise: int = 0
    packaging_paise: int = 0
    delivery_paise: int = 0
    platform_paise: int = 0
    tax_paise: int = 0
    total_paise: int = 0
    coupon_code: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "subtotal_paise": self.subtotal_paise,
            "discount_paise": self.discount_paise,
            "packaging_paise": self.packaging_paise,
            "delivery_paise": self.delivery_paise,
            "platform_paise": self.platform_paise,
            "tax_paise": self.tax_paise,
            "total_paise": self.total_paise,
            "coupon_code": self.coupon_code,
        }

    @staticmethod
    def from_dict(raw: Dict[str, Any]) -> "Bill":
        return Bill(
            subtotal_paise=int(raw.get("subtotal_paise", 0)),
            discount_paise=int(raw.get("discount_paise", 0)),
            packaging_paise=int(raw.get("packaging_paise", 0)),
            delivery_paise=int(raw.get("delivery_paise", 0)),
            platform_paise=int(raw.get("platform_paise", 0)),
            tax_paise=int(raw.get("tax_paise", 0)),
            total_paise=int(raw.get("total_paise", 0)),
            coupon_code=str(raw.get("coupon_code", "")),
        )

    def lines(self) -> List[Tuple[str, str]]:
        rows = [("Item subtotal", money(self.subtotal_paise))]
        if self.discount_paise:
            label = "Discount"
            if self.coupon_code:
                label = "Discount ({0})".format(self.coupon_code)
            rows.append((label, "-" + money(self.discount_paise)))
        rows.append(("Packaging", money(self.packaging_paise)))
        rows.append(("Delivery", money(self.delivery_paise) if self.delivery_paise else "FREE"))
        rows.append(("Platform fee", money(self.platform_paise)))
        rows.append(("GST @ {0}%".format(GST_PERCENT), money(self.tax_paise)))
        rows.append(("TOTAL PAYABLE", money(self.total_paise)))
        return rows


@dataclass
class OrderEvent:
    at: datetime
    status: OrderStatus
    note: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {"at": self.at.isoformat(), "status": self.status.value, "note": self.note}

    @staticmethod
    def from_dict(raw: Dict[str, Any]) -> "OrderEvent":
        return OrderEvent(
            at=datetime.fromisoformat(raw["at"]),
            status=OrderStatus(raw["status"]),
            note=str(raw.get("note", "")),
        )


@dataclass
class Order:
    order_id: str
    customer_id: str
    restaurant_id: str
    restaurant_name: str
    lines: List[CartLine]
    address: Address
    bill: Bill
    payment_method: PaymentMethod
    payment_status: PaymentStatus = PaymentStatus.PENDING
    payment_ref: str = ""
    status: OrderStatus = OrderStatus.DRAFT
    events: List[OrderEvent] = field(default_factory=list)
    rider_id: Optional[str] = None
    eta_minutes: int = 0
    placed_at: datetime = field(default_factory=datetime.now)
    rating: Optional[int] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "order_id": self.order_id,
            "customer_id": self.customer_id,
            "restaurant_id": self.restaurant_id,
            "restaurant_name": self.restaurant_name,
            "lines": [line.to_dict() for line in self.lines],
            "address": self.address.to_dict(),
            "bill": self.bill.to_dict(),
            "payment_method": self.payment_method.value,
            "payment_status": self.payment_status.value,
            "payment_ref": self.payment_ref,
            "status": self.status.value,
            "events": [e.to_dict() for e in self.events],
            "rider_id": self.rider_id,
            "eta_minutes": self.eta_minutes,
            "placed_at": self.placed_at.isoformat(),
            "rating": self.rating,
        }

    @staticmethod
    def from_dict(raw: Dict[str, Any]) -> "Order":
        return Order(
            order_id=str(raw["order_id"]),
            customer_id=str(raw["customer_id"]),
            restaurant_id=str(raw["restaurant_id"]),
            restaurant_name=str(raw.get("restaurant_name", "")),
            lines=[CartLine.from_dict(l) for l in raw.get("lines", [])],
            address=Address.from_dict(raw.get("address", {})),
            bill=Bill.from_dict(raw.get("bill", {})),
            payment_method=PaymentMethod(raw.get("payment_method", "cash_on_delivery")),
            payment_status=PaymentStatus(raw.get("payment_status", "pending")),
            payment_ref=str(raw.get("payment_ref", "")),
            status=OrderStatus(raw.get("status", "draft")),
            events=[OrderEvent.from_dict(e) for e in raw.get("events", [])],
            rider_id=raw.get("rider_id"),
            eta_minutes=int(raw.get("eta_minutes", 0)),
            placed_at=datetime.fromisoformat(raw["placed_at"]),
            rating=raw.get("rating"),
        )

    @property
    def is_active(self) -> bool:
        return self.status not in (OrderStatus.DELIVERED, OrderStatus.CANCELLED)

    def item_count(self) -> int:
        return sum(line.quantity for line in self.lines)

    def summary_line(self) -> str:
        return "{0}  {1:<22} {2:>2} item(s)  {3:>11}  {4}".format(
            self.order_id,
            self.restaurant_name[:22],
            self.item_count(),
            money(self.bill.total_paise),
            self.status.label,
        )

    def eta_clock(self) -> str:
        return (self.placed_at + timedelta(minutes=self.eta_minutes)).strftime("%H:%M")


# =============================================================================
# SECTION 4 -- PERSISTENCE (the DataStore)
# =============================================================================


class DataStore:
    """Everything the app knows, plus lossless load/save to one JSON file."""

    def __init__(self, path: str = DEFAULT_DATA_FILE) -> None:
        self.path = path
        self.customers: Dict[str, Customer] = {}
        self.restaurants: Dict[str, Restaurant] = {}
        self.riders: Dict[str, Rider] = {}
        self.coupons: Dict[str, Coupon] = {}
        self.orders: Dict[str, Order] = {}

    # ---------------------------------------------------------------- lookups
    def customer(self, customer_id: str) -> Customer:
        try:
            return self.customers[customer_id]
        except KeyError:
            raise AppError("No such customer: {0}".format(customer_id))

    def restaurant(self, restaurant_id: str) -> Restaurant:
        try:
            return self.restaurants[restaurant_id]
        except KeyError:
            raise AppError("No such restaurant: {0}".format(restaurant_id))

    def order(self, order_id: str) -> Order:
        try:
            return self.orders[order_id.upper()]
        except KeyError:
            raise AppError("No such order: {0}".format(order_id))

    def coupon(self, code: str) -> Coupon:
        try:
            return self.coupons[code.strip().upper()]
        except KeyError:
            raise AppError("Coupon '{0}' does not exist.".format(code.strip().upper()))

    def orders_of(self, customer_id: str) -> List[Order]:
        found = [o for o in self.orders.values() if o.customer_id == customer_id]
        found.sort(key=lambda o: o.placed_at, reverse=True)
        return found

    def search_restaurants(self, term: str) -> List[Restaurant]:
        """Match on restaurant name, cuisine, area, or any dish name."""
        term = term.strip().lower()
        if not term:
            return list(self.restaurants.values())
        hits = []
        for r in self.restaurants.values():
            haystack = " ".join([r.name, r.cuisine, r.area]).lower()
            dish_hit = any(term in i.name.lower() for i in r.menu)
            if term in haystack or dish_hit:
                hits.append(r)
        return hits

    # ------------------------------------------------------------ (de)serialise
    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema_version": SCHEMA_VERSION,
            "saved_at": datetime.now().isoformat(),
            "customers": [c.to_dict() for c in self.customers.values()],
            "restaurants": [r.to_dict() for r in self.restaurants.values()],
            "riders": [r.to_dict() for r in self.riders.values()],
            "coupons": [c.to_dict() for c in self.coupons.values()],
            "orders": [o.to_dict() for o in self.orders.values()],
        }

    def load_dict(self, raw: Dict[str, Any]) -> None:
        self.customers = {}
        self.restaurants = {}
        self.riders = {}
        self.coupons = {}
        self.orders = {}
        for item in raw.get("customers", []):
            c = Customer.from_dict(item)
            self.customers[c.customer_id] = c
        for item in raw.get("restaurants", []):
            r = Restaurant.from_dict(item)
            self.restaurants[r.restaurant_id] = r
        for item in raw.get("riders", []):
            rd = Rider.from_dict(item)
            self.riders[rd.rider_id] = rd
        for item in raw.get("coupons", []):
            cp = Coupon.from_dict(item)
            self.coupons[cp.code] = cp
        for item in raw.get("orders", []):
            o = Order.from_dict(item)
            self.orders[o.order_id] = o

    def save(self) -> bool:
        """Atomic write: build a temp file, then replace. No half-written JSON."""
        payload = json.dumps(self.to_dict(), indent=2)
        directory = os.path.dirname(os.path.abspath(self.path)) or "."
        try:
            handle, tmp_path = tempfile.mkstemp(prefix=".bnb-", suffix=".tmp", dir=directory)
            with os.fdopen(handle, "w", encoding="utf-8") as fh:
                fh.write(payload)
            os.replace(tmp_path, self.path)
            return True
        except OSError as exc:
            print("  [warn] could not save data: {0}".format(exc))
            return False

    def load(self) -> str:
        """Return a one-word status: 'loaded', 'seeded' or 'recovered'."""
        if not os.path.exists(self.path):
            self.seed()
            self.save()
            return "seeded"
        try:
            with open(self.path, "r", encoding="utf-8") as fh:
                raw = json.load(fh)
            if int(raw.get("schema_version", 0)) != SCHEMA_VERSION:
                raise ValueError("schema version mismatch")
            self.load_dict(raw)
            if not self.restaurants:
                raise ValueError("empty catalog")
            return "loaded"
        except (ValueError, OSError, KeyError, TypeError):
            backup = self.path + ".bak"
            try:
                os.replace(self.path, backup)
            except OSError:
                pass
            self.seed()
            self.save()
            return "recovered"

    # -------------------------------------------------------------- seed data
    def seed(self) -> None:
        """Build a believable starting catalog so the app is useful instantly."""
        self.customers = {}
        self.restaurants = {}
        self.riders = {}
        self.coupons = {}
        self.orders = {}

        spice = Restaurant(
            restaurant_id="R001",
            name="Spice Route",
            cuisine="North Indian",
            area="Virar West",
            rating=4.4,
            packaging_fee_paise=rupees(15),
            open_hour=10,
            close_hour=23,
            menu=[
                MenuItem("R001-01", "Paneer Butter Masala", rupees(240), "Mains", True, 18),
                MenuItem("R001-02", "Dal Tadka", rupees(180), "Mains", True, 14),
                MenuItem("R001-03", "Chicken Handi", rupees(310), "Mains", False, 22),
                MenuItem("R001-04", "Butter Naan", rupees(45), "Breads", True, 6),
                MenuItem("R001-05", "Tandoori Roti", rupees(30), "Breads", True, 5),
                MenuItem("R001-06", "Jeera Rice", rupees(150), "Rice", True, 12),
                MenuItem("R001-07", "Gulab Jamun (2 pc)", rupees(90), "Desserts", True, 4),
                MenuItem("R001-08", "Masala Papad", rupees(60), "Starters", True, 5),
            ],
        )
        wok = Restaurant(
            restaurant_id="R002",
            name="Wok & Roll",
            cuisine="Pan Asian",
            area="Nalasopara East",
            rating=4.1,
            packaging_fee_paise=rupees(20),
            open_hour=11,
            close_hour=23,
            menu=[
                MenuItem("R002-01", "Veg Hakka Noodles", rupees(190), "Noodles", True, 12),
                MenuItem("R002-02", "Chicken Schezwan Noodles", rupees(240), "Noodles", False, 14, True),
                MenuItem("R002-03", "Paneer Chilli Dry", rupees(230), "Starters", True, 15, True),
                MenuItem("R002-04", "Veg Momos (8 pc)", rupees(140), "Starters", True, 10),
                MenuItem("R002-05", "Burnt Garlic Fried Rice", rupees(200), "Rice", True, 12),
                MenuItem("R002-06", "Thai Green Curry", rupees(280), "Mains", True, 20),
                MenuItem("R002-07", "Honey Chilli Potato", rupees(160), "Starters", True, 11),
            ],
        )
        crust = Restaurant(
            restaurant_id="R003",
            name="Crust & Crumb",
            cuisine="Italian",
            area="Virar East",
            rating=4.6,
            packaging_fee_paise=rupees(25),
            open_hour=11,
            close_hour=24,
            menu=[
                MenuItem("R003-01", "Margherita Pizza (10 in)", rupees(320), "Pizza", True, 18),
                MenuItem("R003-02", "Farmhouse Pizza (10 in)", rupees(390), "Pizza", True, 20),
                MenuItem("R003-03", "Chicken Pepperoni Pizza", rupees(450), "Pizza", False, 22),
                MenuItem("R003-04", "Penne Alfredo", rupees(310), "Pasta", True, 16),
                MenuItem("R003-05", "Garlic Bread", rupees(130), "Sides", True, 8),
                MenuItem("R003-06", "Tiramisu", rupees(220), "Desserts", True, 4),
                MenuItem("R003-07", "Cheesy Dip", rupees(50), "Sides", True, 2),
            ],
        )
        tiffin = Restaurant(
            restaurant_id="R004",
            name="Anna's Tiffin House",
            cuisine="South Indian",
            area="Virar West",
            rating=4.7,
            packaging_fee_paise=rupees(10),
            open_hour=7,
            close_hour=22,
            menu=[
                MenuItem("R004-01", "Masala Dosa", rupees(120), "Dosa", True, 10),
                MenuItem("R004-02", "Mysore Masala Dosa", rupees(150), "Dosa", True, 12, True),
                MenuItem("R004-03", "Idli Sambar (3 pc)", rupees(90), "Tiffin", True, 7),
                MenuItem("R004-04", "Medu Vada (2 pc)", rupees(80), "Tiffin", True, 8),
                MenuItem("R004-05", "Filter Coffee", rupees(50), "Beverages", True, 3),
                MenuItem("R004-06", "Rava Kesari", rupees(70), "Desserts", True, 5),
                MenuItem("R004-07", "Curd Rice", rupees(110), "Rice", True, 6),
            ],
        )
        grill = Restaurant(
            restaurant_id="R005",
            name="Smoke & Grill",
            cuisine="Barbecue",
            area="Vasai West",
            rating=4.2,
            packaging_fee_paise=rupees(30),
            open_hour=12,
            close_hour=23,
            menu=[
                MenuItem("R005-01", "Chicken Tikka (6 pc)", rupees(340), "Grills", False, 20, True),
                MenuItem("R005-02", "Paneer Tikka (6 pc)", rupees(300), "Grills", True, 18),
                MenuItem("R005-03", "Mutton Seekh Kebab", rupees(420), "Grills", False, 25),
                MenuItem("R005-04", "Grilled Veg Platter", rupees(360), "Platters", True, 22),
                MenuItem("R005-05", "Mint Chutney", rupees(30), "Sides", True, 2),
                MenuItem("R005-06", "Cold Coffee", rupees(140), "Beverages", True, 5),
                # Keyword arguments here on purpose: this dish is seeded SOLD OUT,
                # and counting positional arguments is exactly how you end up
                # setting 'spicy' when you meant 'available'.
                MenuItem("R005-07", "Chocolate Brownie", rupees(180), "Desserts",
                         veg=True, prep_minutes=4, available=False),
            ],
        )
        for r in (spice, wok, crust, tiffin, grill):
            self.restaurants[r.restaurant_id] = r

        malhar = Customer(
            customer_id="C001",
            name="Malhar",
            phone="9820011223",
            wallet_paise=rupees(500),
            loyalty_points=120,
            addresses=[
                Address("Home", "Flat 402, Sai Residency", "Virar West", "Palghar", "401303", 2.5),
                Address("Work", "3rd Floor, Tech Park", "Vasai East", "Palghar", "401208", 7.5),
            ],
        )
        guest = Customer(
            customer_id="C002",
            name="Guest User",
            phone="9700099887",
            wallet_paise=rupees(100),
            addresses=[Address("Home", "B-12, Green Meadows", "Nalasopara West", "Palghar", "401203", 4.0)],
        )
        for c in (malhar, guest):
            self.customers[c.customer_id] = c

        riders = [
            Rider("D001", "Arjun", "Bike", "Virar West", 4.8),
            Rider("D002", "Sneha", "Scooter", "Virar East", 4.6),
            Rider("D003", "Imran", "Bike", "Nalasopara East", 4.4),
            Rider("D004", "Kavya", "EV Scooter", "Vasai West", 4.9),
        ]
        for rd in riders:
            self.riders[rd.rider_id] = rd

        coupons = [
            Coupon("WELCOME50", "50% off up to Rs.100 on your first order",
                   percent_off=50, min_order_paise=rupees(199), max_discount_paise=rupees(100)),
            Coupon("FLAT75", "Flat Rs.75 off above Rs.399",
                   flat_off_paise=rupees(75), min_order_paise=rupees(399)),
            Coupon("FREESHIP", "Free delivery, no minimum", free_delivery=True),
            Coupon("PARTY20", "20% off up to Rs.250 above Rs.799",
                   percent_off=20, min_order_paise=rupees(799), max_discount_paise=rupees(250)),
            Coupon("EXPIRED10", "Retired offer, kept to show inactive handling",
                   percent_off=10, active=False),
        ]
        for cp in coupons:
            self.coupons[cp.code] = cp


# =============================================================================
# SECTION 5 -- PRICING AND COUPONS
# =============================================================================


def delivery_fee_paise(distance_km: float, subtotal_paise: int) -> int:
    """Base fare for the first 2 km, then per-km, capped, free on big orders."""
    if subtotal_paise >= FREE_DELIVERY_THRESHOLD_PAISE:
        return 0
    extra_km = max(0.0, float(distance_km) - DELIVERY_BASE_KM)
    fee = DELIVERY_BASE_PAISE + int(round(extra_km * DELIVERY_PER_KM_PAISE))
    return min(fee, DELIVERY_FEE_CAP_PAISE)


class CouponEngine:
    """Validates and prices coupons. The client never decides a discount."""

    @staticmethod
    def check(coupon: Coupon, subtotal_paise: int) -> None:
        if not coupon.active:
            raise AppError("Coupon {0} is no longer active.".format(coupon.code))
        if subtotal_paise < coupon.min_order_paise:
            raise AppError(
                "Coupon {0} needs a minimum order of {1} (cart is {2}).".format(
                    coupon.code, money(coupon.min_order_paise), money(subtotal_paise)
                )
            )

    @staticmethod
    def discount_paise(coupon: Coupon, subtotal_paise: int) -> int:
        CouponEngine.check(coupon, subtotal_paise)
        discount = 0
        if coupon.percent_off:
            discount = percent_of(subtotal_paise, coupon.percent_off)
            if coupon.max_discount_paise:
                discount = min(discount, coupon.max_discount_paise)
        discount += coupon.flat_off_paise
        # A discount can never exceed the food value. Guarding this prevents
        # negative totals, which is a classic place for abuse.
        return min(discount, subtotal_paise)

    @staticmethod
    def eligible(coupons: Sequence[Coupon], subtotal_paise: int) -> List[Coupon]:
        out = []
        for c in coupons:
            try:
                CouponEngine.check(c, subtotal_paise)
                out.append(c)
            except AppError:
                continue
        return out


def build_bill(
    restaurant: Restaurant,
    lines: Sequence[CartLine],
    distance_km: float,
    coupon: Optional[Coupon] = None,
) -> Bill:
    """Single place where a total is computed. Everything else calls this."""
    subtotal = sum(line.line_total_paise for line in lines)
    if subtotal <= 0:
        raise AppError("Cannot price an empty cart.")

    discount = 0
    code = ""
    free_ship = False
    if coupon is not None:
        discount = CouponEngine.discount_paise(coupon, subtotal)
        code = coupon.code
        free_ship = coupon.free_delivery

    packaging = restaurant.packaging_fee_paise
    delivery = 0 if free_ship else delivery_fee_paise(distance_km, subtotal)
    taxable = subtotal - discount + packaging
    tax = percent_of(taxable, GST_PERCENT)
    total = taxable + delivery + PLATFORM_FEE_PAISE + tax

    return Bill(
        subtotal_paise=subtotal,
        discount_paise=discount,
        packaging_paise=packaging,
        delivery_paise=delivery,
        platform_paise=PLATFORM_FEE_PAISE,
        tax_paise=tax,
        total_paise=total,
        coupon_code=code,
    )


def estimate_eta_minutes(restaurant: Restaurant, lines: Sequence[CartLine], distance_km: float) -> int:
    """Prep time is driven by the slowest dish, not the sum of all dishes --
    a kitchen cooks in parallel. Then add travel time and a small buffer."""
    prep = 0
    for line in lines:
        item = restaurant.find_item(line.item_id)
        if item is not None:
            prep = max(prep, item.prep_minutes)
    travel = int(round(float(distance_km) * MINUTES_PER_KM))
    return max(15, prep + travel + 5)


# =============================================================================
# SECTION 6 -- PAYMENTS (simulated)
# =============================================================================


class PaymentGateway:
    """A stand-in for a real PSP.

    fail_rate defaults to 0.0 so runs are deterministic. Raise it to see the
    retry path. Note what is *not* here: no card number, CVV or UPI PIN is
    ever accepted, stored or logged. Only a method and an opaque reference.
    """

    def __init__(self, fail_rate: float = 0.0, seed: Optional[int] = 7) -> None:
        self.fail_rate = max(0.0, min(1.0, float(fail_rate)))
        self.rng = random.Random(seed)

    def charge(self, customer: Customer, method: PaymentMethod, amount_paise: int) -> Tuple[PaymentStatus, str]:
        if amount_paise <= 0:
            raise AppError("Invalid charge amount.")
        if method is PaymentMethod.CASH:
            return PaymentStatus.PENDING, "COD"
        if method is PaymentMethod.WALLET:
            if customer.wallet_paise < amount_paise:
                raise AppError(
                    "Wallet has {0}, order needs {1}. Top up or pick another method.".format(
                        money(customer.wallet_paise), money(amount_paise)
                    )
                )
            customer.wallet_paise -= amount_paise
            return PaymentStatus.PAID, new_id("WLT")
        if self.rng.random() < self.fail_rate:
            return PaymentStatus.FAILED, new_id("ERR")
        return PaymentStatus.PAID, new_id("TXN")

    def refund(self, customer: Customer, order: Order) -> int:
        """Prepaid orders are refunded to the wallet; COD has nothing to return."""
        if order.payment_status is not PaymentStatus.PAID:
            return 0
        amount = order.bill.total_paise
        customer.wallet_paise += amount
        order.payment_status = PaymentStatus.REFUNDED
        return amount


# =============================================================================
# SECTION 7 -- ORDER SERVICE
# =============================================================================


class OrderService:
    """All order mutations live here so the rules cannot drift apart."""

    def __init__(self, store: DataStore, gateway: Optional[PaymentGateway] = None) -> None:
        self.store = store
        self.gateway = gateway or PaymentGateway()

    # ------------------------------------------------------------------ create
    def place_order(
        self,
        customer: Customer,
        cart: Cart,
        address: Address,
        method: PaymentMethod,
        coupon: Optional[Coupon] = None,
    ) -> Order:
        if cart.is_empty() or cart.restaurant_id is None:
            raise AppError("Your cart is empty.")
        restaurant = self.store.restaurant(cart.restaurant_id)

        # Re-check availability at order time. Stock can change while a
        # customer browses; trusting the cart alone is how you sell air.
        for line in cart.lines:
            item = restaurant.find_item(line.item_id)
            if item is None or not item.available:
                raise AppError("'{0}' just went out of stock. Please update your cart.".format(line.name))

        bill = build_bill(restaurant, cart.lines, address.distance_km, coupon)
        status, ref = self.gateway.charge(customer, method, bill.total_paise)
        if status is PaymentStatus.FAILED:
            raise AppError("Payment failed (ref {0}). Nothing was charged.".format(ref))

        order = Order(
            order_id=new_id("ORD"),
            customer_id=customer.customer_id,
            restaurant_id=restaurant.restaurant_id,
            restaurant_name=restaurant.name,
            lines=[CartLine.from_dict(l.to_dict()) for l in cart.lines],  # deep copy
            address=Address.from_dict(address.to_dict()),
            bill=bill,
            payment_method=method,
            payment_status=status,
            payment_ref=ref,
            status=OrderStatus.PLACED,
            eta_minutes=estimate_eta_minutes(restaurant, cart.lines, address.distance_km),
            placed_at=datetime.now(),
        )
        order.events.append(OrderEvent(order.placed_at, OrderStatus.PLACED, "Order received"))
        self.store.orders[order.order_id] = order
        cart.clear()
        return order

    # ------------------------------------------------------------ transitions
    def advance(self, order: Order) -> Order:
        allowed = STATUS_FLOW[order.status]
        forward = [s for s in allowed if s is not OrderStatus.CANCELLED]
        if not forward:
            raise AppError("Order {0} is already {1}.".format(order.order_id, order.status.label))
        return self.set_status(order, forward[0])

    def set_status(self, order: Order, new_status: OrderStatus, note: str = "") -> Order:
        if new_status not in STATUS_FLOW[order.status]:
            raise AppError(
                "Illegal transition {0} -> {1}.".format(order.status.label, new_status.label)
            )
        order.status = new_status
        order.events.append(OrderEvent(datetime.now(), new_status, note or self._note_for(new_status, order)))

        if new_status is OrderStatus.OUT_FOR_DELIVERY and order.rider_id is None:
            self.assign_rider(order)
        if new_status is OrderStatus.DELIVERED:
            self._on_delivered(order)
        return order

    def _note_for(self, status: OrderStatus, order: Order) -> str:
        notes = {
            OrderStatus.CONFIRMED: "{0} accepted your order".format(order.restaurant_name),
            OrderStatus.PREPARING: "Kitchen has started cooking",
            OrderStatus.READY_FOR_PICKUP: "Food packed and waiting for a rider",
            OrderStatus.OUT_FOR_DELIVERY: "Rider picked up your order",
            OrderStatus.DELIVERED: "Delivered. Enjoy your meal!",
            OrderStatus.CANCELLED: "Order cancelled",
        }
        return notes.get(status, "")

    def _on_delivered(self, order: Order) -> None:
        if order.payment_method is PaymentMethod.CASH:
            order.payment_status = PaymentStatus.PAID
        customer = self.store.customers.get(order.customer_id)
        if customer is not None:
            earned = order.bill.total_paise // LOYALTY_PAISE_PER_POINT
            customer.loyalty_points += earned
        if order.rider_id:
            rider = self.store.riders.get(order.rider_id)
            if rider is not None:
                rider.busy = False
                rider.deliveries += 1

    def cancel(self, order: Order, reason: str = "Cancelled by customer") -> int:
        if order.status not in CANCELLABLE:
            raise AppError(
                "Too late to cancel: order is already {0}.".format(order.status.label)
            )
        customer = self.store.customers.get(order.customer_id)
        refunded = 0
        if customer is not None:
            refunded = self.gateway.refund(customer, order)
        if order.rider_id:
            rider = self.store.riders.get(order.rider_id)
            if rider is not None:
                rider.busy = False
        order.status = OrderStatus.CANCELLED
        order.events.append(OrderEvent(datetime.now(), OrderStatus.CANCELLED, reason))
        return refunded

    # ----------------------------------------------------------------- riders
    def assign_rider(self, order: Order) -> Optional[Rider]:
        """Prefer a free rider in the delivery area, else any free rider."""
        free = [r for r in self.store.riders.values() if not r.busy]
        if not free:
            return None
        local = [r for r in free if r.area.lower() == order.address.area.lower()]
        pool = local or free
        pool.sort(key=lambda r: (-r.rating, r.deliveries))
        rider = pool[0]
        rider.busy = True
        order.rider_id = rider.rider_id
        return rider

    def rate(self, order: Order, stars: int) -> None:
        if order.status is not OrderStatus.DELIVERED:
            raise AppError("You can only rate a delivered order.")
        if not 1 <= stars <= 5:
            raise AppError("Rating must be between 1 and 5.")
        order.rating = stars

    def redeem_points(self, customer: Customer) -> int:
        if customer.loyalty_points < LOYALTY_POINTS_PER_REDEEM:
            raise AppError(
                "You need {0} points to redeem (you have {1}).".format(
                    LOYALTY_POINTS_PER_REDEEM, customer.loyalty_points
                )
            )
        blocks = customer.loyalty_points // LOYALTY_POINTS_PER_REDEEM
        credit = blocks * LOYALTY_REDEEM_VALUE_PAISE
        customer.loyalty_points -= blocks * LOYALTY_POINTS_PER_REDEEM
        customer.wallet_paise += credit
        return credit


# =============================================================================
# SECTION 8 -- REPORTING
# =============================================================================


class ReportService:
    def __init__(self, store: DataStore) -> None:
        self.store = store

    def delivered(self) -> List[Order]:
        return [o for o in self.store.orders.values() if o.status is OrderStatus.DELIVERED]

    def revenue_paise(self) -> int:
        """Only delivered orders count as revenue. Cancelled ones never do."""
        return sum(o.bill.total_paise for o in self.delivered())

    def status_counts(self) -> Dict[str, int]:
        counts: Dict[str, int] = {}
        for order in self.store.orders.values():
            counts[order.status.label] = counts.get(order.status.label, 0) + 1
        return counts

    def top_items(self, limit: int = 5) -> List[Tuple[str, int]]:
        tally: Dict[str, int] = {}
        for order in self.store.orders.values():
            if order.status is OrderStatus.CANCELLED:
                continue
            for line in order.lines:
                tally[line.name] = tally.get(line.name, 0) + line.quantity
        ranked = sorted(tally.items(), key=lambda kv: (-kv[1], kv[0]))
        return ranked[:limit]

    def average_order_paise(self) -> int:
        done = self.delivered()
        if not done:
            return 0
        return self.revenue_paise() // len(done)

    def busiest_restaurant(self) -> Optional[Tuple[str, int]]:
        tally: Dict[str, int] = {}
        for order in self.store.orders.values():
            if order.status is OrderStatus.CANCELLED:
                continue
            tally[order.restaurant_name] = tally.get(order.restaurant_name, 0) + 1
        if not tally:
            return None
        return sorted(tally.items(), key=lambda kv: (-kv[1], kv[0]))[0]


# =============================================================================
# SECTION 9 -- CONSOLE RENDERING HELPERS
# =============================================================================


def rule(char: str = "-") -> str:
    return char * SCREEN_WIDTH


def banner(text: str) -> None:
    print()
    print(rule("="))
    print(" " + text.upper())
    print(rule("="))


def heading(text: str) -> None:
    print()
    print(text)
    print(rule("-"))


def render_table(headers: Sequence[str], rows: Sequence[Sequence[Any]]) -> None:
    """Width-aware ASCII table. Computes column widths from the data itself."""
    cols = len(headers)
    widths = [len(str(h)) for h in headers]
    text_rows = []
    for row in rows:
        cells = [str(c) for c in row] + [""] * (cols - len(row))
        text_rows.append(cells)
        for i in range(cols):
            widths[i] = max(widths[i], len(cells[i]))
    line = "  ".join(str(h).ljust(widths[i]) for i, h in enumerate(headers))
    print(line)
    print("-" * len(line))
    for cells in text_rows:
        print("  ".join(cells[i].ljust(widths[i]) for i in range(cols)))
    if not text_rows:
        print("(nothing to show)")


def print_bill(bill: Bill) -> None:
    heading("BILL")
    for label, value in bill.lines():
        print("  {0:<28} {1:>14}".format(label, value))


def plural(count: int, word: str, suffix: str = "s") -> str:
    """'1 order' / '3 orders'. Small touch, but wrong grammar looks broken."""
    return "{0} {1}{2}".format(count, word, "" if count == 1 else suffix)


def print_menu_options(options: Sequence[Tuple[str, str]]) -> None:
    for key, text in options:
        print("  [{0}] {1}".format(key, text))


# =============================================================================
# SECTION 10 -- INPUT VALIDATION
# =============================================================================


def prompt(text: str, default: Optional[str] = None) -> str:
    """Read one line. Ctrl-C / Ctrl-D become a clean UserQuit, not a traceback."""
    suffix = " [{0}]".format(default) if default is not None else ""
    try:
        raw = input("{0}{1}: ".format(text, suffix))
    except (EOFError, KeyboardInterrupt):
        print()
        raise UserQuit()
    raw = raw.strip()
    if not raw and default is not None:
        return default
    return raw


def ask_int(text: str, low: int, high: int, default: Optional[int] = None) -> int:
    """Loop until the value is an integer inside [low, high]. Never trust input."""
    while True:
        raw = prompt(text, None if default is None else str(default))
        try:
            value = int(raw)
        except ValueError:
            print("  Please enter a whole number between {0} and {1}.".format(low, high))
            continue
        if not low <= value <= high:
            print("  Out of range. Enter {0} to {1}.".format(low, high))
            continue
        return value


def ask_yes_no(text: str, default: bool = False) -> bool:
    fallback = "y" if default else "n"
    while True:
        raw = prompt("{0} (y/n)".format(text), fallback).lower()
        if raw in ("y", "yes"):
            return True
        if raw in ("n", "no"):
            return False
        print("  Please answer y or n.")


def ask_choice(text: str, valid: Sequence[str], default: Optional[str] = None) -> str:
    lowered = [v.lower() for v in valid]
    while True:
        raw = prompt(text, default).lower()
        if raw in lowered:
            return raw
        print("  Choose one of: {0}".format(", ".join(valid)))


def ask_phone(text: str = "Phone (10 digits)") -> str:
    while True:
        raw = prompt(text)
        if PHONE_RE.match(raw):
            return raw
        print("  That is not a valid 10-digit Indian mobile number.")


def ask_pincode(text: str = "PIN code") -> str:
    while True:
        raw = prompt(text)
        if PINCODE_RE.match(raw):
            return raw
        print("  A PIN code is exactly 6 digits.")


def ask_float(text: str, low: float, high: float, default: Optional[float] = None) -> float:
    while True:
        raw = prompt(text, None if default is None else str(default))
        try:
            value = float(raw)
        except ValueError:
            print("  Please enter a number, for example 3.5")
            continue
        if not low <= value <= high:
            print("  Enter a value between {0} and {1}.".format(low, high))
            continue
        return value


def pick_from(label: str, items: Sequence[Any], render: Callable[[Any], str]) -> Optional[Any]:
    """Numbered picker. Returns None if the user backs out with 0."""
    if not items:
        print("  Nothing available here.")
        return None
    heading(label)
    for index, item in enumerate(items, start=1):
        print("  {0:>2}. {1}".format(index, render(item)))
    print("   0. Go back")
    choice = ask_int("Choose", 0, len(items), 0)
    if choice == 0:
        return None
    return items[choice - 1]


# =============================================================================
# SECTION 11 -- THE INTERACTIVE APP
# =============================================================================


class FoodDeliveryApp:
    def __init__(self, store: DataStore) -> None:
        self.store = store
        self.gateway = PaymentGateway()
        self.orders = OrderService(store, self.gateway)
        self.reports = ReportService(store)
        self.customer: Optional[Customer] = None
        self.cart: Optional[Cart] = None

    # ------------------------------------------------------------------- entry
    def run(self) -> int:
        banner("{0} v{1}".format(APP_NAME, APP_VERSION))
        print(" Food delivery, entirely in the standard library.")
        print(" Press Ctrl-C at any prompt to save and exit.")
        try:
            self.login()
            self.main_loop()
        except UserQuit:
            print("\nSaving your data...")
        finally:
            self.store.save()
        print("Goodbye! Data file: {0}".format(os.path.abspath(self.store.path)))
        return 0

    def login(self) -> None:
        heading("WHO IS ORDERING?")
        people = list(self.store.customers.values())
        for index, person in enumerate(people, start=1):
            print("  {0:>2}. {1} ({2})".format(index, person.name, person.phone))
        print("   0. Create a new account")
        choice = ask_int("Choose", 0, len(people), 1)
        if choice == 0:
            self.customer = self.create_customer()
        else:
            self.customer = people[choice - 1]
        self.cart = Cart(customer_id=self.customer.customer_id)
        if not self.customer.addresses:
            print("\nYou have no saved address yet. Let's add one.")
            self.add_address()
        print("\nWelcome, {0}! Wallet: {1} | Points: {2}".format(
            self.customer.name, money(self.customer.wallet_paise), self.customer.loyalty_points))

    def create_customer(self) -> Customer:
        heading("NEW ACCOUNT")
        name = prompt("Your name", "New Customer")
        phone = ask_phone()
        customer = Customer(customer_id=new_id("CUS"), name=name, phone=phone)
        self.store.customers[customer.customer_id] = customer
        return customer

    def add_address(self) -> Address:
        assert self.customer is not None
        heading("ADD AN ADDRESS")
        label = prompt("Label (Home/Work/Other)", "Home")
        line1 = prompt("Flat / building / street", "Flat 1, Main Street")
        area = prompt("Area", "Virar West")
        city = prompt("City", "Palghar")
        pincode = ask_pincode()
        distance = ask_float("Distance from restaurants in km", 0.1, 25.0, 3.0)
        address = Address(label, line1, area, city, pincode, distance)
        self.customer.addresses.append(address)
        print("  Saved: {0}".format(address.one_line()))
        return address

    # --------------------------------------------------------------- main menu
    def main_loop(self) -> None:
        while True:
            assert self.customer is not None and self.cart is not None
            banner("MAIN MENU")
            print(" {0} | Cart: {1} item(s) = {2} | Wallet: {3}".format(
                self.customer.name,
                self.cart.item_count(),
                money(self.cart.subtotal_paise()),
                money(self.customer.wallet_paise),
            ))
            print()
            print_menu_options([
                ("1", "Browse restaurants"),
                ("2", "Search dishes or restaurants"),
                ("3", "View cart"),
                ("4", "Checkout"),
                ("5", "My orders and live tracking"),
                ("6", "Wallet and loyalty"),
                ("7", "Addresses"),
                ("8", "Offers"),
                ("9", "Admin dashboard"),
                ("0", "Save and quit"),
            ])
            choice = ask_choice("Select", [str(n) for n in range(10)], "1")
            actions: Dict[str, Callable[[], None]] = {
                "1": self.screen_browse,
                "2": self.screen_search,
                "3": self.screen_cart,
                "4": self.screen_checkout,
                "5": self.screen_orders,
                "6": self.screen_wallet,
                "7": self.screen_addresses,
                "8": self.screen_offers,
                "9": self.screen_admin,
            }
            if choice == "0":
                raise UserQuit()
            try:
                actions[choice]()
            except AppError as exc:
                print("\n  ! {0}".format(exc))
            self.store.save()

    # ---------------------------------------------------------------- browsing
    def screen_browse(self) -> None:
        restaurants = sorted(self.store.restaurants.values(), key=lambda r: -r.rating)
        chosen = pick_from(
            "RESTAURANTS NEAR YOU",
            restaurants,
            lambda r: "{0:<22} {1:<14} {2:<18} {3:.1f} stars  {4}".format(
                r.name[:22], r.cuisine[:14], r.area[:18], r.rating,
                "OPEN" if r.is_open() else "CLOSED",
            ),
        )
        if chosen is not None:
            self.screen_restaurant(chosen)

    def screen_search(self) -> None:
        term = prompt("Search (dish, cuisine, area or name)")
        hits = self.store.search_restaurants(term)
        if not hits:
            print("  No matches for '{0}'.".format(term))
            return
        chosen = pick_from(
            "RESULTS FOR '{0}'".format(term.upper()),
            hits,
            lambda r: "{0:<24} {1:<14} {2:.1f} stars".format(r.name[:24], r.cuisine[:14], r.rating),
        )
        if chosen is not None:
            self.screen_restaurant(chosen)

    def screen_restaurant(self, restaurant: Restaurant) -> None:
        assert self.cart is not None
        while True:
            banner(restaurant.name)
            print(" {0} | {1} | {2:.1f} stars | {3}".format(
                restaurant.cuisine, restaurant.area, restaurant.rating,
                "OPEN NOW" if restaurant.is_open() else "CLOSED (you can still order for later)"))
            print(" Packaging: {0} | From {1}".format(
                money(restaurant.packaging_fee_paise), money(restaurant.cheapest_paise())))

            items = restaurant.menu
            for category in restaurant.categories():
                heading(category.upper())
                rows = []
                for item in items:
                    if item.category != category:
                        continue
                    flags = [item.diet_tag]
                    if item.spicy:
                        flags.append("SPICY")
                    if not item.available:
                        flags.append("SOLD OUT")
                    rows.append([
                        str(items.index(item) + 1),
                        item.name,
                        money(item.price_paise),
                        "{0} min".format(item.prep_minutes),
                        "/".join(flags),
                    ])
                render_table(["#", "Dish", "Price", "Prep", "Tags"], rows)

            print()
            print_menu_options([
                ("1", "Add an item to the cart"),
                ("2", "View cart"),
                ("0", "Back to the main menu"),
            ])
            choice = ask_choice("Select", ["0", "1", "2"], "1")
            if choice == "0":
                return
            if choice == "2":
                self.screen_cart()
                continue
            index = ask_int("Item number", 1, len(items))
            item = items[index - 1]
            if not item.available:
                print("  ! '{0}' is sold out.".format(item.name))
                continue
            if self.cart.lines and self.cart.restaurant_id not in (None, restaurant.restaurant_id):
                other = self.store.restaurants[self.cart.restaurant_id].name
                print("\n  Your cart already has food from {0}.".format(other))
                if not ask_yes_no("  Clear it and start a new cart", False):
                    continue
                self.cart.clear()
            self.cart.restaurant_id = restaurant.restaurant_id
            quantity = ask_int("Quantity", 1, 20, 1)
            notes = prompt("Any cooking note (press Enter to skip)")
            line = self.cart.add(item, quantity, notes)
            print("  Added {0} x {1} = {2}".format(
                line.quantity, line.name, money(line.line_total_paise)))

    # -------------------------------------------------------------------- cart
    def screen_cart(self) -> None:
        assert self.cart is not None
        while True:
            banner("YOUR CART")
            if self.cart.is_empty():
                print(" Your cart is empty. Browse a restaurant to add food.")
                return
            restaurant = self.store.restaurant(self.cart.restaurant_id or "")
            print(" From: {0} ({1})".format(restaurant.name, restaurant.area))
            rows = []
            for index, line in enumerate(self.cart.lines, start=1):
                rows.append([
                    str(index), line.name, str(line.quantity),
                    money(line.unit_price_paise), money(line.line_total_paise),
                    line.notes or "-",
                ])
            render_table(["#", "Dish", "Qty", "Unit", "Total", "Note"], rows)
            print("\n Subtotal: {0}".format(money(self.cart.subtotal_paise())))
            print()
            print_menu_options([
                ("1", "Change a quantity"),
                ("2", "Remove an item"),
                ("3", "Empty the cart"),
                ("4", "Checkout"),
                ("0", "Back"),
            ])
            choice = ask_choice("Select", ["0", "1", "2", "3", "4"], "0")
            if choice == "0":
                return
            if choice == "1":
                index = ask_int("Which line", 1, len(self.cart.lines))
                line = self.cart.lines[index - 1]
                quantity = ask_int("New quantity (0 removes it)", 0, 20, line.quantity)
                self.cart.set_quantity(line.item_id, quantity)
            elif choice == "2":
                index = ask_int("Which line", 1, len(self.cart.lines))
                self.cart.remove(self.cart.lines[index - 1].item_id)
            elif choice == "3":
                if ask_yes_no("Empty the whole cart", False):
                    self.cart.clear()
                    return
            elif choice == "4":
                self.screen_checkout()
                return

    # ---------------------------------------------------------------- checkout
    def screen_checkout(self) -> None:
        assert self.customer is not None and self.cart is not None
        if self.cart.is_empty():
            raise AppError("Nothing to check out -- your cart is empty.")
        restaurant = self.store.restaurant(self.cart.restaurant_id or "")
        banner("CHECKOUT")

        address = self.choose_address()
        if address is None:
            return

        subtotal = self.cart.subtotal_paise()
        coupon = self.choose_coupon(subtotal)

        bill = build_bill(restaurant, self.cart.lines, address.distance_km, coupon)
        heading("ORDER SUMMARY")
        print("  {0} -> {1}".format(restaurant.name, address.label))
        for line in self.cart.lines:
            print("   {0} x {1:<28} {2:>11}".format(
                line.quantity, line.name[:28], money(line.line_total_paise)))
        print_bill(bill)
        print("\n  Estimated delivery in about {0} minutes".format(
            estimate_eta_minutes(restaurant, self.cart.lines, address.distance_km)))

        method = self.choose_payment(bill.total_paise)
        if method is None:
            return
        if not ask_yes_no("\nPlace this order", True):
            print("  Order not placed. Your cart is untouched.")
            return

        order = self.orders.place_order(self.customer, self.cart, address, method, coupon)
        heading("ORDER PLACED")
        print("  Order id : {0}".format(order.order_id))
        print("  Paid     : {0} via {1} ({2})".format(
            money(order.bill.total_paise), order.payment_method.label, order.payment_status.label))
        print("  ETA      : about {0} min, around {1}".format(order.eta_minutes, order.eta_clock()))
        print("\n  Track it from 'My orders' in the main menu.")

    def choose_address(self) -> Optional[Address]:
        assert self.customer is not None
        options: List[Any] = list(self.customer.addresses) + ["__new__"]
        chosen = pick_from(
            "DELIVER TO",
            options,
            lambda a: "Add a new address" if a == "__new__"
            else "{0:<6} {1} ({2:.1f} km)".format(a.label, a.one_line(), a.distance_km),
        )
        if chosen is None:
            return None
        if chosen == "__new__":
            return self.add_address()
        return chosen

    def choose_coupon(self, subtotal: int) -> Optional[Coupon]:
        usable = CouponEngine.eligible(list(self.store.coupons.values()), subtotal)
        heading("OFFERS FOR THIS CART")
        if not usable:
            print("  No coupon applies to {0} yet. Add more items to unlock offers.".format(
                money(subtotal)))
            return None
        for index, coupon in enumerate(usable, start=1):
            saving = CouponEngine.discount_paise(coupon, subtotal)
            extra = "free delivery" if coupon.free_delivery else "saves {0}".format(money(saving))
            print("  {0:>2}. {1:<12} {2} ({3})".format(index, coupon.code, coupon.description, extra))
        print("   0. No coupon")
        choice = ask_int("Apply which coupon", 0, len(usable), 0)
        if choice == 0:
            return None
        picked = usable[choice - 1]
        print("  Applied {0}.".format(picked.code))
        return picked

    def choose_payment(self, total: int) -> Optional[PaymentMethod]:
        assert self.customer is not None
        methods = list(PaymentMethod)
        heading("PAYMENT")
        for index, method in enumerate(methods, start=1):
            note = ""
            if method is PaymentMethod.WALLET:
                note = " (balance {0}{1})".format(
                    money(self.customer.wallet_paise),
                    "" if self.customer.wallet_paise >= total else " - not enough",
                )
            print("  {0:>2}. {1}{2}".format(index, method.label, note))
        print("   0. Cancel checkout")
        choice = ask_int("Pay with", 0, len(methods), 1)
        if choice == 0:
            return None
        return methods[choice - 1]

    # ------------------------------------------------------------------ orders
    def screen_orders(self) -> None:
        assert self.customer is not None
        mine = self.store.orders_of(self.customer.customer_id)
        if not mine:
            print("\n  You have not ordered anything yet.")
            return
        chosen = pick_from("MY ORDERS", mine, lambda o: o.summary_line())
        if chosen is not None:
            self.screen_track(chosen)

    def screen_track(self, order: Order) -> None:
        assert self.customer is not None
        while True:
            banner("ORDER {0}".format(order.order_id))
            print("  {0} -> {1}".format(order.restaurant_name, order.address.label))
            print("  Placed  : {0}".format(order.placed_at.strftime("%d %b %Y, %H:%M")))
            print("  Status  : {0}".format(order.status.label))
            print("  Payment : {0} / {1} ({2})".format(
                order.payment_method.label, order.payment_status.label, order.payment_ref))
            if order.rider_id:
                rider = self.store.riders.get(order.rider_id)
                if rider is not None:
                    print("  Rider   : {0} on a {1}, {2:.1f} stars".format(
                        rider.name, rider.vehicle, rider.rating))
            if order.is_active:
                print("  ETA     : about {0} min (around {1})".format(order.eta_minutes, order.eta_clock()))
            if order.rating:
                print("  Rating  : {0}/5".format(order.rating))

            heading("ITEMS")
            render_table(
                ["Qty", "Dish", "Amount"],
                [[line.quantity, line.name, money(line.line_total_paise)] for line in order.lines],
            )
            print_bill(order.bill)

            heading("TIMELINE")
            for event in order.events:
                print("  {0}  {1:<18} {2}".format(
                    event.at.strftime("%H:%M:%S"), event.status.label, event.note))

            print()
            print_menu_options([
                ("1", "Simulate the next step"),
                ("2", "Cancel this order"),
                ("3", "Rate this order"),
                ("0", "Back"),
            ])
            choice = ask_choice("Select", ["0", "1", "2", "3"], "1")
            if choice == "0":
                return
            try:
                if choice == "1":
                    self.orders.advance(order)
                    print("  Now: {0}".format(order.status.label))
                elif choice == "2":
                    refunded = self.orders.cancel(order)
                    if refunded:
                        print("  Cancelled. {0} refunded to your wallet.".format(money(refunded)))
                    else:
                        print("  Cancelled. Nothing to refund (cash on delivery).")
                elif choice == "3":
                    stars = ask_int("Stars (1-5)", 1, 5, 5)
                    self.orders.rate(order, stars)
                    print("  Thanks for the feedback!")
            except AppError as exc:
                print("  ! {0}".format(exc))
            self.store.save()

    # ------------------------------------------------------------------ wallet
    def screen_wallet(self) -> None:
        assert self.customer is not None
        while True:
            banner("WALLET AND LOYALTY")
            print("  Balance : {0}".format(money(self.customer.wallet_paise)))
            print("  Points  : {0} ({1} points = {2})".format(
                self.customer.loyalty_points, LOYALTY_POINTS_PER_REDEEM,
                money(LOYALTY_REDEEM_VALUE_PAISE)))
            print()
            print_menu_options([
                ("1", "Top up the wallet"),
                ("2", "Redeem loyalty points"),
                ("0", "Back"),
            ])
            choice = ask_choice("Select", ["0", "1", "2"], "0")
            if choice == "0":
                return
            try:
                if choice == "1":
                    amount = ask_int("Amount in rupees", 1, 10000, 500)
                    self.customer.wallet_paise += rupees(amount)
                    print("  Added {0}. New balance {1}.".format(
                        money(rupees(amount)), money(self.customer.wallet_paise)))
                else:
                    credit = self.orders.redeem_points(self.customer)
                    print("  Converted points into {0} of wallet credit.".format(money(credit)))
            except AppError as exc:
                print("  ! {0}".format(exc))
            self.store.save()

    def screen_addresses(self) -> None:
        assert self.customer is not None
        banner("SAVED ADDRESSES")
        if not self.customer.addresses:
            print("  None saved yet.")
        else:
            render_table(
                ["Label", "Address", "Distance"],
                [[a.label, a.one_line(), "{0:.1f} km".format(a.distance_km)]
                 for a in self.customer.addresses],
            )
        if ask_yes_no("\nAdd another address", False):
            self.add_address()

    def screen_offers(self) -> None:
        banner("ALL OFFERS")
        rows = []
        for coupon in self.store.coupons.values():
            if coupon.percent_off:
                value = "{0}% off".format(coupon.percent_off)
                if coupon.max_discount_paise:
                    value += " (max {0})".format(money(coupon.max_discount_paise))
            elif coupon.flat_off_paise:
                value = "{0} off".format(money(coupon.flat_off_paise))
            elif coupon.free_delivery:
                value = "Free delivery"
            else:
                value = "-"
            rows.append([
                coupon.code, value,
                money(coupon.min_order_paise) if coupon.min_order_paise else "none",
                "active" if coupon.active else "inactive",
            ])
        render_table(["Code", "Benefit", "Min order", "State"], rows)

    # ------------------------------------------------------------------- admin
    def screen_admin(self) -> None:
        while True:
            banner("ADMIN DASHBOARD")
            print_menu_options([
                ("1", "Business report"),
                ("2", "Rider roster"),
                ("3", "Toggle a dish in or out of stock"),
                ("4", "Advance every active order by one step"),
                ("0", "Back"),
            ])
            choice = ask_choice("Select", ["0", "1", "2", "3", "4"], "1")
            if choice == "0":
                return
            if choice == "1":
                self.admin_report()
            elif choice == "2":
                self.admin_riders()
            elif choice == "3":
                self.admin_stock()
            elif choice == "4":
                self.admin_advance_all()
            self.store.save()

    def admin_report(self) -> None:
        heading("BUSINESS REPORT")
        print("  Orders total     : {0}".format(len(self.store.orders)))
        print("  Delivered        : {0}".format(len(self.reports.delivered())))
        print("  Revenue          : {0}".format(money(self.reports.revenue_paise())))
        print("  Average order    : {0}".format(money(self.reports.average_order_paise())))
        busiest = self.reports.busiest_restaurant()
        if busiest:
            print("  Busiest kitchen  : {0} ({1})".format(
                busiest[0], plural(busiest[1], "order")))
        counts = self.reports.status_counts()
        if counts:
            heading("ORDERS BY STATUS")
            render_table(["Status", "Count"], [[k, v] for k, v in sorted(counts.items())])
        top = self.reports.top_items()
        if top:
            heading("TOP DISHES")
            render_table(["Dish", "Units"], [[name, qty] for name, qty in top])

    def admin_riders(self) -> None:
        heading("RIDERS")
        render_table(
            ["Id", "Name", "Vehicle", "Area", "Rating", "State", "Deliveries"],
            [[r.rider_id, r.name, r.vehicle, r.area, "{0:.1f}".format(r.rating),
              "busy" if r.busy else "free", r.deliveries]
             for r in self.store.riders.values()],
        )

    def admin_stock(self) -> None:
        restaurant = pick_from(
            "PICK A RESTAURANT",
            list(self.store.restaurants.values()),
            lambda r: "{0} ({1} dishes)".format(r.name, len(r.menu)),
        )
        if restaurant is None:
            return
        item = pick_from(
            "PICK A DISH",
            restaurant.menu,
            lambda i: "{0:<30} {1:>10}  {2}".format(
                i.name[:30], money(i.price_paise), "in stock" if i.available else "SOLD OUT"),
        )
        if item is None:
            return
        item.available = not item.available
        print("  '{0}' is now {1}.".format(item.name, "in stock" if item.available else "sold out"))

    def admin_advance_all(self) -> None:
        active = [o for o in self.store.orders.values() if o.is_active]
        if not active:
            print("  No active orders to move.")
            return
        for order in active:
            try:
                self.orders.advance(order)
                print("  {0} -> {1}".format(order.order_id, order.status.label))
            except AppError as exc:
                print("  {0}: {1}".format(order.order_id, exc))


# =============================================================================
# SECTION 12 -- SCRIPTED DEMO (no input needed)
# =============================================================================


def run_demo(path: str) -> int:
    """End-to-end order with zero typing, so the app is provably runnable."""
    banner("{0} -- SCRIPTED DEMO".format(APP_NAME))
    store = DataStore(path)
    print(" Data: {0} ({1})".format(os.path.abspath(path), store.load()))

    service = OrderService(store)
    customer = store.customer("C001")
    restaurant = store.restaurant("R003")
    cart = Cart(customer_id=customer.customer_id, restaurant_id=restaurant.restaurant_id)

    heading("1. BUILD A CART")
    for item_id, quantity in (("R003-01", 2), ("R003-05", 1), ("R003-06", 2)):
        item = restaurant.find_item(item_id)
        assert item is not None
        line = cart.add(item, quantity)
        print("  + {0} x {1:<28} {2:>11}".format(
            line.quantity, line.name[:28], money(line.line_total_paise)))
    print("  Subtotal: {0}".format(money(cart.subtotal_paise())))

    heading("2. APPLY THE BEST AVAILABLE COUPON")
    usable = CouponEngine.eligible(list(store.coupons.values()), cart.subtotal_paise())
    best = None
    best_value = -1
    for coupon in usable:
        value = CouponEngine.discount_paise(coupon, cart.subtotal_paise())
        if coupon.free_delivery:
            value += delivery_fee_paise(2.5, cart.subtotal_paise())
        print("  {0:<12} would save {1}".format(coupon.code, money(value)))
        if value > best_value:
            best, best_value = coupon, value
    print("  Best: {0}".format(best.code if best else "none"))

    heading("3. PRICE AND PAY")
    address = customer.addresses[0]
    top_up = rupees(2000)
    customer.wallet_paise += top_up
    print("  Topped the wallet up by {0} -> balance {1}".format(
        money(top_up), money(customer.wallet_paise)))
    order = service.place_order(customer, cart, address, PaymentMethod.WALLET, best)
    print("  Charged the wallet; balance is now {0}".format(money(customer.wallet_paise)))
    print_bill(order.bill)
    print("\n  Order {0} placed, ETA {1} min (around {2})".format(
        order.order_id, order.eta_minutes, order.eta_clock()))

    heading("4. WALK THE ORDER THROUGH EVERY STAGE")
    while order.is_active:
        service.advance(order)
        rider = store.riders.get(order.rider_id or "")
        extra = " (rider: {0})".format(rider.name) if rider else ""
        print("  -> {0}{1}".format(order.status.label, extra))

    heading("5. RATE IT AND CHECK THE LEDGER")
    service.rate(order, 5)
    reports = ReportService(store)
    print("  Rating recorded   : {0}/5".format(order.rating))
    print("  Loyalty points now: {0}".format(customer.loyalty_points))
    print("  Delivered orders  : {0}".format(len(reports.delivered())))
    print("  Revenue           : {0}".format(money(reports.revenue_paise())))

    heading("6. A SECOND ORDER, THEN CANCEL IT")
    cart2 = Cart(customer.customer_id, "R004")
    tiffin = store.restaurant("R004")
    dosa = tiffin.find_item("R004-01")
    assert dosa is not None
    cart2.add(dosa, 3)
    order2 = service.place_order(customer, cart2, address, PaymentMethod.CARD)
    print("  Placed {0} for {1}".format(order2.order_id, money(order2.bill.total_paise)))
    service.advance(order2)
    refund = service.cancel(order2, "Demo cancellation")
    print("  Cancelled {0}; refunded {1} to the wallet (now {2})".format(
        order2.order_id, money(refund), money(customer.wallet_paise)))
    print("  Revenue still {0} -- cancelled orders never count.".format(
        money(reports.revenue_paise())))

    store.save()
    banner("DEMO COMPLETE")
    print(" Run without --demo for the full interactive app.")
    return 0


# =============================================================================
# SECTION 13 -- BUILT-IN TEST SUITE
# =============================================================================


class TestRunner:
    """A tiny test harness. No pytest, no unittest ceremony -- just asserts."""

    def __init__(self) -> None:
        self.passed = 0
        self.failed: List[str] = []

    def check(self, name: str, condition: bool, detail: str = "") -> None:
        if condition:
            self.passed += 1
            print("  PASS  {0}".format(name))
        else:
            self.failed.append(name)
            print("  FAIL  {0}{1}".format(name, " -- " + detail if detail else ""))

    def raises(self, name: str, func: Callable[[], Any], expected: type = AppError) -> None:
        try:
            func()
        except expected:
            self.check(name, True)
        except Exception as exc:  # noqa: BLE001 - deliberately broad in a test harness
            self.check(name, False, "raised {0} instead".format(type(exc).__name__))
        else:
            self.check(name, False, "nothing was raised")

    def report(self) -> int:
        print()
        print(rule("="))
        total = self.passed + len(self.failed)
        if self.failed:
            print(" {0}/{1} passed. Failures: {2}".format(self.passed, total, ", ".join(self.failed)))
            print(rule("="))
            return 1
        print(" ALL {0} CHECKS PASSED".format(total))
        print(rule("="))
        return 0


def run_self_tests() -> int:
    banner("{0} -- SELF TEST".format(APP_NAME))
    t = TestRunner()
    temp_dir = tempfile.mkdtemp(prefix="bnb-test-")
    data_path = os.path.join(temp_dir, "test_store.json")

    # -- money -------------------------------------------------------------
    heading("MONEY AND MATHS")
    t.check("rupees() converts to paise", rupees(180) == 18000)
    t.check("rupees() handles decimals", rupees(99.5) == 9950)
    t.check("money() formats paise", money(18000) == "Rs.180.00")
    t.check("money() pads the paise part", money(5) == "Rs.0.05")
    t.check("money() keeps the sign", money(-750) == "-Rs.7.50")
    t.check("percent_of() stays in exact integers",
            percent_of(rupees(200), 5) == rupees(10), str(percent_of(rupees(200), 5)))
    t.check("percent_of() rounds to the nearest paisa",
            percent_of(1005, 5) == 50, str(percent_of(1005, 5)))

    # -- store -------------------------------------------------------------
    heading("STORE AND CATALOG")
    store = DataStore(data_path)
    status = store.load()
    t.check("fresh store seeds itself", status == "seeded", status)
    t.check("five restaurants seeded", len(store.restaurants) == 5)
    t.check("lookup by id works", store.restaurant("R001").name == "Spice Route")
    t.raises("unknown restaurant raises", lambda: store.restaurant("NOPE"))
    t.check("dish search finds a restaurant",
            any(r.restaurant_id == "R004" for r in store.search_restaurants("dosa")))
    t.check("empty search returns everything", len(store.search_restaurants("  ")) == 5)
    t.check("sold-out dish is hidden from available_items",
            all(i.available for i in store.restaurant("R005").available_items()))

    # -- cart --------------------------------------------------------------
    heading("CART")
    pizza_place = store.restaurant("R003")
    margherita = pizza_place.find_item("R003-01")
    garlic = pizza_place.find_item("R003-05")
    assert margherita is not None and garlic is not None
    cart = Cart("C001", "R003")
    cart.add(margherita, 1)
    cart.add(margherita, 2)
    t.check("adding the same dish merges lines", len(cart.lines) == 1)
    t.check("merged quantity adds up", cart.lines[0].quantity == 3)
    cart.add(garlic, 2)
    t.check("subtotal is exact",
            cart.subtotal_paise() == rupees(320) * 3 + rupees(130) * 2,
            money(cart.subtotal_paise()))
    t.check("item_count counts units", cart.item_count() == 5)
    cart.set_quantity("R003-05", 1)
    t.check("set_quantity updates a line", cart.find("R003-05").quantity == 1)
    cart.set_quantity("R003-05", 0)
    t.check("quantity zero removes the line", cart.find("R003-05") is None)
    t.check("a cart with food keeps its restaurant link", cart.restaurant_id == "R003")
    throwaway = Cart("C001", "R003")
    throwaway.add(garlic, 1)
    throwaway.set_quantity("R003-05", 0)
    t.check("emptying the last line unlinks the restaurant",
            throwaway.restaurant_id is None and throwaway.is_empty())
    t.raises("removing an absent line raises", lambda: cart.remove("R003-99"))
    t.raises("quantity below 1 is rejected", lambda: cart.add(margherita, 0))

    brownie = store.restaurant("R005").find_item("R005-07")
    assert brownie is not None
    t.check("seed marks the brownie unavailable", brownie.available is False)
    t.raises("adding a sold-out dish raises", lambda: Cart("C001", "R005").add(brownie, 1))

    # -- delivery and coupons ---------------------------------------------
    heading("DELIVERY FEES AND COUPONS")
    t.check("base fee covers the first 2 km",
            delivery_fee_paise(1.5, rupees(200)) == DELIVERY_BASE_PAISE)
    t.check("extra km costs more",
            delivery_fee_paise(5.0, rupees(200)) == DELIVERY_BASE_PAISE + rupees(30),
            money(delivery_fee_paise(5.0, rupees(200))))
    t.check("fee is capped", delivery_fee_paise(50.0, rupees(200)) == DELIVERY_FEE_CAP_PAISE)
    t.check("big orders ship free", delivery_fee_paise(9.0, rupees(600)) == 0)

    welcome = store.coupon("welcome50")  # lookup is case-insensitive
    t.check("coupon lookup is case-insensitive", welcome.code == "WELCOME50")
    t.check("percent coupon respects its cap",
            CouponEngine.discount_paise(welcome, rupees(1000)) == rupees(100))
    party = store.coupon("PARTY20")
    t.check("percent coupon below its cap is a true percentage",
            CouponEngine.discount_paise(party, rupees(799)) == 15980,
            money(CouponEngine.discount_paise(party, rupees(799))))
    t.check("a discount can never exceed the food value",
            CouponEngine.discount_paise(
                Coupon("TESTBIG", "flat 5000 off", flat_off_paise=rupees(5000)),
                rupees(300)) == rupees(300))
    t.raises("coupon below minimum order raises",
             lambda: CouponEngine.discount_paise(welcome, rupees(50)))
    t.raises("inactive coupon raises",
             lambda: CouponEngine.discount_paise(store.coupon("EXPIRED10"), rupees(900)))
    t.check("flat coupon subtracts a flat amount",
            CouponEngine.discount_paise(store.coupon("FLAT75"), rupees(500)) == rupees(75))
    t.check("eligible() filters by cart value",
            {c.code for c in CouponEngine.eligible(list(store.coupons.values()), rupees(100))}
            == {"FREESHIP"})

    # -- billing -----------------------------------------------------------
    heading("BILLING")
    plain = build_bill(pizza_place, cart.lines, 3.0, None)
    expected_sub = rupees(320) * 3
    t.check("subtotal flows into the bill", plain.subtotal_paise == expected_sub)
    t.check("packaging comes from the restaurant",
            plain.packaging_paise == pizza_place.packaging_fee_paise)
    t.check("a cart over the free-delivery threshold ships free",
            plain.delivery_paise == 0, money(plain.delivery_paise))
    small = Cart("C001", "R003")
    small.add(garlic, 1)
    small_bill = build_bill(pizza_place, small.lines, 6.0, None)
    t.check("a small cart is charged for distance",
            small_bill.delivery_paise == DELIVERY_BASE_PAISE + rupees(40),
            money(small_bill.delivery_paise))
    t.check("FREESHIP wipes a real delivery fee",
            build_bill(pizza_place, small.lines, 6.0,
                       store.coupon("FREESHIP")).delivery_paise == 0)
    t.check("tax is 5% of food plus packaging",
            plain.tax_paise == percent_of(expected_sub + plain.packaging_paise, GST_PERCENT))
    t.check("total is the sum of its parts",
            plain.total_paise == (plain.subtotal_paise - plain.discount_paise
                                  + plain.packaging_paise + plain.delivery_paise
                                  + plain.platform_paise + plain.tax_paise))

    discounted = build_bill(pizza_place, cart.lines, 3.0, welcome)
    t.check("a coupon lowers the total", discounted.total_paise < plain.total_paise)
    t.check("the coupon code is recorded", discounted.coupon_code == "WELCOME50")
    shipped = build_bill(pizza_place, cart.lines, 3.0, store.coupon("FREESHIP"))
    t.check("free delivery zeroes the delivery line", shipped.delivery_paise == 0)
    t.raises("pricing an empty cart raises", lambda: build_bill(pizza_place, [], 3.0, None))

    # -- ETA ---------------------------------------------------------------
    heading("ETA MODEL")
    eta = estimate_eta_minutes(pizza_place, cart.lines, 2.5)
    t.check("ETA is at least the floor", eta >= 15, str(eta))
    t.check("further address means a longer ETA",
            estimate_eta_minutes(pizza_place, cart.lines, 10.0) > eta)

    # -- payments and orders ----------------------------------------------
    heading("PAYMENTS AND ORDERS")
    service = OrderService(store)
    customer = store.customer("C001")
    address = customer.addresses[0]
    poor = Customer("C900", "Broke", "9800000000",
                    [Address("Home", "x", "Virar West", "Palghar", "401303", 2.0)], rupees(1))
    store.customers[poor.customer_id] = poor
    t.raises("wallet payment without funds raises",
             lambda: service.gateway.charge(poor, PaymentMethod.WALLET, rupees(500)))
    t.check("cash payment stays pending",
            service.gateway.charge(customer, PaymentMethod.CASH, rupees(100))[0]
            is PaymentStatus.PENDING)

    customer.wallet_paise += rupees(5000)     # fund the wallet for the next test
    wallet_before = customer.wallet_paise
    order = service.place_order(customer, cart, address, PaymentMethod.WALLET, None)
    t.check("order id is issued", order.order_id.startswith("ORD-"))
    t.check("order starts as placed", order.status is OrderStatus.PLACED)
    t.check("wallet was debited by the exact total",
            customer.wallet_paise == wallet_before - order.bill.total_paise)
    t.check("placing an order empties the cart", cart.is_empty())
    t.check("order lines are a copy, not a reference",
            order.lines and order.lines[0].quantity == 3)
    t.raises("placing from an empty cart raises",
             lambda: service.place_order(customer, cart, address, PaymentMethod.CASH, None))

    heading("STATUS MACHINE")
    t.raises("illegal jump is refused",
             lambda: service.set_status(order, OrderStatus.DELIVERED))
    service.advance(order)
    t.check("placed advances to confirmed", order.status is OrderStatus.CONFIRMED)
    service.advance(order)
    service.advance(order)
    t.check("confirmed walks to ready for pickup",
            order.status is OrderStatus.READY_FOR_PICKUP, order.status.label)
    service.advance(order)
    t.check("dispatch assigns a rider", order.rider_id is not None)
    t.check("assigned rider is marked busy", store.riders[order.rider_id].busy is True)
    t.raises("a dispatched order cannot be cancelled", lambda: service.cancel(order))
    points_before = customer.loyalty_points
    service.advance(order)
    t.check("order reaches delivered", order.status is OrderStatus.DELIVERED)
    t.check("delivery frees the rider", store.riders[order.rider_id].busy is False)
    t.check("delivery credits loyalty points", customer.loyalty_points > points_before)
    t.raises("a delivered order cannot advance", lambda: service.advance(order))
    t.check("every event was recorded", len(order.events) == 6, str(len(order.events)))

    heading("RATING, REFUNDS, LOYALTY")
    service.rate(order, 4)
    t.check("rating is stored", order.rating == 4)
    t.raises("rating out of range is refused", lambda: service.rate(order, 9))

    cart3 = Cart("C001", "R001")
    dal = store.restaurant("R001").find_item("R001-02")
    assert dal is not None
    cart3.add(dal, 2)
    order3 = service.place_order(customer, cart3, address, PaymentMethod.CARD, None)
    t.check("card payment is marked paid", order3.payment_status is PaymentStatus.PAID)
    wallet_pre_refund = customer.wallet_paise
    refunded = service.cancel(order3)
    t.check("cancelling refunds the full total", refunded == order3.bill.total_paise)
    t.check("refund lands in the wallet",
            customer.wallet_paise == wallet_pre_refund + refunded)
    t.check("refunded orders say so", order3.payment_status is PaymentStatus.REFUNDED)
    t.check("cancelled order is no longer active", order3.is_active is False)

    customer.loyalty_points = 250
    credit = service.redeem_points(customer)
    t.check("redeeming 250 points gives two blocks",
            credit == 2 * LOYALTY_REDEEM_VALUE_PAISE, money(credit))
    t.check("leftover points remain", customer.loyalty_points == 50)
    t.raises("redeeming too few points raises", lambda: service.redeem_points(customer))

    # -- reporting ---------------------------------------------------------
    heading("REPORTING")
    reports = ReportService(store)
    t.check("revenue counts delivered orders only",
            reports.revenue_paise() == order.bill.total_paise, money(reports.revenue_paise()))
    t.check("delivered list has one order", len(reports.delivered()) == 1)
    t.check("top items ignores cancelled orders",
            all(name != "Dal Tadka" for name, _ in reports.top_items()))
    t.check("average order equals the only delivered total",
            reports.average_order_paise() == order.bill.total_paise)
    t.check("status counts add up to the order count",
            sum(reports.status_counts().values()) == len(store.orders))

    # -- persistence -------------------------------------------------------
    heading("PERSISTENCE")
    t.check("save writes the file", store.save() is True)
    reloaded = DataStore(data_path)
    t.check("reload reports 'loaded'", reloaded.load() == "loaded")
    t.check("order count survives the round trip",
            len(reloaded.orders) == len(store.orders))
    same = reloaded.order(order.order_id)
    t.check("totals survive the round trip", same.bill.total_paise == order.bill.total_paise)
    t.check("enums survive the round trip", same.status is OrderStatus.DELIVERED)
    t.check("datetimes survive the round trip",
            abs((same.placed_at - order.placed_at).total_seconds()) < 1)
    t.check("nested lines survive the round trip",
            [l.to_dict() for l in same.lines] == [l.to_dict() for l in order.lines])
    t.check("wallet balance survives the round trip",
            reloaded.customer("C001").wallet_paise == customer.wallet_paise)

    with open(data_path, "w", encoding="utf-8") as fh:
        fh.write("{ this is not valid json")
    broken = DataStore(data_path)
    t.check("corrupt file is recovered, not fatal", broken.load() == "recovered")
    t.check("recovery reseeds the catalog", len(broken.restaurants) == 5)
    t.check("a backup of the bad file was kept", os.path.exists(data_path + ".bak"))

    # -- cleanup -----------------------------------------------------------
    for name in os.listdir(temp_dir):
        try:
            os.remove(os.path.join(temp_dir, name))
        except OSError:
            pass
    try:
        os.rmdir(temp_dir)
    except OSError:
        pass

    return t.report()


# =============================================================================
# SECTION 14 -- ENTRY POINT
# =============================================================================


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="food_delivery_app.py",
        description="{0} -- a pure-Python food delivery app.".format(APP_NAME),
    )
    parser.add_argument("--data", default=DEFAULT_DATA_FILE,
                        help="path to the JSON data file (default: %(default)s)")
    parser.add_argument("--selftest", action="store_true", help="run the built-in test suite")
    parser.add_argument("--demo", action="store_true", help="run a scripted order, no typing")
    parser.add_argument("--reset", action="store_true", help="delete saved data and reseed")
    parser.add_argument("--version", action="version",
                        version="{0} {1}".format(APP_NAME, APP_VERSION))
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_arg_parser().parse_args(argv)

    if args.reset:
        for path in (args.data, args.data + ".bak"):
            if os.path.exists(path):
                try:
                    os.remove(path)
                    print("Removed {0}".format(path))
                except OSError as exc:
                    print("Could not remove {0}: {1}".format(path, exc))

    if args.selftest:
        return run_self_tests()
    if args.demo:
        return run_demo(args.data)

    store = DataStore(args.data)
    state = store.load()
    if state == "recovered":
        print("\n[note] The data file was unreadable, so it was backed up and reseeded.")
    return FoodDeliveryApp(store).run()


if __name__ == "__main__":
    try:
        sys.exit(main())
    except UserQuit:
        print("\nBye.")
        sys.exit(0)
