import Mathlib

/-!
# Dimensioned quantities

A `Quantity d` is a real number tagged with a dimension `d`.  Addition needs
equal dimensions; multiplication and division combine them.  Adding a
concentration to a rate is then a type error.

**What this does not do.**

* It tracks dimensions, not units.  Hours and seconds, or molar and
  millimolar, have the same dimension and are not told apart.
* It does not track the base of a logarithmic rate.  A rate in doublings per
  hour and a rate in base-10 logarithm units per hour both have dimension
  1/time (see `BioLib.Papers.MonodRegoes`, where a factor `log₁₀ 2` is needed).
* Use is opt-in.  The core definitions of the library take bare reals.
  `BioLib.Ecology.Dimensional` shows typed wrappers whose values agree with the
  untyped functions by definition, so untyped theorems apply to them.
-/

namespace BioLib

/-- A dimension: integer exponents of four base dimensions. -/
@[ext] structure Dimension where
  /-- Exponent of time. -/
  time : ℤ := 0
  /-- Exponent of amount of substance. -/
  amount : ℤ := 0
  /-- Exponent of volume. -/
  volume : ℤ := 0
  /-- Exponent of organism count. -/
  count : ℤ := 0
  deriving DecidableEq, Repr

namespace Dimension

instance : One Dimension := ⟨{}⟩

instance : Mul Dimension :=
  ⟨fun a b => ⟨a.time + b.time, a.amount + b.amount, a.volume + b.volume, a.count + b.count⟩⟩

instance : Div Dimension :=
  ⟨fun a b => ⟨a.time - b.time, a.amount - b.amount, a.volume - b.volume, a.count - b.count⟩⟩

/-- Time. -/
def T : Dimension := { time := 1 }
/-- Amount of substance. -/
def N : Dimension := { amount := 1 }
/-- Volume. -/
def V : Dimension := { volume := 1 }
/-- Organism count. -/
def cells : Dimension := { count := 1 }

/-- Concentration: amount per volume. -/
def concentration : Dimension := N / V
/-- Rate: per time. -/
def rate : Dimension := 1 / T
/-- Population density: organisms per volume. -/
def density : Dimension := cells / V

theorem div_mul_cancel (a b : Dimension) : a / b * b = a := by
  ext <;> exact Int.sub_add_cancel _ _

theorem mul_comm (a b : Dimension) : a * b = b * a := by
  ext <;> exact Int.add_comm _ _

theorem mul_one (a : Dimension) : a * 1 = a := by
  ext <;> exact Int.add_zero _

theorem div_self (a : Dimension) : a / a = 1 := by
  ext <;> exact Int.sub_self _

end Dimension

/-- A real quantity of dimension `d`. -/
@[ext] structure Quantity (d : Dimension) where
  /-- The numerical value in whatever coherent unit system the model uses. -/
  val : ℝ

namespace Quantity

variable {d d₁ d₂ : Dimension}

instance : Zero (Quantity d) := ⟨⟨0⟩⟩
instance : Add (Quantity d) := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Sub (Quantity d) := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance : Neg (Quantity d) := ⟨fun a => ⟨-a.val⟩⟩
instance : LT (Quantity d) := ⟨fun a b => a.val < b.val⟩
instance : LE (Quantity d) := ⟨fun a b => a.val ≤ b.val⟩

instance : HMul (Quantity d₁) (Quantity d₂) (Quantity (d₁ * d₂)) :=
  ⟨fun a b => ⟨a.val * b.val⟩⟩

noncomputable instance : HDiv (Quantity d₁) (Quantity d₂) (Quantity (d₁ / d₂)) :=
  ⟨fun a b => ⟨a.val / b.val⟩⟩

/-- Reinterpret a quantity along an equality of dimensions. -/
def cast (_h : d₁ = d₂) (q : Quantity d₁) : Quantity d₂ := ⟨q.val⟩

@[simp] theorem val_zero : (0 : Quantity d).val = 0 := rfl
@[simp] theorem val_add (a b : Quantity d) : (a + b).val = a.val + b.val := rfl
@[simp] theorem val_sub (a b : Quantity d) : (a - b).val = a.val - b.val := rfl
@[simp] theorem val_neg (a : Quantity d) : (-a).val = -a.val := rfl
@[simp] theorem val_mul (a : Quantity d₁) (b : Quantity d₂) : (a * b).val = a.val * b.val := rfl
@[simp] theorem val_div (a : Quantity d₁) (b : Quantity d₂) : (a / b).val = a.val / b.val := rfl
@[simp] theorem val_cast (h : d₁ = d₂) (q : Quantity d₁) : (q.cast h).val = q.val := rfl
theorem lt_def {a b : Quantity d} : a < b ↔ a.val < b.val := Iff.rfl
theorem le_def {a b : Quantity d} : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

end Quantity

end BioLib
