import BioLib.Foundations.Quantities
import BioLib.Foundations.Saturation
import BioLib.Ecology.Inhibition

/-!
# Dimension-checked versions of the saturation and inhibition models

Typed wrappers around `saturation` and `netGrowthRate`.  Their signatures state
the dimensional contract of each model:

* in `vmax * x / (K + x)`, `K` and `x` have the same dimension and the result
  has the dimension of `vmax`;
* in `r - α * B`, the sensitivity `α` has dimension rate per concentration.

The values agree with the untyped functions by definition, so every untyped
theorem transfers.  The composition at the end type-checks only because the
output dimension of the first model is the input dimension of the second.
-/

namespace BioLib.Ecology.Dimensional

open BioLib Dimension

variable {d c : Dimension}

/-- Saturation response with dimensions: the input and half-saturation constant
share a dimension, the output has the dimension of the maximum. -/
noncomputable def saturationQ (vmax : Quantity d) (K x : Quantity c) : Quantity d :=
  ⟨saturation vmax.val K.val x.val⟩

@[simp] theorem saturationQ_val (vmax : Quantity d) (K x : Quantity c) :
    (saturationQ vmax K x).val = saturation vmax.val K.val x.val := rfl

/-- Net growth rate with dimensions: `α` is a rate per concentration. -/
def netGrowthRateQ (r : Quantity rate) (α : Quantity (rate / concentration))
    (B : Quantity concentration) : Quantity rate :=
  r - (α * B).cast (Dimension.div_mul_cancel rate concentration)

@[simp] theorem netGrowthRateQ_val (r : Quantity rate) (α : Quantity (rate / concentration))
    (B : Quantity concentration) :
    (netGrowthRateQ r α B).val = netGrowthRate r.val α.val B.val := rfl

/-- Typed composition: nutrient concentration to compound concentration to net
growth rate. -/
noncomputable def composedGrowthQ (r : Quantity rate) (α : Quantity (rate / concentration))
    (Bmax : Quantity concentration) (K N : Quantity concentration) : Quantity rate :=
  netGrowthRateQ r α (saturationQ Bmax K N)

/-- The untyped criterion for negative growth applies to the typed model. -/
theorem netGrowthRateQ_neg_iff {r : Quantity rate} {α : Quantity (rate / concentration)}
    {B : Quantity concentration} (hα : 0 < α.val) :
    netGrowthRateQ r α B < 0 ↔ r.val / α.val < B.val := by
  rw [Quantity.lt_def, netGrowthRateQ_val, Quantity.val_zero]
  exact netGrowthRate_neg_iff hα

end BioLib.Ecology.Dimensional
