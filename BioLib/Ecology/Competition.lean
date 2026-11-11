import BioLib.Ecology.Growth

/-!
# Multi-species competition (generalized Lotka–Volterra)

For species indexed by `ι`, intrinsic rates `r` and an interaction matrix `A`,

`dxᵢ/dt = xᵢ * (rᵢ + ∑ⱼ Aᵢⱼ xⱼ)`.

Competition corresponds to nonpositive entries of `A`.  With a single species
and `A = -r / K` the model is logistic growth.
-/

open Matrix

namespace BioLib.Ecology

variable {ι : Type*} [Fintype ι]

/-- Generalized Lotka–Volterra vector field. -/
def glvField (r : ι → ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => x i * (r i + (A *ᵥ x) i)

/-- Extinction of every species is an equilibrium. -/
@[simp] theorem glvField_zero (r : ι → ℝ) (A : Matrix ι ι ℝ) : glvField r A 0 = 0 := by
  funext i
  simp [glvField]

/-- Any abundance vector solving `r + A x = 0` is an equilibrium. -/
theorem glvField_eq_zero_of_balance {r : ι → ℝ} {A : Matrix ι ι ℝ} {x : ι → ℝ}
    (h : r + A *ᵥ x = 0) : glvField r A x = 0 := by
  funext i
  have hi : r i + (A *ᵥ x) i = 0 := congrFun h i
  simp [glvField, hi]

/-- A species that is absent stays absent. -/
theorem glvField_apply_eq_zero_of_absent (r : ι → ℝ) (A : Matrix ι ι ℝ) {x : ι → ℝ} {i : ι}
    (h : x i = 0) : glvField r A x i = 0 := by
  simp [glvField, h]

/-- With one species and self-limitation `-r / K`, the model is logistic growth. -/
theorem glvField_unit_eq_logisticRate (r K P : ℝ) :
    glvField (fun _ : Unit => r) (Matrix.of fun _ _ => -r / K) (fun _ => P) () =
      logisticRate r K P := by
  simp [glvField, Matrix.mulVec, dotProduct, logisticRate]
  ring

end BioLib.Ecology
