import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheEscapeRankCountsTheDominantZeros
import GaloisForLFunctions.ArithmeticPolarization.TheCollisionLaw

/-!
# Escape kernels are collided forms

The escape states of the damped Möbius receiver are phase kernels over the dominant translated
zeros `z_k = ½ + x + i y_k` (ACP `TheEscapeRankCountsTheDominantZeros`). Their denominators are
exterior points of conjugate pairs.

* **Cauchy denominators are exterior points** (`cauchy_denominator_eq_extPoint`):
  `2x + i(y_k − y_l) = ext(z_k, z̄_l) − ½`, with `ext(ρ, ρ′) = ρ + ρ′ − ½`. On the diagonal it is the
  collided point `2 Re z_k − ½` shifted by `−½`, i.e. twice the depth.
* **Escape forms are Cauchy forms of the conjugate exterior divisor**
  (`escapeForm_eq_exteriorCauchyForm`, `exteriorCauchyForm_pos`): every escape form is
  `Σ_{k,l} V_k V̄_l / (ext(z_k, z̄_l) − ½)`, the Pick form of the points `z_k − ½` of the right
  half-plane, positive definite on distinct ordinates. It pairs each dominant zero with the
  conjugates of the dominant zeros, never with its reflection `1 − z̄_k`: escape states are
  determinant-type (collided) forms at the dominant depth, of the same kind as the collided form
  `D` of `TheOscillatoryCapacity`, and not Rosati forms. Their positivity is automatic, which is
  why escape classifies the dominant zeros (rank) without excluding them; exclusion needs the
  gauge mass (ACG), a comparison with a Rosati quantity.
-/

open Complex Finset MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

variable {r : ℕ}

/-- The dominant translated zero `z_k = ½ + x + i y_k`. -/
def domZero (x : ℝ) (y : Fin r → ℝ) (k : Fin r) : ℂ := 1 / 2 + x + y k * I

/-- **Cauchy denominators are exterior points of conjugate pairs.** -/
theorem cauchy_denominator_eq_extPoint (x : ℝ) (y : Fin r → ℝ) (k l : Fin r) :
    2 * (x : ℂ) + ((y k : ℂ) - y l) * I = extPoint (domZero x y k) (conj (domZero x y l)) - 1 / 2 := by
  simp only [extPoint, domZero, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀,
    map_one, map_ofNat]
  ring

/-- **Escape forms are Cauchy forms of the conjugate exterior divisor.** -/
theorem escapeForm_eq_exteriorCauchyForm {ι : Type*} (s : Finset ι) (w : ι → ℂ) (p : ι → ℝ)
    (x : ℝ) (y : Fin r → ℝ) (c θ : Fin r → ℂ) :
    ∑ i ∈ s, ∑ i' ∈ s, w i * conj (w i') *
        ArithmeticCorrespondencePositivity.escapeKernel x y c θ (p i) (p i') =
      ∑ k, ∑ l, ArithmeticCorrespondencePositivity.escapeVec s w p x y c θ k *
        conj (ArithmeticCorrespondencePositivity.escapeVec s w p x y c θ l) /
          (extPoint (domZero x y k) (conj (domZero x y l)) - 1 / 2) := by
  rw [ArithmeticCorrespondencePositivity.escapeForm_eq_cauchyForm]
  simp_rw [cauchy_denominator_eq_extPoint]

/-- **The exterior Cauchy form is positive definite** on distinct ordinates at positive depth. -/
theorem exteriorCauchyForm_pos {x : ℝ} (hx : 0 < x) {y : Fin r → ℝ} (hy : Function.Injective y)
    {v : Fin r → ℂ} (hv : v ≠ 0) :
    0 < (∑ k, ∑ l, v k * conj (v l) /
      (extPoint (domZero x y k) (conj (domZero x y l)) - 1 / 2)).re := by
  simp_rw [← cauchy_denominator_eq_extPoint]
  rw [ArithmeticCorrespondencePositivity.cauchyForm_eq_integral hx, Complex.ofReal_re]
  exact ArithmeticCorrespondencePositivity.integral_cauchyDensity_pos hx hy hv

end GaloisForLFunctions.ArithmeticPolarization
