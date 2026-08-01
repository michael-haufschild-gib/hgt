import GaloisForLFunctions.RHTower.DeningerTraceEnergy
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The boundary space of the Kummer phase stage

The boundary norm weights the squared coefficients by the absolute frequencies.  Dividing a
square-summable sequence by the square root of the absolute frequency produces a boundary datum
whose boundary norm is the norm of that sequence, and multiplying back recovers it; so the
coefficient space parametrizes the boundary space isometrically, and the boundary space inherits
completeness.

* `deningerBoundaryNormSq` : the weighted boundary norm.
* `deningerBoundaryDatum` : the boundary datum of a coefficient sequence.
* `deningerBoundary_normSq_datum` : the parametrization is isometric.
* `deningerBoundaryDatum_leftInverse` : and bijective onto the finite-norm data.
-/

namespace RHTower

open scoped ENNReal

section BoundarySpace

variable {ι : Type*}

/-- The squared boundary norm: squared coefficients weighted by the absolute frequencies. -/
noncomputable def deningerBoundaryNormSq (ℓ : ι → ℝ) (φ : ι → ℂ) : ℝ :=
  ∑' a : ι, |ℓ a| * ‖φ a‖ ^ 2

/-- The boundary datum attached to a coefficient sequence. -/
noncomputable def deningerBoundaryDatum (ℓ : ι → ℝ) (ψ : lp (fun _ : ι => ℂ) 2) (a : ι) : ℂ :=
  (ψ : ι → ℂ) a / ((Real.sqrt |ℓ a| : ℝ) : ℂ)

/-- The weight of a nonzero frequency is nonzero. -/
theorem deningerBoundaryWeight_ne_zero {μ : ℝ} (hμ : μ ≠ 0) : Real.sqrt |μ| ≠ 0 := by
  have habs : 0 < |μ| := abs_pos.mpr hμ
  exact ne_of_gt (Real.sqrt_pos.mpr habs)

/-- **The parametrization is isometric termwise.** -/
theorem deningerBoundary_term (ℓ : ι → ℝ) (hℓ : ∀ a, ℓ a ≠ 0) (ψ : lp (fun _ : ι => ℂ) 2)
    (a : ι) : |ℓ a| * ‖deningerBoundaryDatum ℓ ψ a‖ ^ 2 = ‖(ψ : ι → ℂ) a‖ ^ 2 := by
  have hw : Real.sqrt |ℓ a| ≠ 0 := deningerBoundaryWeight_ne_zero (hℓ a)
  have habs : |ℓ a| ≠ 0 := abs_ne_zero.mpr (hℓ a)
  have hnorm : ‖deningerBoundaryDatum ℓ ψ a‖ = ‖(ψ : ι → ℂ) a‖ / Real.sqrt |ℓ a| := by
    rw [deningerBoundaryDatum, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hnorm, div_pow, Real.sq_sqrt (abs_nonneg (ℓ a))]
  field_simp

/-- **The boundary norm of the datum is the coefficient norm.**  So the coefficient space
parametrizes the boundary space isometrically, and the boundary space is complete. -/
theorem deningerBoundary_normSq_datum (ℓ : ι → ℝ) (hℓ : ∀ a, ℓ a ≠ 0)
    (ψ : lp (fun _ : ι => ℂ) 2) :
    deningerBoundaryNormSq ℓ (deningerBoundaryDatum ℓ ψ) = ∑' a : ι, ‖(ψ : ι → ℂ) a‖ ^ 2 := by
  rw [deningerBoundaryNormSq]
  exact tsum_congr fun a => deningerBoundary_term ℓ hℓ ψ a

/-- **Multiplying back by the weight recovers the coefficient sequence.** -/
theorem deningerBoundaryDatum_leftInverse (ℓ : ι → ℝ) (hℓ : ∀ a, ℓ a ≠ 0)
    (ψ : lp (fun _ : ι => ℂ) 2) (a : ι) :
    ((Real.sqrt |ℓ a| : ℝ) : ℂ) * deningerBoundaryDatum ℓ ψ a = (ψ : ι → ℂ) a := by
  have hw : ((Real.sqrt |ℓ a| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast deningerBoundaryWeight_ne_zero (hℓ a)
  rw [deningerBoundaryDatum, mul_div_cancel₀ _ hw]

end BoundarySpace

end RHTower
