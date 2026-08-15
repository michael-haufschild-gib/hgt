import GaloisForLFunctions.HTGeometry.PowerTailSquareIntegrable

/-!
# The polynomial group degree must stay below the Gamma shift

The homogeneous component of the shifted-line value carries the Gamma propagator decay
`(1+|x|)^{-(1/2+σ)}` against the group factor `exp(∓ixB/2)`, whose norm may grow polynomially of
degree `m`.  Its squared density is therefore `|x|^{-1-2σ+2m}`, integrable on a terminal ray exactly
when `m < σ`.

So an arbitrary polynomial degree is *not* enough: past `m = σ` the homogeneous component leaves
`L²` and no amount of rough block forcing can repair it, because forcing changes only the
particular solution.  Both directions are proved: the strict inequality is sufficient, and at
`m ≥ σ` the model density has infinite mass.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **`(14)`: the exact integrability threshold of the distorted homogeneous density.** -/
theorem integrableOn_polyDistortedDensity_iff {σ m : ℝ} :
    IntegrableOn (fun x : ℝ => x ^ (-1 - 2 * σ + 2 * m)) (Ioi (1 : ℝ)) volume ↔ m < σ := by
  rw [integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- **`(15)`, homogeneous half.**  Below the shift the distorted homogeneous component is square
integrable on a terminal ray. -/
theorem lintegral_sq_polyDistorted_ne_top {X : Type*} [NormedAddCommGroup X] {f : ℝ → X}
    {C σ m L₀ : ℝ} (hL₀ : 0 < L₀) (hm : m < σ)
    (hf : ∀ x ∈ Ioi L₀, ‖f x‖ ≤ C * x ^ (-(1 / 2 + σ - m))) :
    (∫⁻ x in Ioi L₀, ‖f x‖ₑ ^ 2) ≠ ⊤ := by
  refine HTGeometry.lintegral_sq_powerTail_ne_top hL₀ ?_ hf
  linarith

/-- **The threshold is sharp.**  At or above the shift the model density has infinite mass, so no
choice of constant rescues the homogeneous component. -/
theorem not_integrableOn_polyDistortedDensity {σ m : ℝ} (hm : σ ≤ m) :
    ¬ IntegrableOn (fun x : ℝ => x ^ (-1 - 2 * σ + 2 * m)) (Ioi (1 : ℝ)) volume := by
  rw [integrableOn_polyDistortedDensity_iff]
  exact not_lt.mpr hm

end GaloisForLFunctions.RHTower
