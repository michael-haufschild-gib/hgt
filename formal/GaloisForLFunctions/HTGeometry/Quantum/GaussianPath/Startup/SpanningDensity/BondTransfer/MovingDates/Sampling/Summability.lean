import Mathlib.Probability.BorelCantelli
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Summability for polynomially many exponentially unlikely windows -/

open MeasureTheory Filter Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
noncomputable section

/-- Polynomially many trials of exponentially small risk give only finitely
many failures on a single draw, without independence between sample sizes. -/
theorem avoid_exponential_windows {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : ℕ→Set Ω) (p : ℕ) (A : ℝ) {c : ℝ} (hc : 0<c)
    (hrisk : ∀ᶠ j : ℕ in atTop, μ.real (E j)≤A*((j:ℝ)^p*exp (-c*j))) :
    ∀ᵐ ω ∂μ, ∀ᶠ j : ℕ in atTop, ω∉E j := by
  have hq : ‖exp (-c)‖<1 := by
    rw [Real.norm_of_nonneg (exp_pos _).le]
    exact exp_lt_one_iff.mpr (neg_lt_zero.mpr hc)
  have hs := (summable_pow_mul_geometric_of_norm_lt_one p hq).mul_left A
  have hx : Summable fun j => μ.real (E j) := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [hrisk] with j hj
    rw [Real.norm_of_nonneg measureReal_nonneg]
    simpa only [←exp_nat_mul,mul_comm (j:ℝ) (-c)] using hj
  apply ae_eventually_notMem
  simpa only [ofReal_measureReal (measure_ne_top _ _)] using hx.tsum_ofReal_ne_top

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
