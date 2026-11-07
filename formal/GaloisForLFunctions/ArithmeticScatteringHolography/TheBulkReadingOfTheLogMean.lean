import GaloisForLFunctions.BlackHoleRingdown.TheCausalSymbolOfTheModularHorizon
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheLogMeanIsTheInnerMassAtInfinity
import GaloisForLFunctions.RHTower.CompactTestXiDivisibilityObstruction

/-!
# The bulk reading of the log-mean

On the universal line `Im ω = -(D + ¼)` the causal symbol of the modular horizon has a transparent form:
it is `Ξ(z + i)/Ξ(z)` at real `z`, and `Ξ(z) = ξ(½ + iz)` is `ξ` on the critical line
(`causalSymbol_universalFrequency`, `log_norm_causalSymbol_universal`). So a pole on this line is a zero on the
line, and the mean of `log |ζ|` on the critical line is the **Bode integral of the causal symbol at
universal damping**.

The bulk reading is then the following.

* **The Bode deficit is a sum of damping deficits.** The Poisson-weighted Bode integral is the Green potential of the
  right zeros (`bode_hasSum`), and each right zero has a damping deficit `¼ - rate = (β - ½)/2 > 0`
  (`rateDeficit_pos`).
* **The log-mean is the density of the deficit.** The Abel log-mean tends to zero exactly when the deficits have
  density zero (`bode_tendsto_iff_deficit_density`). So the question of the log-mean is whether, on average at large
  scale, modes ring at the universal rate. A single slow mode is invisible to it.
* **Over a curve the same integral is exact.** It is `2 log q · Σ (¼ - rate)⁺` (`bode_integral`,
  `posLog_eq_rate_deficit`), and it vanishes exactly under universal damping.
-/

open Complex Filter Topology MeasureTheory
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

open GaloisForLFunctions.BlackHoleRingdown ArithmeticInnerFunctionTheory
open _root_.RHTower

/-- The frequency on the universal line with resonance coordinate `z`: rate exactly `D + ¼`. -/
def universalFrequency (D z : ℝ) : ℂ := -((z : ℂ) / 2) - I * ((D : ℂ) + 1 / 4)

theorem causalCoordinate_universalFrequency (D z : ℝ) :
    causalCoordinate D (universalFrequency D z) = (z : ℂ) := by
  unfold causalCoordinate universalFrequency
  ring_nf

/-- The universal frequency has damping exactly `D + ¼`. -/
theorem universalFrequency_im (D z : ℝ) : (universalFrequency D z).im = -(D + 1 / 4) := by
  simp [universalFrequency]

/-- **On the universal line the causal symbol is `Ξ(z + i)/Ξ(z)`.** -/
theorem causalSymbol_universalFrequency (D z : ℝ) :
    causalSymbol D (universalFrequency D z) = XiC ((z : ℂ) + I) / xi (1 / 2 + (z : ℂ) * I) := by
  rw [causalSymbol, causalCoordinate_universalFrequency, thetaCuspHawkingOpticalCuspScattering,
    thetaCuspHawkingOpticalCuspNumerator, thetaCuspHawkingOpticalCuspDenominator,
    CompactTestXiDivisibility.XiC_ofReal_eq_xi_linePt]
  have e : linePt z = 1 / 2 + (z : ℂ) * I := by simp [linePt]
  rw [e]

/-- **A pole on the universal line is a zero on the critical line.** The density of `log` of the symbol there splits
into the critical-line term and a regular term. -/
theorem log_norm_causalSymbol_universal (D z : ℝ) (h0 : xi (1 / 2 + (z : ℂ) * I) ≠ 0)
    (h1 : XiC ((z : ℂ) + I) ≠ 0) :
    Real.log ‖causalSymbol D (universalFrequency D z)‖ =
      Real.log ‖XiC ((z : ℂ) + I)‖ - Real.log ‖xi (1 / 2 + (z : ℂ) * I)‖ := by
  rw [causalSymbol_universalFrequency, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h0)]

/-! ### The deficit -/

/-- The damping deficit of a zero, below the universal rate: `¼ - (1-β)/2 = (β - ½)/2`. -/
def rateDeficit (ρ : ℂ) : ℝ := 1 / 4 - (1 - ρ.re) / 2

theorem rateDeficit_eq (ρ : ℂ) : rateDeficit ρ = depth ρ / 2 := by
  unfold rateDeficit depth
  ring

/-- A right zero rings slower than universal. -/
theorem rateDeficit_pos (ρ : ZetaRightZero) : 0 < rateDeficit (ρ : ℂ) := by
  rw [rateDeficit_eq]
  have := ρ.2.2
  unfold depth
  linarith

/-- **The Poisson-weighted Bode integral is the Green potential of the slow modes.** -/
theorem bode_hasSum {w : ℂ} (hw : 1 / 2 < w.re) (h0 : zetaEntire w ≠ 0) :
    HasSum (fun ρ : ZetaRightZero => zeroMult ρ * greenKernel w ρ)
      ((∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) +
        Real.log ‖w‖ - Real.log ‖zetaEntire w‖) :=
  hasSum_innerField hw h0

/-- **The log-mean is the density of the deficit.** The Abel log-mean of `ζ` on the critical line tends to zero exactly
when the damping deficits have density zero. -/
theorem bode_tendsto_iff_deficit_density (t : ℝ) :
    Tendsto (fun x : ℝ => ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ *
      halfPlanePoissonKernel (centre x t) τ) atTop (𝓝 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Z : Finset ZetaRightZero,
        (∀ ρ ∈ Z, |(ρ : ℂ).im - t| ≤ T) → ∑ ρ ∈ Z, zeroMult ρ * rateDeficit ρ ≤ ε * T := by
  rw [tendsto_poisson_log_iff_depthDensity]
  constructor
  · intro h ε hε
    obtain ⟨T₀, hT⟩ := h (2 * ε) (by positivity)
    refine ⟨T₀, fun T hT₀ Z hZ => ?_⟩
    have := hT T hT₀ Z hZ
    have e : ∑ ρ ∈ Z, zeroMult ρ * rateDeficit ρ = (∑ ρ ∈ Z, zeroMult ρ * depth ρ) / 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [rateDeficit_eq]
      ring
    rw [e]
    linarith
  · intro h ε hε
    obtain ⟨T₀, hT⟩ := h (ε / 2) (by positivity)
    refine ⟨T₀, fun T hT₀ Z hZ => ?_⟩
    have := hT T hT₀ Z hZ
    have e : ∑ ρ ∈ Z, zeroMult ρ * rateDeficit ρ = (∑ ρ ∈ Z, zeroMult ρ * depth ρ) / 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [rateDeficit_eq]
      ring
    rw [e] at this
    linarith

end GaloisForLFunctions.ArithmeticScatteringHolography

end
