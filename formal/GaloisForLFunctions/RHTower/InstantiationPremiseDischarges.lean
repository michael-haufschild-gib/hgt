import GaloisForLFunctions.RHTower.SmoothAFEZetaRightReflectedPrimalMass
import GaloisForLFunctions.RHTower.XiMassPrefixQuadratureDefect
import GaloisForLFunctions.RHTower.ConstrainedWeilApertureConstantTerm
import GaloisForLFunctions.RHTower.ConstrainedWeilApertureWindowMean

set_option autoImplicit false

/-!
# Premises discharged by instantiating corpus theorems

* the inner bound `1/2 ≤ ‖smoothAFECutoff u‖` on `(0, r]` — `exists_smoothAFECutoff_inner_norm_lower`
  fixes one radius `r` for every channel;
* `0 ≤ xiMassVerticalBound σ` — `xiMassVerticalBound_nonneg`;
* `(xiSpectralPoint q).re ≠ 0` — `xiSpectralPoint_re_ne_zero`.
-/

namespace RHTower

open Complex Finset Nat

noncomputable section

/-- One fixed cutoff radius keeps a quarter of every terminal power-square weight. -/
theorem quarter_terminalPowerSquareWeight_le_reflectedCutoff_uniform :
    ∃ r : ℝ, 0 < r ∧ ∀ (d : ℝ) (N n : ℕ), 0 < N → 0 < n → n ≤ N →
      (1 / 4 : ℝ) * terminalPowerSquareWeight d N n ≤
        terminalReflectedCutoffSquareWeight d r N n := by
  obtain ⟨r, hr, hcut⟩ := exists_smoothAFECutoff_inner_norm_lower
  exact ⟨r, hr, fun d N n hN hn hnN =>
    quarter_terminalPowerSquareWeight_le_reflectedCutoff (d := d) hr hcut hN hn hnN⟩

/-- One fixed cutoff radius keeps a quarter of every reciprocal-prime channel lower bound. -/
theorem normalized_reflected_cutoff_channel_lower_recip_uniform :
    ∃ r : ℝ, 0 < r ∧ ∀ d : ℝ, 0 < d → d < 1 / 2 → ∀ N p : ℕ, 0 < p → 2 * p ≤ N →
      (1 / 4 : ℝ) * (((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) * ((p : ℝ)⁻¹)) ≤
        ∑ m ∈ dyadicCofactorBlock N p, terminalReflectedCutoffSquareWeight d r N (p * m) := by
  obtain ⟨r, hr, hcut⟩ := exists_smoothAFECutoff_inner_norm_lower
  exact ⟨r, hr, fun d hd0 hdhalf N p hp h2p =>
    normalized_reflected_cutoff_channel_lower_recip hd0 hdhalf hr hcut hp h2p⟩

/-- The cone prime-index sum bound is monotone in the cutoff. -/
theorem conePrimeIndexSumBound_mono_unconditional {sigma : ℝ} {M N : ℕ} (h : M ≤ N) :
    (M : ℝ) * (Real.log ((M : ℝ) + 1) * xiMassVerticalBound sigma) ≤
      (N : ℝ) * (Real.log ((N : ℝ) + 1) * xiMassVerticalBound sigma) :=
  conePrimeIndexSumBound_mono h (xiMassVerticalBound_nonneg sigma)

/-- The two ray frequencies of a zero copy never cancel. -/
theorem rayFreq_sum_ne_zero_unconditional (γ : ℝ) (q : XiZeroCopy) :
    rayFreq₁ γ q + rayFreq₂ γ q ≠ 0 :=
  rayFreq_sum_ne_zero γ (xiSpectralPoint_re_ne_zero q)

end

end RHTower
