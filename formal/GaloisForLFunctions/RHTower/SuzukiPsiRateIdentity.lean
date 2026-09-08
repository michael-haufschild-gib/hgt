import GaloisForLFunctions.RHTower.SuzukiScrewSubexponentialCriterion
import GaloisForLFunctions.RHTower.SuzukiScrewFormExcessLowerBound

/-!
# The exact exponential rate of Suzuki's screw function is the top excess

Suzuki's explicit screw function `Ψ(t) = Σ'_q (1 − cos(z_q t))/z_q²` is bounded below by
`−(e^{Θ t} + 1) Σ'_q ‖z_q‖⁻²` on the source half-line whenever every spectral point has
`|Im z_q| ≤ Θ`; in particular `Ψ(t) ≥ −2 Σ'_q ‖z_q‖⁻² · e^{Θ_sup t}`.  Together with the corpus's
strip law (a one-sided bound `Ψ(t) ≥ −C e^{εt}` confines every copy to `|Im z_q| ≤ ε`), this gives the
exact identity: for `ε ≥ 0`, `Ψ(t) ≥ −C e^{εt}` on `t ≥ 0` for some `C` if and only if `Θ_sup ≤ ε`.

On the source half-line `Ψ` is the explicit smooth part minus the prime hinge sum
`Σ_{2 ≤ n ≤ e^t} Λ(n) n^{−1/2} (t − log n)`, so the same identity reads: **the top horizontal excess
of the zeta zeros is the exponential growth rate of the excess of the prime hinge sum over its
archimedean main term.**
-/

open Complex

namespace RHTower

noncomputable section

theorem xiSpectralInvSqSum_nonneg' : 0 ≤ xiSpectralInvSqSum :=
  tsum_nonneg fun _ => by positivity

/-- Screw summand bound with a general excess bound `|Im z_q| ≤ Θ`. -/
theorem norm_xiScrewDivisorTerm_le_of_im_le {Θ : ℝ}
    (hΘ : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) (t : ℝ) (q : XiZeroCopy) :
    ‖xiScrewDivisorTerm t q‖ ≤ (Real.exp (Θ * |t|) + 1) / ‖xiSpectralPoint q‖ ^ 2 := by
  set w : ℂ := I * xiSpectralPoint q with hw
  have hwre : |w.re| ≤ Θ := by
    have : w.re = -(xiSpectralPoint q).im := by
      simp [hw, Complex.mul_re]
    rw [this, abs_neg]
    exact hΘ q
  have hΘ0 : 0 ≤ Θ := le_trans (abs_nonneg _) (hΘ q)
  have htre : |(((t : ℂ) * w).re)| ≤ Θ * |t| := by
    rw [Complex.mul_re]
    simp only [ofReal_re, ofReal_im, zero_mul, sub_zero, abs_mul]
    calc |t| * |w.re| ≤ |t| * Θ := mul_le_mul_of_nonneg_left hwre (abs_nonneg _)
      _ = Θ * |t| := by ring
  have hcosh : ‖Complex.cosh ((t : ℂ) * w)‖ ≤ Real.exp (Θ * |t|) :=
    (norm_cosh_le_exp_abs_re _).trans (Real.exp_le_exp.mpr htre)
  rw [xiScrewDivisorTerm, norm_div, norm_pow, norm_mul, norm_I, one_mul]
  calc
    ‖Complex.cosh ((t : ℂ) * w) - 1‖ / ‖xiSpectralPoint q‖ ^ 2 ≤
        (‖Complex.cosh ((t : ℂ) * w)‖ + 1) / ‖xiSpectralPoint q‖ ^ 2 := by
      gcongr
      simpa using norm_sub_le (Complex.cosh ((t : ℂ) * w)) 1
    _ ≤ (Real.exp (Θ * |t|) + 1) / ‖xiSpectralPoint q‖ ^ 2 := by
      gcongr

/-- **Upper half of the rate law.**  `Ψ(t) ≥ −(e^{Θt} + 1) Σ'_q ‖z_q‖⁻²` on the source half-line
when every copy has `|Im z_q| ≤ Θ`. -/
theorem suzukiPsi_ge_of_im_le {Θ : ℝ} (hΘ : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ)
    {t : ℝ} (ht : 0 ≤ t) :
    -((Real.exp (Θ * t) + 1) * xiSpectralInvSqSum) ≤ suzukiPsi t := by
  rw [suzukiPsi_eq_xiScrewDivisor_re ht, xiScrewDivisor]
  have hsum := xiScrewDivisorTerm_summable t
  rw [Complex.re_tsum hsum]
  have hre : Summable fun q => (xiScrewDivisorTerm t q).re :=
    (hsum.hasSum.mapL Complex.reCLM).summable
  have hg : Summable fun q : XiZeroCopy =>
      (Real.exp (Θ * t) + 1) * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  have hle : ∀ q, -((Real.exp (Θ * t) + 1) * (1 / ‖xiSpectralPoint q‖ ^ 2)) ≤
      (xiScrewDivisorTerm t q).re := by
    intro q
    have h1 := (abs_le.mp (Complex.abs_re_le_norm (xiScrewDivisorTerm t q))).1
    have h2 := norm_xiScrewDivisorTerm_le_of_im_le hΘ t q
    rw [abs_of_nonneg ht] at h2
    have : (Real.exp (Θ * t) + 1) / ‖xiSpectralPoint q‖ ^ 2 =
        (Real.exp (Θ * t) + 1) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring
    linarith
  have := Summable.tsum_le_tsum hle hg.neg hre
  rw [tsum_neg, Summable.tsum_mul_left _ xiSpectralPoint_inv_sq_summable] at this
  exact this

/-- **`Ψ` has exponential negativity rate `ε`**: `Ψ(t) ≥ −C e^{εt}` on `t ≥ 0`. -/
def SuzukiPsiRate (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → -(C * Real.exp (ε * t)) ≤ suzukiPsi t

theorem SuzukiPsiRate.mono {ε ε' : ℝ} (h : SuzukiPsiRate ε) (hle : ε ≤ ε') : SuzukiPsiRate ε' := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun t ht => le_trans ?_ (hb t ht)⟩
  rw [neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hle ht)) hC

/-- Rate `Θ_sup` holds, with constant `2 Σ'_q ‖z_q‖⁻²`. -/
theorem suzukiPsiRate_topExcess : SuzukiPsiRate xiTopExcess := by
  refine ⟨2 * xiSpectralInvSqSum, by linarith [xiSpectralInvSqSum_nonneg'], fun t ht => ?_⟩
  refine le_trans ?_ (suzukiPsi_ge_of_im_le abs_im_xiSpectralPoint_le_xiTopExcess ht)
  rw [neg_le_neg_iff]
  have h1 : 1 ≤ Real.exp (xiTopExcess * t) :=
    Real.one_le_exp (mul_nonneg xiTopExcess_nonneg ht)
  have hS := xiSpectralInvSqSum_nonneg'
  nlinarith

/-- A rate `ε ≥ 0` bounds the top excess. -/
theorem xiTopExcess_le_of_suzukiPsiRate {ε : ℝ} (hε0 : 0 ≤ ε) (h : SuzukiPsiRate ε) :
    xiTopExcess ≤ ε := by
  obtain ⟨C, _, hb⟩ := h
  exact Real.iSup_le (fun q => abs_im_xiSpectralPoint_le_of_suzukiPsi_ge' hb hε0 q) hε0

/-- **Exact rate identity for Suzuki's screw function.**  For `ε ≥ 0`, `Ψ` has negativity rate `ε`
if and only if `Θ_sup ≤ ε`. -/
theorem suzukiPsiRate_iff {ε : ℝ} (hε0 : 0 ≤ ε) : SuzukiPsiRate ε ↔ xiTopExcess ≤ ε :=
  ⟨xiTopExcess_le_of_suzukiPsiRate hε0, fun h => suzukiPsiRate_topExcess.mono h⟩

/-- **The prime hinge sum exceeds its smooth part at rate `ε`.** -/
def ScrewPrimeSumRate (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
    GaloisForLFunctions.RHTower.screwPrimeSum t ≤
      ccmGuinandWeilXiScrewSmoothPart t + C * Real.exp (ε * t)

theorem screwPrimeSumRate_iff_suzukiPsiRate {ε : ℝ} :
    ScrewPrimeSumRate ε ↔ SuzukiPsiRate ε := by
  constructor
  · rintro ⟨C, hC, hb⟩
    refine ⟨C, hC, fun t ht => ?_⟩
    rw [suzukiPsi_eq_smoothPart_sub_screwPrimeSum ht]
    linarith [hb t ht]
  · rintro ⟨C, hC, hb⟩
    refine ⟨C, hC, fun t ht => ?_⟩
    have := hb t ht
    rw [suzukiPsi_eq_smoothPart_sub_screwPrimeSum ht] at this
    linarith

/-- **The top excess of the zeta zeros is the exponential rate of the prime hinge excess.**
For `ε ≥ 0`: `Σ_{2≤n≤e^t} Λ(n) n^{−1/2}(t − log n) ≤ smooth(t) + C e^{εt}` on `t ≥ 0` for some `C`
if and only if every zero satisfies `|Re ρ − ½| ≤ ε`. -/
theorem screwPrimeSumRate_iff {ε : ℝ} (hε0 : 0 ≤ ε) :
    ScrewPrimeSumRate ε ↔ xiTopExcess ≤ ε := by
  rw [screwPrimeSumRate_iff_suzukiPsiRate]
  exact suzukiPsiRate_iff hε0

end

end RHTower
