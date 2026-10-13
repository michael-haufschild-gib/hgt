import GaloisForLFunctions.RHTower.GaussianCentralGapFilterLightCone
import GaloisForLFunctions.RHTower.XiSliceEventualPositivityFiniteOffLine
import GaloisForLFunctions.RHTower.XiCosineShiftLaguerrePolya
import GaloisForLFunctions.RHTower.LindelofCosineFiniteDefectDepth

/-!
# The Gaussian central gap at large heights: finitely many off-line zeros, zeros near the line

Let `F(ε, τ)` be the Gaussian-filtered central prime gap at scale `ε` and height `2τ`
(`gaussianFilteredCentralGap`).  The corpus criterion says RH holds iff `F(·, τ) = O(√ε)` on `ε ≥ 1`
for every height `τ` (`riemannHypothesis_iff_filteredCentralGap_isBigO`).  The window reads the
zeros through the light-cone exponent
`Re w_ρ(τ) = (γ/2 − τ)²/2 − b − b²/8`, `b = Re ρ − ½`, `γ = Im ρ`.

**Theorem** (`eventualFilteredCentralGapBudget_iff_finiteOffLine`).  The filtered gap is
`O(√ε)` at every large height (`|τ| ≥ T` for some `T`) iff only finitely many zeros of `ξ` lie off
the critical line.

**Theorem** (`eventualFilteredCentralGapSubexponential_iff_zerosApproachLine`).  The filtered gap is
`O(e^{sε}√ε)` at every large height for every rate `s > 0` iff the zeros approach the critical line
(for every `h > 0` only finitely many zeros have `|β − ½| > h`).

**Theorem** (`eventualFilteredCentralGapRate_iff`, `..._iff_finite_re_gt`).  For `s ≥ 0` the
filtered gap is `O(e^{sε}√ε)` at every large height iff only finitely many zeros have
`b + b²/8 > s`.  At `s = h + h²/8` this reads: only finitely many zeros have `Re ρ > ½ + h`.  So the
optimal large-height growth rate is `Θ + Θ²/8`, where `Θ` is the limit superior of
`Re ρ − ½` as the height grows.

**Theorem** (`filteredCentralGapRate_iff`, `filteredCentralGapRate_iff_re_le`).  At all heights the
same reading holds with the full abscissa: the gap is `O(e^{sε}√ε)` at every height iff every zero
has `b + b²/8 ≤ s`.  Since `b < ½`, the rate `17/32` holds unconditionally
(`filteredCentralGapRate_seventeen_thirtySeconds`); a rate below `17/32` is a zero-free strip, and
rate `0` is RH.

So the Gaussian central-gap receiver of route TG reads the large-height ladder through its growth
rate.  Bounded `O(√ε)` growth is FOL, subexponential growth is ZAL, and the all-height bounded form
is RH.

**Proof.**
* **Height-local lemmas.**
  - If every zero has `Re w_ρ(τ) ≥ 0`, the zero series is bounded and `F(·, τ) = O(√ε)`
    (`exists_filteredCentralGap_le_of_re_nonneg`).
  - If one zero has `Re w_ρ(τ) < 0`, light-cone amplification makes `F(·, τ)` grow faster than every
    `C√ε` (`not_exists_filteredCentralGap_le_of_re_neg`).

  Both are extracted from the corpus proof of the RH criterion.
* (⇐) With finitely many off-line zeros of height `≤ H`, every `|τ| ≥ H/2 + 2` puts every zero
  outside the light cone.
* (⇒) Infinitely many off-line zeros give, after reflection, zeros right of the line at arbitrarily
  large heights `γ`.  At `τ = γ/2` such a zero has `Re w = −(b + b²/8) < 0`.
* The ZAL rung uses the rate-`s` versions of both lemmas
  (`exists_filteredCentralGap_le_exp_of_re_ge`, `not_exists_filteredCentralGap_le_exp_of_re_lt`):
  every zero with `|b| ≤ h` has `Re w ≥ −(h + h²/8)`, and a zero with `b > h` at its own height has
  `Re w < −h`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- **Outside the light cone the filtered gap is `O(√ε)`.** -/
theorem exists_filteredCentralGap_le_of_re_nonneg {τ : ℝ}
    (h : ∀ q : XiZeroCopy, 0 ≤ (zeroLightConeExponent τ q).re) :
    ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε → ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.sqrt ε := by
  obtain ⟨C₀, hC₀, hexp⟩ := exists_norm_filteredGap_add_zeroSeries_le
  have hAs : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := summable_norm_zeroBohrAmplitude
  set A : ℝ := ∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hsqrt : ∀ ε : ℝ, 0 ≤ ε →
      Real.sqrt (2 * Real.pi * ε) = Real.sqrt (2 * Real.pi) * Real.sqrt ε :=
    fun ε hε => Real.sqrt_mul (by positivity) ε
  have hsum_le : ∀ ε : ℝ, 0 ≤ ε → ∀ τ : ℝ,
      Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ := by
    intro ε hε τ
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      (hAs.mul_right (Real.exp ε))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_neg_mul_zeroLightConeExponent_le hε τ q)
      (norm_nonneg _)
  refine ⟨C₀ * (Real.sqrt (2 * Real.pi) + 1) + Real.sqrt (2 * Real.pi) * A, fun ε hε => ?_⟩
  have hε0 : 0 < ε := by linarith
  have hs1 : 1 ≤ Real.sqrt ε := Real.one_le_sqrt.2 hε
  have hZ : ‖∑' q : XiZeroCopy, zeroBohrAmplitude q *
      Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤ A := by
    refine (norm_tsum_le_tsum_norm (hsum_le ε hε0.le τ)).trans ?_
    refine Summable.tsum_le_tsum (fun q => ?_) (hsum_le ε hε0.le τ) hAs
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(ε : ℂ) * zeroLightConeExponent τ q).re =
        -(ε * (zeroLightConeExponent τ q).re) := by
      simp
    rw [hre]
    have := h q
    have hle : Real.exp (-(ε * (zeroLightConeExponent τ q).re)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith [norm_nonneg (zeroBohrAmplitude q)]
  have h1 := hexp ε hε0 τ
  have he : Real.exp (-2 * ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have htri := norm_sub_le
      (gaussianFilteredCentralGap ε τ + ((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
      ∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q))
    (((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
      ∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q))
  rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at htri
  rw [hsqrt ε hε0.le] at htri h1
  have hspi : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hsε : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hprod : Real.sqrt (2 * Real.pi) * Real.sqrt ε *
      ‖∑' q : XiZeroCopy, zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt ε * A := by gcongr
  nlinarith

/-- **A zero inside the light cone makes the filtered gap outgrow every `C√ε`.** -/
theorem not_exists_filteredCentralGap_le_of_re_neg {τ : ℝ} {q₀ : XiZeroCopy}
    (hneg : (zeroLightConeExponent τ q₀).re < 0) :
    ¬ ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε → ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.sqrt ε := by
  rintro ⟨Cτ, hCτ⟩
  obtain ⟨C₀, hC₀, hexp⟩ := exists_norm_filteredGap_add_zeroSeries_le
  have hAs : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := summable_norm_zeroBohrAmplitude
  set A : ℝ := ∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hsqrt : ∀ ε : ℝ, 0 ≤ ε →
      Real.sqrt (2 * Real.pi * ε) = Real.sqrt (2 * Real.pi) * Real.sqrt ε :=
    fun ε hε => Real.sqrt_mul (by positivity) ε
  have hsum_le : ∀ ε : ℝ, 0 ≤ ε → ∀ τ : ℝ,
      Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ := by
    intro ε hε τ
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      (hAs.mul_right (Real.exp ε))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_neg_mul_zeroLightConeExponent_le hε τ q)
      (norm_nonneg _)
  have hfin : {q : XiZeroCopy | (zeroLightConeExponent τ q).re < 0}.Finite := by
    refine (finite_xiZeroCopy_norm_le (1 / 2 + (2 * |τ| + 4))).subset fun q hq => ?_
    simp only [mem_setOf_eq] at hq ⊢
    rw [re_zeroLightConeExponent] at hq
    have hb := re_xiZero_sub_half_bounds q
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    have hγ : ((xiZero q).im / 2 - τ) ^ 2 < 4 := by nlinarith
    have hγ' : |(xiZero q).im / 2 - τ| < 2 := by
      rw [← Real.sqrt_sq_eq_abs]
      calc Real.sqrt (((xiZero q).im / 2 - τ) ^ 2) < Real.sqrt 4 :=
          Real.sqrt_lt_sqrt (sq_nonneg _) hγ
        _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have him : |(xiZero q).im| ≤ 2 * |τ| + 4 := by
      have := abs_sub_abs_le_abs_sub ((xiZero q).im / 2) τ
      rw [abs_div, abs_two] at this
      linarith
    rw [norm_xiSpectralPoint]
    calc ‖xiZero q - 1 / 2‖ ≤ |(xiZero q - 1 / 2).re| + |(xiZero q - 1 / 2).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 / 2 + (2 * |τ| + 4) := by
          have h1 : |(xiZero q - 1 / 2).re| ≤ 1 / 2 := by
            simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
            exact abs_le.2 ⟨by linarith, by linarith⟩
          have h2 : (xiZero q - 1 / 2).im = (xiZero q).im := by simp
          rw [h2]
          linarith
  set target : ℝ := Cτ / Real.sqrt (2 * Real.pi) + 2 * C₀ with htarget
  obtain ⟨ε, hε1, hbig⟩ := GaloisForLFunctions.HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg
    (w := zeroLightConeExponent τ) (c := zeroBohrAmplitude) (ε₀ := 1) zero_le_one
    (fun q q' h => by unfold zeroBohrAmplitude; rw [xiZero_eq_of_zeroLightConeExponent_eq h])
    (fun q _ => zeroBohrAmplitude_ne_zero q) hfin (m := fun q => ‖zeroBohrAmplitude q‖)
    (fun _ => norm_nonneg _) hAs
    (fun q hq ε hε => by
      rw [norm_mul, Complex.norm_exp]
      have hre : (-(ε : ℂ) * zeroLightConeExponent τ q).re =
          -(ε * (zeroLightConeExponent τ q).re) := by simp
      rw [hre]
      have hle : Real.exp (-(ε * (zeroLightConeExponent τ q).re)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith)
      nlinarith [norm_nonneg (zeroBohrAmplitude q)])
    (fun ε hε => hsum_le ε (by linarith) τ) ⟨q₀, hneg⟩ target
  have hε0 : 0 < ε := by linarith
  have h1 := hexp ε hε0 τ
  have h2 := hCτ ε hε1
  have htri := norm_sub_le
      (gaussianFilteredCentralGap ε τ + ((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
      ∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q))
    (gaussianFilteredCentralGap ε τ)
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at htri
  rw [hsqrt ε hε0.le] at htri h1
  have hspi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsε : 1 ≤ Real.sqrt ε := Real.one_le_sqrt.2 hε1
  have he : Real.exp (-2 * ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hpos : 0 < Real.sqrt (2 * Real.pi) * Real.sqrt ε := by positivity
  -- `√(2π)√ε · ‖Σ‖ ≤ Cτ √ε + C₀ (√(2π)√ε + 1)`
  have hkey : Real.sqrt (2 * Real.pi) * Real.sqrt ε *
      ‖∑' q : XiZeroCopy, zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤
      Cτ * Real.sqrt ε + C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left he hC₀]
  have hbig' : Real.sqrt (2 * Real.pi) * Real.sqrt ε * target <
      Real.sqrt (2 * Real.pi) * Real.sqrt ε *
      ‖∑' q : XiZeroCopy, zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ :=
    mul_lt_mul_of_pos_left hbig hpos
  have hexpand : Real.sqrt (2 * Real.pi) * Real.sqrt ε * target =
      Cτ * Real.sqrt ε + 2 * C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε) := by
    rw [htarget]; field_simp
  have hfin' : C₀ ≤ C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε) := by
    have : 1 ≤ Real.sqrt (2 * Real.pi) * Real.sqrt ε := by
      have h2pi : 1 ≤ Real.sqrt (2 * Real.pi) := by
        rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
      nlinarith
    nlinarith
  linarith

/-- The filtered central gap is `O(√ε)` at every large height. -/
def EventualFilteredCentralGapBudget : Prop :=
  ∃ T : ℝ, ∀ τ : ℝ, T ≤ |τ| →
    ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε → ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.sqrt ε

/-- **The large-height Gaussian central-gap budget is "finitely many off-line zeros".** -/
theorem eventualFilteredCentralGapBudget_iff_finiteOffLine :
    EventualFilteredCentralGapBudget ↔ BacklundConverse.FiniteOffLine := by
  constructor
  · rintro ⟨T, hT⟩
    by_contra hinf
    -- an off-line copy of large height
    have hO : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Infinite := hinf
    obtain ⟨q, hqO, hqB⟩ := (hO.sdiff (finite_xiZeroCopy_norm_le (2 * |T| + 3))).nonempty
    simp only [mem_setOf_eq, not_le] at hqO hqB
    have hspim := LindelofSparse.spectral_im_eq q
    have hspre := LindelofSparse.spectral_re_eq q
    have hb := re_xiZero_sub_half_bounds q
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    have hzq : xiZero q = (q.1 : ℂ) := rfl
    have hγ : 2 * |T| + 2 < |(q.1 : ℂ).im| := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
      rw [hspre, hspim] at h1
      have h2 : |1 / 2 - (q.1 : ℂ).re| < 1 / 2 := by
        rw [abs_lt]; rw [hzq] at hb; constructor <;> linarith
      linarith
    -- a copy right of the line at the same absolute height
    obtain ⟨q₀, hq₀re, hq₀im⟩ : ∃ q₀ : XiZeroCopy, 1 / 2 < (q₀.1 : ℂ).re ∧
        2 * |T| + 2 < |(q₀.1 : ℂ).im| := by
      rcases lt_or_gt_of_ne (show (q.1 : ℂ).re ≠ 1 / 2 by
          intro h; apply hqO; rw [hspim, h]; ring) with hlt | hgt
      · set q' := xiZeroCopyReflectEquiv.symm q with hq'
        have hsp : xiSpectralPoint q' = -xiSpectralPoint q := xiSpectralPoint_reflect_symm q
        have him' : (xiSpectralPoint q').im = -(xiSpectralPoint q).im := by rw [hsp, Complex.neg_im]
        have hre' : (xiSpectralPoint q').re = -(xiSpectralPoint q).re := by rw [hsp, Complex.neg_re]
        rw [LindelofSparse.spectral_im_eq, hspim] at him'
        rw [LindelofSparse.spectral_re_eq, hspre] at hre'
        refine ⟨q', by linarith, ?_⟩
        rw [hre', abs_neg]; exact hγ
      · exact ⟨q, hgt, hγ⟩
    set τ : ℝ := (q₀.1 : ℂ).im / 2 with hτ
    have hτT : T ≤ |τ| := by
      rw [hτ, abs_div, abs_two]
      have := le_abs_self T
      linarith
    have hneg : (zeroLightConeExponent τ q₀).re < 0 := by
      rw [re_zeroLightConeExponent]
      have hz0 : xiZero q₀ = (q₀.1 : ℂ) := rfl
      rw [hz0, hτ, sub_self]
      have hb0 : 0 < (q₀.1 : ℂ).re - 1 / 2 := by linarith
      nlinarith
    exact not_exists_filteredCentralGap_le_of_re_neg hneg (hT τ hτT)
  · intro hF
    obtain ⟨H, hH⟩ := (hF.image fun q => |(xiZero q).im|).bddAbove
    refine ⟨|H| + 2, fun τ hτ => exists_filteredCentralGap_le_of_re_nonneg fun q => ?_⟩
    rw [re_zeroLightConeExponent]
    have hb := re_xiZero_sub_half_bounds q
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    by_cases hq : (xiSpectralPoint q).im = 0
    · have hspim := LindelofSparse.spectral_im_eq q
      have hre : (xiZero q).re = 1 / 2 := by
        have : (q.1 : ℂ).re = 1 / 2 := by linarith
        exact this
      rw [hre]
      nlinarith [sq_nonneg ((xiZero q).im / 2 - τ)]
    · have hγH : |(xiZero q).im| ≤ H := hH ⟨q, hq, rfl⟩
      have hdist : 2 ≤ |(xiZero q).im / 2 - τ| := by
        have h1 := abs_sub_abs_le_abs_sub τ ((xiZero q).im / 2)
        rw [abs_sub_comm] at h1
        have h2 : |(xiZero q).im / 2| ≤ H / 2 := by rw [abs_div, abs_two]; linarith
        have h3 := le_abs_self H
        have h4 := abs_nonneg H
        linarith
      have hsq : 4 ≤ ((xiZero q).im / 2 - τ) ^ 2 := by
        have := sq_abs ((xiZero q).im / 2 - τ)
        nlinarith
      nlinarith

/-! ### Growth rates: the zeros-approach-the-line rung -/

/-- The zero copies with `Re w_ρ(τ) < 0` at a given height are finitely many. -/
theorem finite_setOf_re_zeroLightConeExponent_neg (τ : ℝ) :
    {q : XiZeroCopy | (zeroLightConeExponent τ q).re < 0}.Finite := by
  refine (finite_xiZeroCopy_norm_le (1 / 2 + (2 * |τ| + 4))).subset fun q hq => ?_
  simp only [mem_setOf_eq] at hq ⊢
  rw [re_zeroLightConeExponent] at hq
  have hb := re_xiZero_sub_half_bounds q
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
  have hγ : ((xiZero q).im / 2 - τ) ^ 2 < 4 := by nlinarith
  have hγ' : |(xiZero q).im / 2 - τ| < 2 := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (((xiZero q).im / 2 - τ) ^ 2) < Real.sqrt 4 :=
          Real.sqrt_lt_sqrt (sq_nonneg _) hγ
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have him : |(xiZero q).im| ≤ 2 * |τ| + 4 := by
    have := abs_sub_abs_le_abs_sub ((xiZero q).im / 2) τ
    rw [abs_div, abs_two] at this
    linarith
  rw [norm_xiSpectralPoint]
  calc ‖xiZero q - 1 / 2‖ ≤ |(xiZero q - 1 / 2).re| + |(xiZero q - 1 / 2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / 2 + (2 * |τ| + 4) := by
        have h1 : |(xiZero q - 1 / 2).re| ≤ 1 / 2 := by
          simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
          exact abs_le.2 ⟨by linarith, by linarith⟩
        have h2 : (xiZero q - 1 / 2).im = (xiZero q).im := by simp
        rw [h2]
        linarith

/-- **Light cone at rate `s`: the filtered gap is `O(e^{sε}√ε)`.** -/
theorem exists_filteredCentralGap_le_exp_of_re_ge {τ s : ℝ} (hs : 0 ≤ s)
    (h : ∀ q : XiZeroCopy, -s ≤ (zeroLightConeExponent τ q).re) :
    ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε →
      ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.exp (s * ε) * Real.sqrt ε := by
  obtain ⟨C₀, hC₀, hexp⟩ := exists_norm_filteredGap_add_zeroSeries_le
  have hAs : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := summable_norm_zeroBohrAmplitude
  set A : ℝ := ∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨C₀ * (Real.sqrt (2 * Real.pi) + 1) + Real.sqrt (2 * Real.pi) * A, fun ε hε => ?_⟩
  have hε0 : 0 < ε := by linarith
  have hs1 : 1 ≤ Real.sqrt ε := Real.one_le_sqrt.2 hε
  have hE1 : 1 ≤ Real.exp (s * ε) := Real.one_le_exp (by positivity)
  have hpt : ∀ q : XiZeroCopy, ‖zeroBohrAmplitude q *
      Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤
      ‖zeroBohrAmplitude q‖ * Real.exp (s * ε) := by
    intro q
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(ε : ℂ) * zeroLightConeExponent τ q).re =
        -(ε * (zeroLightConeExponent τ q).re) := by simp
    rw [hre]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    nlinarith [h q]
  have hsum : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q *
      Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hAs.mul_right _)
  have hZ : ‖∑' q : XiZeroCopy, zeroBohrAmplitude q *
      Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤ A * Real.exp (s * ε) := by
    refine (norm_tsum_le_tsum_norm hsum).trans ?_
    rw [hA, ← tsum_mul_right]
    exact Summable.tsum_le_tsum hpt hsum (hAs.mul_right _)
  have h1 := hexp ε hε0 τ
  have he : Real.exp (-2 * ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hsqrt : Real.sqrt (2 * Real.pi * ε) = Real.sqrt (2 * Real.pi) * Real.sqrt ε :=
    Real.sqrt_mul (by positivity) ε
  have htri := norm_sub_le (gaussianFilteredCentralGap ε τ +
      ((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
        ∑' q : XiZeroCopy, zeroBohrAmplitude q *
          Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q))
    (((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
      ∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q))
  rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at htri
  rw [hsqrt] at htri h1
  have hspi : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hsε : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hprod : Real.sqrt (2 * Real.pi) * Real.sqrt ε *
      ‖∑' q : XiZeroCopy, zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt ε * (A * Real.exp (s * ε)) := by gcongr
  have hE : 0 ≤ Real.exp (s * ε) := (Real.exp_pos _).le
  have hc1 : C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + Real.exp (-2 * ε)) ≤
      C₀ * (Real.sqrt (2 * Real.pi) + 1) * Real.exp (s * ε) * Real.sqrt ε := by
    have : Real.sqrt (2 * Real.pi) * Real.sqrt ε + Real.exp (-2 * ε) ≤
        (Real.sqrt (2 * Real.pi) + 1) * Real.exp (s * ε) * Real.sqrt ε := by
      nlinarith [mul_nonneg hspi hsε]
    calc C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + Real.exp (-2 * ε))
        ≤ C₀ * ((Real.sqrt (2 * Real.pi) + 1) * Real.exp (s * ε) * Real.sqrt ε) :=
          mul_le_mul_of_nonneg_left this hC₀
      _ = _ := by ring
  nlinarith

/-- **A zero deeper than the rate makes the filtered gap outgrow `C e^{sε}√ε`.** -/
theorem not_exists_filteredCentralGap_le_exp_of_re_lt {τ s : ℝ} (hs : 0 ≤ s) {q₀ : XiZeroCopy}
    (hneg : (zeroLightConeExponent τ q₀).re < -s) :
    ¬ ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε →
      ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.exp (s * ε) * Real.sqrt ε := by
  rintro ⟨Cτ, hCτ⟩
  obtain ⟨C₀, hC₀, hexp⟩ := exists_norm_filteredGap_add_zeroSeries_le
  have hAs : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := summable_norm_zeroBohrAmplitude
  set w : XiZeroCopy → ℂ := fun q => zeroLightConeExponent τ q + (s : ℂ) with hw
  have hwre : ∀ q, (w q).re = (zeroLightConeExponent τ q).re + s := fun q => by simp [hw]
  have hsum_le : ∀ ε : ℝ, 0 ≤ ε → Summable fun q : XiZeroCopy =>
      ‖zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * w q)‖ := by
    intro ε hε
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      (hAs.mul_right (Real.exp (ε * (1 + |s|))))
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(ε : ℂ) * w q).re = -(ε * (w q).re) := by simp
    rw [hre]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have h1 := neg_re_zeroLightConeExponent_le τ q
    rw [hwre]
    nlinarith [neg_abs_le s]
  set target : ℝ := Cτ / Real.sqrt (2 * Real.pi) + 2 * C₀ with htarget
  obtain ⟨ε, hε1, hbig⟩ := GaloisForLFunctions.HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg
    (w := w) (c := zeroBohrAmplitude) (ε₀ := 1) zero_le_one
    (fun q q' h => by
      unfold zeroBohrAmplitude
      rw [xiZero_eq_of_zeroLightConeExponent_eq (add_right_cancel h)])
    (fun q _ => zeroBohrAmplitude_ne_zero q)
    ((finite_setOf_re_zeroLightConeExponent_neg τ).subset fun q hq => by
      simp only [mem_setOf_eq] at hq ⊢
      rw [hwre] at hq
      linarith)
    (m := fun q => ‖zeroBohrAmplitude q‖) (fun _ => norm_nonneg _) hAs
    (fun q hq ε hε => by
      rw [norm_mul, Complex.norm_exp]
      have hre : (-(ε : ℂ) * w q).re = -(ε * (w q).re) := by simp
      rw [hre]
      have hle : Real.exp (-(ε * (w q).re)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith)
      nlinarith [norm_nonneg (zeroBohrAmplitude q)])
    (fun ε hε => hsum_le ε (by linarith)) ⟨q₀, by rw [hwre]; linarith⟩ target
  have hε0 : 0 < ε := by linarith
  -- the shifted series is `e^{-sε}` times the zero series
  have hshift : (∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * w q)) =
      ((Real.exp (-(s * ε)) : ℝ) : ℂ) *
        ∑' q : XiZeroCopy, zeroBohrAmplitude q *
          Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    simp only [hw]
    rw [Complex.ofReal_exp]
    rw [show -(ε : ℂ) * (zeroLightConeExponent τ q + (s : ℂ)) =
      -(ε : ℂ) * zeroLightConeExponent τ q + ((-(s * ε) : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_add]
    ring
  rw [hshift, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le] at hbig
  set Z := ‖∑' q : XiZeroCopy, zeroBohrAmplitude q *
      Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ with hZ
  have h1 := hexp ε hε0 τ
  have h2 := hCτ ε hε1
  have htri := norm_sub_le (gaussianFilteredCentralGap ε τ +
      ((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
        ∑' q : XiZeroCopy, zeroBohrAmplitude q *
          Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q))
    (gaussianFilteredCentralGap ε τ)
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at htri
  have hsqrt : Real.sqrt (2 * Real.pi * ε) = Real.sqrt (2 * Real.pi) * Real.sqrt ε :=
    Real.sqrt_mul (by positivity) ε
  rw [hsqrt] at htri h1
  rw [← hZ] at htri
  have hspi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsε : 1 ≤ Real.sqrt ε := Real.one_le_sqrt.2 hε1
  have he : Real.exp (-2 * ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hEm : 0 < Real.exp (-(s * ε)) := Real.exp_pos _
  have hEinv : Real.exp (-(s * ε)) * Real.exp (s * ε) = 1 := by
    rw [← Real.exp_add]; simp
  have hEm1 : Real.exp (-(s * ε)) ≤ 1 ∨ 1 < Real.exp (-(s * ε)) := le_or_gt _ 1
  have hpos : 0 < Real.sqrt (2 * Real.pi) * Real.sqrt ε := by positivity
  -- `√(2π)√ε Z ≤ Cτ e^{sε}√ε + C₀(√(2π)√ε + 1)`
  have hkey : Real.sqrt (2 * Real.pi) * Real.sqrt ε * Z ≤
      Cτ * Real.exp (s * ε) * Real.sqrt ε + C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left he hC₀]
  -- multiply by `e^{-sε}`
  have hkey' : Real.sqrt (2 * Real.pi) * Real.sqrt ε * (Real.exp (-(s * ε)) * Z) ≤
      Cτ * Real.sqrt ε +
        Real.exp (-(s * ε)) * (C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + 1)) := by
    have := mul_le_mul_of_nonneg_left hkey hEm.le
    calc Real.sqrt (2 * Real.pi) * Real.sqrt ε * (Real.exp (-(s * ε)) * Z)
        = Real.exp (-(s * ε)) * (Real.sqrt (2 * Real.pi) * Real.sqrt ε * Z) := by ring
      _ ≤ Real.exp (-(s * ε)) * (Cτ * Real.exp (s * ε) * Real.sqrt ε +
            C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + 1)) := this
      _ = Cτ * Real.sqrt ε * (Real.exp (-(s * ε)) * Real.exp (s * ε)) +
            Real.exp (-(s * ε)) * (C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + 1)) := by ring
      _ = _ := by rw [hEinv, mul_one]
  have hEle : Real.exp (-(s * ε)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hc1 : Real.exp (-(s * ε)) * (C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + 1)) ≤
      C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + 1) := by
    have : 0 ≤ C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + 1) := by positivity
    nlinarith
  have hbig' : Real.sqrt (2 * Real.pi) * Real.sqrt ε * target <
      Real.sqrt (2 * Real.pi) * Real.sqrt ε * (Real.exp (-(s * ε)) * Z) :=
    mul_lt_mul_of_pos_left hbig hpos
  have hexpand : Real.sqrt (2 * Real.pi) * Real.sqrt ε * target =
      Cτ * Real.sqrt ε + 2 * C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε) := by
    rw [htarget]; field_simp
  have hfin' : C₀ ≤ C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε) := by
    have : 1 ≤ Real.sqrt (2 * Real.pi) * Real.sqrt ε := by
      have h2pi : 1 ≤ Real.sqrt (2 * Real.pi) := by
        rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
      nlinarith
    nlinarith
  linarith

/-- The filtered central gap grows slower than every exponential `e^{sε}` at large heights. -/
def EventualFilteredCentralGapSubexponential : Prop :=
  ∀ s : ℝ, 0 < s → ∃ T : ℝ, ∀ τ : ℝ, T ≤ |τ| →
    ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε → ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.exp (s * ε) * Real.sqrt ε

/-- Reflection `ρ ↦ 1 − ρ` of a zero copy. -/
private theorem reflect_re_im (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv.symm q).1 : ℂ).re = 1 - (q.1 : ℂ).re ∧
      ((xiZeroCopyReflectEquiv.symm q).1 : ℂ).im = -(q.1 : ℂ).im := by
  have hsp : xiSpectralPoint (xiZeroCopyReflectEquiv.symm q) = -xiSpectralPoint q :=
    xiSpectralPoint_reflect_symm q
  have him : (xiSpectralPoint (xiZeroCopyReflectEquiv.symm q)).im = -(xiSpectralPoint q).im := by
    rw [hsp, Complex.neg_im]
  have hre : (xiSpectralPoint (xiZeroCopyReflectEquiv.symm q)).re = -(xiSpectralPoint q).re := by
    rw [hsp, Complex.neg_re]
  rw [LindelofSparse.spectral_im_eq, LindelofSparse.spectral_im_eq] at him
  rw [LindelofSparse.spectral_re_eq, LindelofSparse.spectral_re_eq] at hre
  exact ⟨by linarith, hre⟩

/-- **The large-height growth rate of the Gaussian central gap is "zeros approach the line".** -/
theorem eventualFilteredCentralGapSubexponential_iff_zerosApproachLine :
    EventualFilteredCentralGapSubexponential ↔ BacklundConverse.ZerosApproachLine := by
  constructor
  · intro hE h hh
    by_contra hinf
    have hD : (CosineDefectBudget.deepCopies h).Infinite := hinf
    set s : ℝ := h / 2 with hs
    obtain ⟨T, hT⟩ := hE s (by rw [hs]; linarith)
    obtain ⟨q, hqD, hqB⟩ := (hD.sdiff (finite_xiZeroCopy_norm_le (2 * |T| + 3))).nonempty
    simp only [mem_setOf_eq, not_le] at hqB
    have hqD' : h < (xiSpectralPoint q).im := hqD
    have hspim := LindelofSparse.spectral_im_eq q
    have hspre := LindelofSparse.spectral_re_eq q
    have hb := re_xiZero_sub_half_bounds q
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    have hzq : xiZero q = (q.1 : ℂ) := rfl
    rw [hzq] at hb
    have hγ : 2 * |T| + 2 < |(q.1 : ℂ).im| := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
      rw [hspre, hspim] at h1
      have h2 : |1 / 2 - (q.1 : ℂ).re| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
      linarith
    set q₀ := xiZeroCopyReflectEquiv.symm q with hq₀
    obtain ⟨hre₀, him₀⟩ := reflect_re_im q
    rw [← hq₀] at hre₀ him₀
    set τ : ℝ := (q₀.1 : ℂ).im / 2 with hτ
    have hτT : T ≤ |τ| := by
      rw [hτ, abs_div, abs_two, him₀, abs_neg]
      have := le_abs_self T
      linarith
    have hneg : (zeroLightConeExponent τ q₀).re < -s := by
      rw [re_zeroLightConeExponent]
      have hz0 : xiZero q₀ = (q₀.1 : ℂ) := rfl
      rw [hz0, hτ, sub_self, hre₀]
      have hb0 : h < 1 / 2 - (q.1 : ℂ).re := by rw [← hspim]; exact hqD'
      rw [hs]
      nlinarith
    exact not_exists_filteredCentralGap_le_exp_of_re_lt (by rw [hs]; linarith) hneg (hT τ hτT)
  · intro hZ s hs
    set h : ℝ := min (s / 2) (1 / 4) with hh
    have hh0 : 0 < h := lt_min (by linarith) (by norm_num)
    have hhs : h ≤ s / 2 := min_le_left _ _
    have hh4 : h ≤ 1 / 4 := min_le_right _ _
    have hD := hZ h hh0
    set E : Set XiZeroCopy := {q | h < |(xiSpectralPoint q).im|} with hE
    have hEfin : E.Finite := by
      refine (hD.union (hD.preimage xiZeroCopyReflectEquiv.symm.injective.injOn)).subset
        fun q hq => ?_
      simp only [hE, mem_setOf_eq] at hq
      rcases lt_abs.mp hq with h1 | h1
      · exact Or.inl h1
      · right
        show h < (xiSpectralPoint (xiZeroCopyReflectEquiv.symm q)).im
        rw [xiSpectralPoint_reflect_symm, Complex.neg_im]
        linarith
    obtain ⟨H, hH⟩ := (hEfin.image fun q => |(xiZero q).im|).bddAbove
    refine ⟨|H| + 2, fun τ hτ => exists_filteredCentralGap_le_exp_of_re_ge hs.le fun q => ?_⟩
    rw [re_zeroLightConeExponent]
    have hb := re_xiZero_sub_half_bounds q
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    have hspim := LindelofSparse.spectral_im_eq q
    by_cases hq : q ∈ E
    · have hγH : |(xiZero q).im| ≤ H := hH ⟨q, hq, rfl⟩
      have hdist : 2 ≤ |(xiZero q).im / 2 - τ| := by
        have h1 := abs_sub_abs_le_abs_sub τ ((xiZero q).im / 2)
        rw [abs_sub_comm] at h1
        have h2 : |(xiZero q).im / 2| ≤ H / 2 := by rw [abs_div, abs_two]; linarith
        have h3 := le_abs_self H
        have h4 := abs_nonneg H
        linarith
      have hsq : 4 ≤ ((xiZero q).im / 2 - τ) ^ 2 := by
        have := sq_abs ((xiZero q).im / 2 - τ)
        nlinarith
      nlinarith
    · simp only [hE, mem_setOf_eq, not_lt] at hq
      have hzq : xiZero q = (q.1 : ℂ) := rfl
      have hbabs : |(xiZero q).re - 1 / 2| ≤ h := by
        rw [hzq]
        rw [hspim] at hq
        rw [abs_sub_comm] at hq
        exact hq
      have hb2 : ((xiZero q).re - 1 / 2) ^ 2 ≤ h ^ 2 := by
        have := sq_abs ((xiZero q).re - 1 / 2)
        nlinarith [abs_nonneg ((xiZero q).re - 1 / 2)]
      have hbl : (xiZero q).re - 1 / 2 ≤ h := (abs_le.mp hbabs).2
      nlinarith [sq_nonneg ((xiZero q).im / 2 - τ)]

/-! ### The exact large-height growth rate -/

/-- The filtered central gap is `O(e^{sε}√ε)` at every large height. -/
def EventualFilteredCentralGapRate (s : ℝ) : Prop :=
  ∃ T : ℝ, ∀ τ : ℝ, T ≤ |τ| →
    ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε → ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.exp (s * ε) * Real.sqrt ε

/-- **The large-height growth rate law.**  For `s ≥ 0` the filtered central gap is `O(e^{sε}√ε)` at
every large height iff only finitely many zeros have `b + b²/8 > s`, where `b = Re ρ − ½`. -/
theorem eventualFilteredCentralGapRate_iff {s : ℝ} (hs : 0 ≤ s) :
    EventualFilteredCentralGapRate s ↔
      {q : XiZeroCopy | s < ((xiZero q).re - 1 / 2) + ((xiZero q).re - 1 / 2) ^ 2 / 8}.Finite := by
  constructor
  · rintro ⟨T, hT⟩
    by_contra hinf
    obtain ⟨q, hqE, hqB⟩ := (Set.Infinite.sdiff hinf
      (finite_xiZeroCopy_norm_le (2 * |T| + 3))).nonempty
    simp only [mem_setOf_eq, not_le] at hqE hqB
    have hspim := LindelofSparse.spectral_im_eq q
    have hspre := LindelofSparse.spectral_re_eq q
    have hb := re_xiZero_sub_half_bounds q
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    have hzq : xiZero q = (q.1 : ℂ) := rfl
    have hγ : 2 * |T| + 2 < |(q.1 : ℂ).im| := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
      rw [hspre, hspim] at h1
      have h2 : |1 / 2 - (q.1 : ℂ).re| < 1 / 2 := by
        rw [abs_lt]; rw [hzq] at hb; constructor <;> linarith
      linarith
    set τ : ℝ := (q.1 : ℂ).im / 2 with hτ
    have hτT : T ≤ |τ| := by
      rw [hτ, abs_div, abs_two]
      have := le_abs_self T
      linarith
    have hneg : (zeroLightConeExponent τ q).re < -s := by
      rw [re_zeroLightConeExponent, hzq, hτ, sub_self]
      rw [hzq] at hqE
      nlinarith
    exact not_exists_filteredCentralGap_le_exp_of_re_lt hs hneg (hT τ hτT)
  · intro hF
    set E : Set XiZeroCopy :=
      {q | s < ((xiZero q).re - 1 / 2) + ((xiZero q).re - 1 / 2) ^ 2 / 8} with hE
    obtain ⟨H, hH⟩ := (hF.image fun q => |(xiZero q).im|).bddAbove
    refine ⟨|H| + 2, fun τ hτ => exists_filteredCentralGap_le_exp_of_re_ge hs fun q => ?_⟩
    rw [re_zeroLightConeExponent]
    have hb := re_xiZero_sub_half_bounds q
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    by_cases hq : q ∈ E
    · have hγH : |(xiZero q).im| ≤ H := hH ⟨q, hq, rfl⟩
      have hdist : 2 ≤ |(xiZero q).im / 2 - τ| := by
        have h1 := abs_sub_abs_le_abs_sub τ ((xiZero q).im / 2)
        rw [abs_sub_comm] at h1
        have h2 : |(xiZero q).im / 2| ≤ H / 2 := by rw [abs_div, abs_two]; linarith
        have h3 := le_abs_self H
        have h4 := abs_nonneg H
        linarith
      have hsq : 4 ≤ ((xiZero q).im / 2 - τ) ^ 2 := by
        have := sq_abs ((xiZero q).im / 2 - τ)
        nlinarith
      nlinarith
    · simp only [hE, mem_setOf_eq, not_lt] at hq
      nlinarith [sq_nonneg ((xiZero q).im / 2 - τ)]

/-- **The growth rate reads the asymptotic abscissa.**  For `h ≥ 0` the filtered central gap is
`O(e^{(h + h²/8)ε}√ε)` at every large height iff only finitely many zeros have `Re ρ > ½ + h`. -/
theorem eventualFilteredCentralGapRate_iff_finite_re_gt {h : ℝ} (hh : 0 ≤ h) :
    EventualFilteredCentralGapRate (h + h ^ 2 / 8) ↔
      {q : XiZeroCopy | 1 / 2 + h < (xiZero q).re}.Finite := by
  rw [eventualFilteredCentralGapRate_iff (by positivity)]
  have hset : {q : XiZeroCopy |
      h + h ^ 2 / 8 < ((xiZero q).re - 1 / 2) + ((xiZero q).re - 1 / 2) ^ 2 / 8} =
      {q : XiZeroCopy | 1 / 2 + h < (xiZero q).re} := by
    ext q
    simp only [mem_setOf_eq]
    have hb := re_xiZero_sub_half_bounds q
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    constructor
    · intro h1
      by_contra h2
      push Not at h2
      nlinarith
    · intro h1
      nlinarith
  rw [hset]

/-! ### The all-height growth rate -/

/-- The filtered central gap is `O(e^{sε}√ε)` at every height. -/
def FilteredCentralGapRate (s : ℝ) : Prop :=
  ∀ τ : ℝ, ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε →
    ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.exp (s * ε) * Real.sqrt ε

/-- **The all-height growth rate law.**  For `s ≥ 0` the filtered central gap is `O(e^{sε}√ε)` at
every height iff every zero has `b + b²/8 ≤ s`, where `b = Re ρ − ½`. -/
theorem filteredCentralGapRate_iff {s : ℝ} (hs : 0 ≤ s) :
    FilteredCentralGapRate s ↔
      ∀ q : XiZeroCopy, ((xiZero q).re - 1 / 2) + ((xiZero q).re - 1 / 2) ^ 2 / 8 ≤ s := by
  constructor
  · intro hR q
    by_contra hlt
    push Not at hlt
    have hneg : (zeroLightConeExponent ((xiZero q).im / 2) q).re < -s := by
      rw [re_zeroLightConeExponent, sub_self]
      nlinarith
    exact not_exists_filteredCentralGap_le_exp_of_re_lt hs hneg (hR _)
  · intro h τ
    refine exists_filteredCentralGap_le_exp_of_re_ge hs fun q => ?_
    rw [re_zeroLightConeExponent]
    nlinarith [h q, sq_nonneg ((xiZero q).im / 2 - τ)]

/-- **The all-height rate reads the abscissa.**  For `h ≥ 0` the filtered central gap is
`O(e^{(h + h²/8)ε}√ε)` at every height iff every zero has `Re ρ ≤ ½ + h`. -/
theorem filteredCentralGapRate_iff_re_le {h : ℝ} (hh : 0 ≤ h) :
    FilteredCentralGapRate (h + h ^ 2 / 8) ↔ ∀ q : XiZeroCopy, (xiZero q).re ≤ 1 / 2 + h := by
  rw [filteredCentralGapRate_iff (by positivity)]
  refine forall_congr' fun q => ?_
  have hb := re_xiZero_sub_half_bounds q
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
  constructor
  · intro h1
    by_contra h2
    push Not at h2
    nlinarith
  · intro h1
    nlinarith

/-- **Unconditional rate.**  The filtered central gap is `O(e^{(17/32)ε}√ε)` at every height,
because every zero has `Re ρ < 1`. -/
theorem filteredCentralGapRate_seventeen_thirtySeconds : FilteredCentralGapRate (17 / 32) := by
  rw [filteredCentralGapRate_iff (by norm_num)]
  intro q
  have hb := re_xiZero_sub_half_bounds q
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
  nlinarith

end

end RHTower
