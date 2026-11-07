import GaloisForLFunctions.ThetaCuspSections.FourthTraceZeroGap

/-!
# A resolvent envelope inside the source-paid zero gap

The fourth reciprocal trace excludes the closed radius-twelve disk.
The complete reciprocal-square mass then bounds the logarithmic derivative
throughout that disk, retaining the exact distance to its boundary.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections
open _root_.RHTower ExplicitCollar

theorem twelve_lt_norm_xiSpectralPoint (q : XiZeroCopy) : 12 < ‖xiSpectralPoint q‖ := by
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have hh := abs_re_le_norm (xiSpectralPoint q)
  rw [hre] at hh
  exact (xiZeroCopy_twelve_lt_abs_im q).trans_le hh

/-- The complete Xi divisor misses the closed radius-twelve disk. -/
theorem XiC_ne_zero_of_norm_le_twelve {z : ℂ} (hz : ‖z‖ ≤ 12) : XiC z ≠ 0 := by
  intro hzero
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hzero
  have hh := twelve_lt_norm_xiSpectralPoint q
  rw [hq] at hh
  exact (not_lt_of_ge hz) hh

private theorem norm_reciprocalSquare_le (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ ≤ 1 / 144 := by
  have hn := twelve_lt_norm_xiSpectralPoint q
  have hs : (144 : ℝ) ≤ ‖xiSpectralPoint q‖ ^ 2 := by nlinarith only [hn]
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, inv_pow, one_div]
  exact inv_anti₀ (by norm_num) hs

/-- The complete reciprocal-square mass, including every off-line zero, is below `1/18`. -/
theorem tsum_norm_reciprocalSquare_le_one_over_eighteen :
    ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ 1 / 18 := by
  have he (q : XiZeroCopy) : ‖xiZeroCopyReciprocalSquare q‖ =
      1 / ‖xiSpectralPoint q‖ ^ 2 := by
    rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, inv_pow, one_div]
  simp_rw [he]
  have hh := WeilDeletion.tsum_inv_normSq_spectralPoint_le
  have hp := poleSharpConstant_le
  linarith only [hh, hp]

/-- The actual logarithmic derivative has a source-paid envelope inside radius twelve. -/
theorem norm_logDeriv_XiC_le_twelve {z : ℂ} (hz : ‖z‖ < 12) :
    ‖logDeriv XiC z‖ ≤ ‖z‖ / (18 * (1 - ‖z‖ ^ 2 / 144)) := by
  have hne := XiC_ne_zero_of_norm_le_twelve hz.le
  have hw : 0 < 1 - ‖z‖ ^ 2 / 144 := by nlinarith only [hz, norm_nonneg z]
  have hterm (q : XiZeroCopy) :
      ‖xiReciprocalSquareResolventTerm z q‖ ≤
        ‖xiZeroCopyReciprocalSquare q‖ / (1 - ‖z‖ ^ 2 / 144) := by
    have hc := mul_le_mul_of_nonneg_left (norm_reciprocalSquare_le q) (sq_nonneg ‖z‖)
    have hd : 1 - ‖z‖ ^ 2 / 144 ≤ ‖1 - z ^ 2 * xiZeroCopyReciprocalSquare q‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) (z ^ 2 * xiZeroCopyReciprocalSquare q)
      rw [norm_one, norm_mul, norm_pow] at hh
      linarith only [hh, hc]
    rw [xiReciprocalSquareResolventTerm, norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hw hd
  have hs := summable_xiReciprocalSquareResolventTerm hne
  have hc := summable_xiZeroCopyReciprocalSquare.norm
  have hsum : ‖∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm z q‖ ≤
      (1 / 18) / (1 - ‖z‖ ^ 2 / 144) := by
    calc
      _ ≤ ∑' q : XiZeroCopy, ‖xiReciprocalSquareResolventTerm z q‖ := norm_tsum_le_tsum_norm hs.norm
      _ ≤ ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ / (1 - ‖z‖ ^ 2 / 144) :=
        hs.norm.tsum_le_tsum hterm (hc.div_const _)
      _ = (∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖) / (1 - ‖z‖ ^ 2 / 144) :=
        tsum_div_const
      _ ≤ _ := div_le_div_of_nonneg_right tsum_norm_reciprocalSquare_le_one_over_eighteen hw.le
  rw [logDeriv_XiC_eq_relativeResolventTrace hne,
    xiRelativeResolventTrace_eq_reciprocalSquareResolvent hne, norm_mul, norm_neg]
  exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg z)).trans_eq (by
    field_simp [hw.ne'])

#print axioms XiC_ne_zero_of_norm_le_twelve
#print axioms tsum_norm_reciprocalSquare_le_one_over_eighteen
#print axioms norm_logDeriv_XiC_le_twelve

end GaloisForLFunctions.ThetaCuspSections
