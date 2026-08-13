import GaloisForLFunctions.RHTower.HedenmalmWardDefectTransverseGreenSource
import GaloisForLFunctions.RHTower.PrimeClockFiniteScaling
import GaloisForLFunctions.RHTower.XiWardFiveShiftWindowedKreinCharge

/-!
# Trace legality of the Ward--Green critical-feature current

P-G149 realizes the forced inverse-square transverse factor as the Green inverse of source Ward
energy.  This module proves that the resulting unbounded graph nevertheless has a legal trace on
every fixed real-centered critical-feature channel.

The key estimate is performed before summation: each reflection-pair exponential defect is
`4 sinh(k a)^2`, so `sinh(k a) / a` is uniformly bounded for `|a| ≤ 1/2` and `k ≤ 5`.  Dropping
the two negative five-shift legs gives an explicit finite scalar ceiling.  Critical-feature Cauchy
energy is square-summable on the Xi divisor, hence the Ward--Green current is an absolutely
summable nonnegative family.  Its trace vanishes exactly under RH because the critical feature
never misses a strip point.

This closes graph-domain and trace-classness.  Arithmetic evaluation of the resulting Hermitian
trace remains open.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Uniform divided-difference ceiling -/

lemma fiveShift_exp_pair_defect_eq_four_sinh_sq (x : ℝ) :
    Real.exp (2 * x) + Real.exp (-2 * x) - 2 =
      4 * Real.sinh x ^ 2 := by
  rw [Real.sinh_eq]
  have hmul : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [sq, ← Real.exp_add]; congr 1; ring,
    show Real.exp (-2 * x) = Real.exp (-x) ^ 2 by
      rw [sq, ← Real.exp_add]; congr 1; ring]
  field_simp
  nlinarith

/-- Uniform amplitude-level cancellation of the inverse-square transverse singularity. -/
lemma fiveShift_renormalized_exp_pair_defect_le
    {k a : ℝ} (hk0 : 0 ≤ k) (hk5 : k ≤ 5) (ha : |a| ≤ 1 / 2) :
    a⁻¹ ^ 2 *
        (Real.exp (2 * k * a) + Real.exp (-2 * k * a) - 2) ≤
      4 * k ^ 2 * Real.cosh (5 / 2) ^ 2 := by
  by_cases ha0 : a = 0
  · simp [ha0]
    positivity
  · have hka : |k * a| ≤ 5 / 2 := by
      rw [abs_mul, abs_of_nonneg hk0]
      calc
        k * |a| ≤ 5 * (1 / 2 : ℝ) :=
          mul_le_mul hk5 ha (abs_nonneg a) (by norm_num)
        _ = 5 / 2 := by ring
    have hsinh := abs_sinh_le_abs_mul_cosh (x := k * a)
      (C := 5 / 2) (by norm_num) hka
    have hsinhSq : Real.sinh (k * a) ^ 2 ≤
        (|k * a| * Real.cosh (5 / 2)) ^ 2 := by
      rw [← sq_abs (Real.sinh (k * a))]
      exact pow_le_pow_left₀ (abs_nonneg _) hsinh 2
    rw [show 2 * k * a = 2 * (k * a) by ring,
      show -2 * k * a = -2 * (k * a) by ring,
      fiveShift_exp_pair_defect_eq_four_sinh_sq]
    calc
      a⁻¹ ^ 2 * (4 * Real.sinh (k * a) ^ 2) ≤
          a⁻¹ ^ 2 * (4 * (|k * a| * Real.cosh (5 / 2)) ^ 2) := by
        gcongr
      _ = 4 * k ^ 2 * Real.cosh (5 / 2) ^ 2 := by
        rw [abs_mul, abs_of_nonneg hk0]
        rw [mul_pow, mul_pow, sq_abs]
        field_simp

/-- Explicit finite majorant for every source-normalized five-shift scalar defect at scale one. -/
def fiveShiftWardGreenUpperConstant : ℝ :=
  4 * Real.cosh (5 / 2) ^ 2 *
    (Real.exp (-(6 / 5 : ℝ)) * Real.exp (-2) *
        Real.exp (-(21 / 10 : ℝ)) * 1 ^ 2 +
      (Real.exp (-(6 / 5 : ℝ)) + Real.exp (-2) +
        Real.exp (-(21 / 10 : ℝ)) +
        Real.exp (-(6 / 5 : ℝ)) * Real.exp (-2) +
        Real.exp (-(6 / 5 : ℝ)) * Real.exp (-(21 / 10 : ℝ)) +
        Real.exp (-2) * Real.exp (-(21 / 10 : ℝ))) * 3 ^ 2 +
      5 ^ 2)

/-- Every inverse-square-normalized five-shift Krein defect is uniformly bounded.  The proof
drops the two negative legs and bounds the remaining `k=1,3,5` divided differences. -/
theorem fiveShiftEulerGammaRenormalizedKreinDefectCombination_one_le
    (q0 : XiZeroCopy) :
    fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q0 ≤
      fiveShiftWardGreenUpperConstant := by
  let A : ℝ := (q0.1 : ℂ).re - 1 / 2
  let w : ℝ := A⁻¹ ^ 2
  let c1 : ℝ := Real.exp (-(6 / 5 : ℝ)) * Real.exp (-2) *
    Real.exp (-(21 / 10 : ℝ))
  let c2 : ℝ := Real.exp (-(6 / 5 : ℝ)) * Real.exp (-2) +
    Real.exp (-(6 / 5 : ℝ)) * Real.exp (-(21 / 10 : ℝ)) +
    Real.exp (-2) * Real.exp (-(21 / 10 : ℝ)) +
    Real.exp (-(6 / 5 : ℝ)) * Real.exp (-2) * Real.exp (-(21 / 10 : ℝ))
  let c3 : ℝ := Real.exp (-(6 / 5 : ℝ)) + Real.exp (-2) +
    Real.exp (-(21 / 10 : ℝ)) +
    Real.exp (-(6 / 5 : ℝ)) * Real.exp (-2) +
    Real.exp (-(6 / 5 : ℝ)) * Real.exp (-(21 / 10 : ℝ)) +
    Real.exp (-2) * Real.exp (-(21 / 10 : ℝ))
  let c4 : ℝ := 1 + Real.exp (-(6 / 5 : ℝ)) + Real.exp (-2) +
    Real.exp (-(21 / 10 : ℝ))
  let D (k : ℝ) : ℝ :=
    ‖xiWeilPairDif (xiWeilPrimeTest (Real.exp k)) q0‖ ^ 2
  have hA : |A| ≤ 1 / 2 := by
    rw [abs_le]
    have hs := xi_divisor_support_re_mem_open_unit q0.1
    dsimp [A]
    constructor <;> linarith
  have hw : 0 ≤ w := sq_nonneg _
  have hc1 : 0 ≤ c1 := by dsimp [c1]; positivity
  have hc2 : 0 ≤ c2 := by dsimp [c2]; positivity
  have hc3 : 0 ≤ c3 := by dsimp [c3]; positivity
  have hc4 : 0 ≤ c4 := by dsimp [c4]; positivity
  have hD (k : ℝ) : 0 ≤ D k := sq_nonneg _
  have hbound (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 5) :
      w * D (k : ℝ) ≤ 4 * (k : ℝ) ^ 2 * Real.cosh (5 / 2) ^ 2 := by
    dsimp only [D]
    have heq := norm_sq_xiWeilPairDif_primeTest_exp (r := 1)
      (by norm_num) k hk1 q0
    norm_num only [mul_one] at heq
    rw [heq]
    dsimp only [w, A]
    exact fiveShift_renormalized_exp_pair_defect_le
      (by positivity) (by exact_mod_cast hk) hA
  have hdrop :
      w * (c1 * D 1 - c2 * D 2 + c3 * D 3 - c4 * D 4 + D 5) ≤
        c1 * (w * D 1) + c3 * (w * D 3) + w * D 5 := by
    have hneg2 : 0 ≤ c2 * D 2 := mul_nonneg hc2 (hD 2)
    have hneg4 : 0 ≤ c4 * D 4 := mul_nonneg hc4 (hD 4)
    nlinarith
  have htarget :
      w * (c1 * D 1 - c2 * D 2 + c3 * D 3 - c4 * D 4 + D 5) ≤
        fiveShiftWardGreenUpperConstant := by
    calc
      w * (c1 * D 1 - c2 * D 2 + c3 * D 3 - c4 * D 4 + D 5) ≤
          c1 * (w * D 1) + c3 * (w * D 3) + w * D 5 := hdrop
      _ ≤ c1 * (4 * (1 : ℝ) ^ 2 * Real.cosh (5 / 2) ^ 2) +
          c3 * (4 * (3 : ℝ) ^ 2 * Real.cosh (5 / 2) ^ 2) +
          4 * (5 : ℝ) ^ 2 * Real.cosh (5 / 2) ^ 2 := by
        have hb1 := mul_le_mul_of_nonneg_left
          (hbound 1 (by norm_num) (by norm_num)) hc1
        have hb3 := mul_le_mul_of_nonneg_left
          (hbound 3 (by norm_num) (by norm_num)) hc3
        have hb5 := hbound 5 (by norm_num) (by norm_num)
        linarith
      _ = fiveShiftWardGreenUpperConstant := by
        simp [fiveShiftWardGreenUpperConstant, c1, c3]
        ring
  rw [fiveShiftEulerGammaRenormalizedKreinDefectCombination,
    fiveShiftEulerGammaKreinDefectCombination]
  norm_num only [mul_one]
  simpa only [w, A, c1, c2, c3, c4, D] using htarget

/-! ## Fixed-feature trace -/

/-- Ward--Green current is the normalized Krein defect times critical-feature energy. -/
theorem fiveShiftCriticalFeatureWardGreenCurrent_eq_renormalizedKrein_mul
    (t : ℝ) (q : XiZeroCopy) :
    fiveShiftCriticalFeatureWardGreenCurrent t q =
      fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q *
        Complex.normSq
          (HedenmalmThetaSource.criticalEvaluation
            (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
            (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num))) := by
  rw [fiveShiftCriticalFeatureWardGreenCurrent_eq,
    fiveShiftCriticalFeaturePairedRenormalizedCurrent_eq,
    fiveShiftEulerGammaRenormalizedKreinDefectCombination_eq_pairedFeature
      (r := 1) (by norm_num)]
  rw [xiSpectralPoint_im_eq]
  ring

theorem fiveShiftEulerGammaRenormalizedKreinDefectCombination_one_nonneg
    (q : XiZeroCopy) :
    0 ≤ fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q := by
  rw [fiveShiftEulerGammaRenormalizedKreinDefectCombination_eq_pairedFeature
    (r := 1) (by norm_num)]
  let A : ℝ := (q.1 : ℂ).re - 1 / 2
  have hA : |A| ≤ 1 / 2 := by
    rw [abs_le]
    have hs := xi_divisor_support_re_mem_open_unit q.1
    dsimp [A]
    constructor <;> linarith
  change 0 ≤ fiveShiftEulerGammaPairedRenormalizedFeature 1 A
  by_cases hA0 : A = 0
  · rw [hA0, fiveShiftEulerGammaPairedRenormalizedFeature_zero]
  · rw [fiveShiftEulerGammaPairedRenormalizedFeature]
    exact mul_nonneg (sq_nonneg _)
      (fiveShiftEulerGammaPairedFeature_pos_of_ne_zero
        (by norm_num) hA0 hA).le

theorem fiveShiftCriticalFeatureWardGreenCurrent_nonneg
    (t : ℝ) (q : XiZeroCopy) :
    0 ≤ fiveShiftCriticalFeatureWardGreenCurrent t q := by
  rw [fiveShiftCriticalFeatureWardGreenCurrent_eq_renormalizedKrein_mul]
  exact mul_nonneg
    (fiveShiftEulerGammaRenormalizedKreinDefectCombination_one_nonneg q)
    (Complex.normSq_nonneg _)

theorem fiveShiftCriticalFeatureWardGreenCurrent_le
    (t : ℝ) (q : XiZeroCopy) :
    fiveShiftCriticalFeatureWardGreenCurrent t q ≤
      fiveShiftWardGreenUpperConstant *
        Complex.normSq
          (HedenmalmThetaSource.criticalEvaluation
            (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
            (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num))) := by
  rw [fiveShiftCriticalFeatureWardGreenCurrent_eq_renormalizedKrein_mul]
  exact mul_le_mul_of_nonneg_right
    (fiveShiftEulerGammaRenormalizedKreinDefectCombination_one_le q)
    (Complex.normSq_nonneg _)

/-- Real critical-feature Cauchy tests are square-summable on the multiplicity-exact Xi divisor. -/
theorem criticalFeatureCauchyKernelTest_squareSummable (t : ℝ) :
    XiWeilSquareSummable (criticalFeatureCauchyKernelTest t) := by
  exact
    ((XiWeilSquareSummable_cauchy (criticalHardyLowerPoint t : ℂ)).const_smul I).add
      ((XiWeilSquareSummable_cauchy (criticalHardyUpperPoint t : ℂ)).const_smul (-I))

/-- Every fixed critical-feature Ward--Green current is absolutely summable. -/
theorem fiveShiftCriticalFeatureWardGreenCurrent_summable (t : ℝ) :
    Summable (fiveShiftCriticalFeatureWardGreenCurrent t) := by
  have hF := criticalFeatureCauchyKernelTest_squareSummable t
  have hdom : Summable (fun q : XiZeroCopy =>
      fiveShiftWardGreenUpperConstant *
        Complex.normSq
          (HedenmalmThetaSource.criticalEvaluation
            (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
            (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num)))) := by
    rw [XiWeilSquareSummable] at hF
    apply (hF.mul_left fiveShiftWardGreenUpperConstant).congr
    intro q
    rw [Complex.normSq_eq_norm_sq]
    congr 2
    rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
    rfl
  exact Summable.of_nonneg_of_le
    (fiveShiftCriticalFeatureWardGreenCurrent_nonneg t)
    (fiveShiftCriticalFeatureWardGreenCurrent_le t) hdom

/-! ## Exact zero classifier -/

theorem fiveShiftEulerGammaRenormalizedKreinDefectCombination_one_eq_zero_iff
    (q : XiZeroCopy) :
    fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [fiveShiftEulerGammaRenormalizedKreinDefectCombination_eq_pairedFeature
    (r := 1) (by norm_num)]
  let A : ℝ := (q.1 : ℂ).re - 1 / 2
  have hA : |A| ≤ 1 / 2 := by
    rw [abs_le]
    have hs := xi_divisor_support_re_mem_open_unit q.1
    dsimp [A]
    constructor <;> linarith
  change fiveShiftEulerGammaPairedRenormalizedFeature 1 A = 0 ↔ _
  constructor
  · intro hzero
    by_contra hline
    have hA0 : A ≠ 0 := by
      dsimp [A]
      exact sub_ne_zero.mpr hline
    have hpos : 0 < fiveShiftEulerGammaPairedRenormalizedFeature 1 A := by
      rw [fiveShiftEulerGammaPairedRenormalizedFeature]
      exact mul_pos (sq_pos_of_ne_zero (inv_ne_zero hA0))
        (fiveShiftEulerGammaPairedFeature_pos_of_ne_zero
          (by norm_num) hA0 hA)
    exact hpos.ne' hzero
  · intro hline
    have hA0 : A = 0 := by dsimp [A]; linarith
    rw [hA0, fiveShiftEulerGammaPairedRenormalizedFeature_zero]

/-- One fixed critical feature sees zero Ward--Green current exactly on the critical line. -/
theorem fiveShiftCriticalFeatureWardGreenCurrent_eq_zero_iff_line
    (t : ℝ) (q : XiZeroCopy) :
    fiveShiftCriticalFeatureWardGreenCurrent t q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [fiveShiftCriticalFeatureWardGreenCurrent_eq_renormalizedKrein_mul,
    mul_eq_zero]
  have heval :
      Complex.normSq
          (HedenmalmThetaSource.criticalEvaluation
            (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
            (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num))) ≠ 0 := by
    exact (Complex.normSq_pos.mpr
      (criticalEvaluation_realCriticalFeature_ne_zero t
        (abs_xiSpectralPoint_im_lt_half q))).ne'
  simp only [heval, or_false]
  exact fiveShiftEulerGammaRenormalizedKreinDefectCombination_one_eq_zero_iff q

/-- Absolutely convergent Ward--Green trace in one fixed critical-feature channel. -/
def fiveShiftCriticalFeatureWardGreenTrace (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, fiveShiftCriticalFeatureWardGreenCurrent t q

/-- **Fixed-feature trace criterion.** Every real-centered Ward--Green trace vanishes exactly
under RH. -/
theorem fiveShiftCriticalFeatureWardGreenTrace_eq_zero_iff_rh (t : ℝ) :
    fiveShiftCriticalFeatureWardGreenTrace t = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
      intro q
      have hle := (fiveShiftCriticalFeatureWardGreenCurrent_summable t).le_tsum q
        (fun r _ => fiveShiftCriticalFeatureWardGreenCurrent_nonneg t r)
      have hsum :
          (∑' r : XiZeroCopy, fiveShiftCriticalFeatureWardGreenCurrent t r) = 0 := by
        simpa only [fiveShiftCriticalFeatureWardGreenTrace] using hzero
      have hq0 : fiveShiftCriticalFeatureWardGreenCurrent t q = 0 := by
        apply le_antisymm
        · simpa only [hsum] using hle
        · exact fiveShiftCriticalFeatureWardGreenCurrent_nonneg t q
      exact (fiveShiftCriticalFeatureWardGreenCurrent_eq_zero_iff_line t q).mp hq0
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline q]
  · intro hRH
    rw [fiveShiftCriticalFeatureWardGreenTrace]
    calc
      (∑' q : XiZeroCopy, fiveShiftCriticalFeatureWardGreenCurrent t q) =
          ∑' _q : XiZeroCopy, 0 := by
        apply tsum_congr
        intro q
        exact (fiveShiftCriticalFeatureWardGreenCurrent_eq_zero_iff_line t q).mpr
          (xi_divisor_support_re_eq_half_of_rh hRH q.1)
      _ = 0 := tsum_zero

end

end RHTower
