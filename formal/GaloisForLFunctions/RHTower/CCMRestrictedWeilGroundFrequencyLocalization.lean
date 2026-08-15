import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundParity
import GaloisForLFunctions.RHTower.SuzukiGroundEnergyContinuity
import GaloisForLFunctions.RHTower.CCMArchimedeanLogWeightEquivalence
import GaloisForLFunctions.RHTower.PrimeMassSharpUpper

open MeasureTheory Set Filter
open scoped ENNReal InnerProduct Topology

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

theorem integrable_ccmFourierWeightDensity_ccmArchimedeanFormEmbedding
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    Integrable (ccmFourierWeightDensity ccmArchimedeanFourierWeight
      (ccmArchimedeanFormEmbedding a f)) := by
  have hfint : Integrable (fun xi : ℝ => ‖(f.1 : ℝ → ℂ) xi‖ ^ 2)
      ccmArchimedeanFormMeasure :=
    (MeasureTheory.Lp.memLp f.1).integrable_norm_pow (by norm_num)
  have hweighted : Integrable
      (fun xi : ℝ => Real.toNNReal (ccmArchimedeanFormWeight xi) •
        ‖(f.1 : ℝ → ℂ) xi‖ ^ 2) volume :=
    (integrable_withDensity_iff_integrable_smul
      measurable_ccmArchimedeanFormWeightNNReal).mp hfint
  refine hweighted.congr ?_
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn f.1] with xi hxi
  unfold ccmFourierWeightDensity
  rw [ccmArchimedeanFourierWeight_value_abs]
  change Real.toNNReal (ccmArchimedeanFormWeight xi) • ‖f.1 xi‖ ^ 2 =
    ccmArchimedeanFormWeight xi *
      ‖fourierUnitary (ccmArchimedeanFourierToTime f.1) xi‖ ^ 2
  rw [fourierUnitary_ccmArchimedeanFourierToTime, hxi,
    NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]

theorem ccmFourierWeightMoment_ccmArchimedeanFormEmbedding
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ccmFourierWeightMoment ccmArchimedeanFourierWeight
        (ccmArchimedeanFormEmbedding a f) = ‖f‖ ^ 2 := by
  unfold ccmFourierWeightMoment ccmFourierWeightDensity
  simp_rw [ccmArchimedeanFourierWeight_value_abs]
  change (∫ xi : ℝ, ccmArchimedeanFormWeight xi *
      ‖fourierUnitary (ccmArchimedeanFourierToTime f.1) xi‖ ^ 2) = ‖f‖ ^ 2
  rw [fourierUnitary_ccmArchimedeanFourierToTime]
  calc
    _ = ∫ xi : ℝ, ccmArchimedeanFormWeight xi * ‖(f.1 : ℝ → ℂ) xi‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ccmArchimedeanWeightedToL2_coeFn f.1] with xi hxi
      rw [hxi]
    _ = ‖f.1‖ ^ 2 := (norm_sq_ccmArchimedeanFourierL2 f.1).symm
    _ = ‖f‖ ^ 2 := rfl

theorem mul_norm_sq_sub_fourierCutoff_ccmArchimedeanFormEmbedding_le
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a)
    {A R : ℝ} (hR : 0 < R) (hAR : A < ccmArchimedeanFormWeight R) :
    A * ‖ccmArchimedeanFormEmbedding a f -
      fourierCutoff (centralInterval R) (measurableSet_centralInterval R)
        (ccmArchimedeanFormEmbedding a f)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [norm_sq_sub_fourierCutoff_central_eq_tailIntegral, ← integral_const_mul]
  have hplain : Integrable (fun xi : ℝ =>
      ‖(fourierUnitary (ccmArchimedeanFormEmbedding a f) : ℝ → ℂ) xi‖ ^ 2) :=
    (Lp.memLp (fourierUnitary (ccmArchimedeanFormEmbedding a f))).integrable_norm_pow
      (by norm_num)
  have hleft : Integrable (fun xi : ℝ =>
      A * (centralInterval R)ᶜ.indicator
        (fun eta : ℝ =>
          ‖(fourierUnitary (ccmArchimedeanFormEmbedding a f) : ℝ → ℂ) eta‖ ^ 2)
        xi) :=
    (hplain.indicator (measurableSet_centralInterval R).compl).const_mul A
  calc
    _ ≤ ccmFourierWeightMoment ccmArchimedeanFourierWeight
        (ccmArchimedeanFormEmbedding a f) := by
      refine integral_mono hleft
        (integrable_ccmFourierWeightDensity_ccmArchimedeanFormEmbedding a f) ?_
      intro xi
      change A * (centralInterval R)ᶜ.indicator
          (fun eta : ℝ =>
            ‖(fourierUnitary (ccmArchimedeanFormEmbedding a f) : ℝ → ℂ) eta‖ ^ 2)
          xi ≤ ccmFourierWeightDensity ccmArchimedeanFourierWeight
            (ccmArchimedeanFormEmbedding a f) xi
      by_cases hxi : xi ∈ (centralInterval R)ᶜ
      · rw [Set.indicator_of_mem hxi]
        unfold ccmFourierWeightDensity
        exact mul_le_mul_of_nonneg_right
          (le_ccmFourierWeight_of_mem_tail ccmArchimedeanFourierWeight hR
            (by simpa [ccmArchimedeanFourierWeight,
              ccmArchimedeanFormWeight, abs_of_pos hR] using hAR) hxi)
          (sq_nonneg _)
      · rw [Set.indicator_of_notMem hxi]
        simpa using ccmFourierWeightDensity_nonneg ccmArchimedeanFourierWeight
          (ccmArchimedeanFormEmbedding a f) xi
    _ = ‖f‖ ^ 2 := ccmFourierWeightMoment_ccmArchimedeanFormEmbedding a f

theorem norm_sq_ccmRestrictedWeilNormalizedGroundFormVector_le
    (a : SuzukiPositiveAperture) :
    ‖(ccmRestrictedWeilNormalizedGroundFormVector a).1‖ ^ 2 ≤
      max 0 (ccmRestrictedWeilGroundEnergy a +
        ‖ccmRestrictedWeilBoundedRemainder a‖) := by
  have hbound := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass
    a (ccmRestrictedWeilNormalizedGroundFormVector a)
  rw [ccmRestrictedWeilNormalizedGroundFormVector_source,
    norm_ccmRestrictedWeilNormalizedGroundFormVector_embedding] at hbound
  simp only [one_pow, mul_one] at hbound
  exact hbound.trans (le_max_right _ _)

/-- Exact complete-form budget of the normalized restricted-Weil ground. -/
def ccmRestrictedWeilGroundFormBudget (a : SuzukiPositiveAperture) : ℝ :=
  max 0 (ccmRestrictedWeilGroundEnergy a +
    ‖ccmRestrictedWeilBoundedRemainder a‖)

theorem ccmRestrictedWeilGroundFormBudget_nonneg (a : SuzukiPositiveAperture) :
    0 ≤ ccmRestrictedWeilGroundFormBudget a := by
  exact le_max_left _ _

/-- Weight level which forces Fourier-tail norm below `epsilon`. -/
def ccmRestrictedWeilGroundFrequencyLevel (a : SuzukiPositiveAperture)
    (epsilon : {x : ℝ // 0 < x}) : ℝ :=
  ccmRestrictedWeilGroundFormBudget a / epsilon.1 ^ 2 + 1

theorem ccmRestrictedWeilGroundFrequencyLevel_pos
    (a : SuzukiPositiveAperture) (epsilon : {x : ℝ // 0 < x}) :
    0 < ccmRestrictedWeilGroundFrequencyLevel a epsilon := by
  unfold ccmRestrictedWeilGroundFrequencyLevel
  have hepssq : 0 < epsilon.1 ^ 2 := sq_pos_of_pos epsilon.property
  have hbudget := ccmRestrictedWeilGroundFormBudget_nonneg a
  positivity

/-- Canonical exact Gamma-window radius for the normalized ground. -/
def ccmRestrictedWeilGroundFrequencyRadius (a : SuzukiPositiveAperture)
    (epsilon : {x : ℝ // 0 < x}) : ℝ :=
  Real.exp (ccmArchimedeanLogComparisonConstant *
    (ccmRestrictedWeilGroundFrequencyLevel a epsilon + 1))

theorem ccmRestrictedWeilGroundFrequencyRadius_pos
    (a : SuzukiPositiveAperture) (epsilon : {x : ℝ // 0 < x}) :
    0 < ccmRestrictedWeilGroundFrequencyRadius a epsilon := by
  exact Real.exp_pos _

theorem ccmRestrictedWeilGroundFrequencyLevel_lt_weight_radius
    (a : SuzukiPositiveAperture) (epsilon : {x : ℝ // 0 < x}) :
    ccmRestrictedWeilGroundFrequencyLevel a epsilon <
      ccmArchimedeanFormWeight
        (ccmRestrictedWeilGroundFrequencyRadius a epsilon) := by
  let A := ccmRestrictedWeilGroundFrequencyLevel a epsilon
  let C := ccmArchimedeanLogComparisonConstant
  let R := ccmRestrictedWeilGroundFrequencyRadius a epsilon
  have hA : 0 < A := ccmRestrictedWeilGroundFrequencyLevel_pos a epsilon
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one
    one_le_ccmArchimedeanLogComparisonConstant
  have hR : 0 < R := ccmRestrictedWeilGroundFrequencyRadius_pos a epsilon
  have hlogR : Real.log R = C * (A + 1) := by
    simp [R, ccmRestrictedWeilGroundFrequencyRadius, C, A]
  have hE : 0 < C * (A + 1) := mul_pos hC (by linarith)
  have hsuzuki : suzukiLogWeight R = 1 + C * (A + 1) := by
    rw [suzukiLogWeight, abs_of_pos hR, hlogR, max_eq_left hE.le]
  have hreverse := suzukiLogWeight_le_ccmArchimedeanComparison R
  rw [hsuzuki] at hreverse
  have hstrict : C * A < 1 + C * (A + 1) := by
    nlinarith
  have hscaled : C * A < C * ccmArchimedeanFormWeight R :=
    hstrict.trans_le hreverse
  by_contra hnot
  have hweight : ccmArchimedeanFormWeight R ≤ A := le_of_not_gt hnot
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left hweight hC.le)) hscaled

theorem ccmRestrictedWeilNormalizedGround_fourierTail_mul_le_budget
    (a : SuzukiPositiveAperture) (epsilon : {x : ℝ // 0 < x}) :
    ccmRestrictedWeilGroundFrequencyLevel a epsilon *
      ‖ccmArchimedeanFormEmbedding a
          (ccmRestrictedWeilNormalizedGroundFormVector a) -
        fourierCutoff
          (centralInterval (ccmRestrictedWeilGroundFrequencyRadius a epsilon))
          (measurableSet_centralInterval
            (ccmRestrictedWeilGroundFrequencyRadius a epsilon))
          (ccmArchimedeanFormEmbedding a
            (ccmRestrictedWeilNormalizedGroundFormVector a))‖ ^ 2 ≤
      ccmRestrictedWeilGroundFormBudget a := by
  exact (mul_norm_sq_sub_fourierCutoff_ccmArchimedeanFormEmbedding_le a
    (ccmRestrictedWeilNormalizedGroundFormVector a)
    (ccmRestrictedWeilGroundFrequencyRadius_pos a epsilon)
    (ccmRestrictedWeilGroundFrequencyLevel_lt_weight_radius a epsilon)).trans
      (norm_sq_ccmRestrictedWeilNormalizedGroundFormVector_le a)

/-- Every exact normalized restricted-Weil ground lies, up to tolerance `epsilon`, in the
canonical Gamma-frequency window.  No spectral-sign or RH hypothesis is used. -/
theorem ccmRestrictedWeilNormalizedGround_fourierTail_lt
    (a : SuzukiPositiveAperture) (epsilon : {x : ℝ // 0 < x}) :
    ‖ccmArchimedeanFormEmbedding a
          (ccmRestrictedWeilNormalizedGroundFormVector a) -
        fourierCutoff
          (centralInterval (ccmRestrictedWeilGroundFrequencyRadius a epsilon))
          (measurableSet_centralInterval
            (ccmRestrictedWeilGroundFrequencyRadius a epsilon))
          (ccmArchimedeanFormEmbedding a
            (ccmRestrictedWeilNormalizedGroundFormVector a))‖ < epsilon.1 := by
  let M := ccmRestrictedWeilGroundFormBudget a
  let A := ccmRestrictedWeilGroundFrequencyLevel a epsilon
  let n := ‖ccmArchimedeanFormEmbedding a
          (ccmRestrictedWeilNormalizedGroundFormVector a) -
        fourierCutoff
          (centralInterval (ccmRestrictedWeilGroundFrequencyRadius a epsilon))
          (measurableSet_centralInterval
            (ccmRestrictedWeilGroundFrequencyRadius a epsilon))
          (ccmArchimedeanFormEmbedding a
            (ccmRestrictedWeilNormalizedGroundFormVector a))‖
  have hmul : A * n ^ 2 ≤ M :=
    ccmRestrictedWeilNormalizedGround_fourierTail_mul_le_budget a epsilon
  have hM : 0 ≤ M := ccmRestrictedWeilGroundFormBudget_nonneg a
  have hA : 0 < A := ccmRestrictedWeilGroundFrequencyLevel_pos a epsilon
  have heps : 0 < epsilon.1 := epsilon.property
  have hepssq : 0 < epsilon.1 ^ 2 := sq_pos_of_pos heps
  have hAeps : A * epsilon.1 ^ 2 = M + epsilon.1 ^ 2 := by
    dsimp [A, M, ccmRestrictedWeilGroundFrequencyLevel]
    field_simp [ne_of_gt heps]
  by_contra hnlt
  have hen : epsilon.1 ≤ n := le_of_not_gt hnlt
  have hnnonneg : 0 ≤ n := norm_nonneg _
  have hsq : epsilon.1 ^ 2 ≤ n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hen) (add_nonneg hnnonneg heps.le)]
  have hscaled : A * epsilon.1 ^ 2 ≤ A * n ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hA.le
  have hcontr : M + epsilon.1 ^ 2 ≤ M := by
    rw [← hAeps]
    exact hscaled.trans hmul
  nlinarith

theorem norm_sq_ccmPolarApertureVector_le
    (a : SuzukiPositiveAperture) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    ‖ccmPolarApertureVector a s‖ ^ 2 ≤ 2 * a.1 * Real.exp a.1 := by
  change ‖ccmPolarL2Vector a s‖ ^ 2 ≤ _
  rw [norm_sq_eq_integral]
  have hrepr :
      (∫ x : ℝ, ‖(ccmPolarL2Vector a s : ℝ → ℂ) x‖ ^ 2) =
        ∫ x in centralInterval a.1, Real.exp (2 * s * x) := by
    rw [← integral_indicator (measurableSet_centralInterval a.1)]
    apply integral_congr_ae
    filter_upwards [ccmPolarL2Vector_coeFn a s] with x hx
    rw [hx]
    by_cases hxin : x ∈ centralInterval a.1
    · rw [Set.indicator_of_mem hxin, Set.indicator_of_mem hxin]
      simp only [ccmPolarProfile, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      rw [← Real.exp_nat_mul]
      apply congrArg Real.exp
      ring
    · rw [Set.indicator_of_notMem hxin, Set.indicator_of_notMem hxin]
      simp
  rw [hrepr]
  have hfun : IntegrableOn (fun x : ℝ => Real.exp (2 * s * x))
      (centralInterval a.1) := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hconst : IntegrableOn (fun _x : ℝ => Real.exp a.1)
      (centralInterval a.1) := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc continuousOn_const
  have hpoint : ∀ x ∈ centralInterval a.1,
      Real.exp (2 * s * x) ≤ Real.exp a.1 := by
    intro x hx
    apply Real.exp_le_exp.mpr
    have hxabs : |x| ≤ a.1 := abs_le.mpr hx
    calc
      2 * s * x ≤ |2 * s * x| := le_abs_self _
      _ = 2 * |s| * |x| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * (1 / 2) * a.1 := by gcongr
      _ = a.1 := by ring
  calc
    (∫ x in centralInterval a.1, Real.exp (2 * s * x)) ≤
        ∫ _x in centralInterval a.1, Real.exp a.1 :=
      setIntegral_mono_on hfun hconst (measurableSet_centralInterval a.1) hpoint
    _ = 2 * a.1 * Real.exp a.1 := by
      have haa : 0 ≤ a.1 + a.1 := by linarith [a.property]
      simp [centralInterval, max_eq_left haa]
      ring

theorem norm_logTranslationCLM_le_one (h : ℝ) :
    ‖logTranslationCLM h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖MellinL2.additiveTranslationUnitary h f‖ ≤ 1 * ‖f‖
  rw [(MellinL2.additiveTranslationUnitary h).norm_map, one_mul]

theorem norm_ccmSymmetricLogTranslation_le_two (h : ℝ) :
    ‖ccmSymmetricLogTranslation h‖ ≤ 2 := by
  unfold ccmSymmetricLogTranslation
  calc
    ‖logTranslationCLM h + logTranslationCLM (-h)‖ ≤
        ‖logTranslationCLM h‖ + ‖logTranslationCLM (-h)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_logTranslationCLM_le_one h)
      (norm_logTranslationCLM_le_one (-h))
    _ = 2 := by norm_num

theorem norm_ccmApertureCompression_le
    (a : SuzukiPositiveAperture) (A : SoninL2 →L[ℂ] SoninL2) :
    ‖ccmApertureCompression a A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro f
  change ‖(suzukiApertureHilbert a).subtypeL.adjoint (A f.1)‖ ≤ ‖A‖ * ‖f‖
  rw [(suzukiApertureHilbert a).adjoint_subtypeL]
  calc
    ‖(suzukiApertureHilbert a).orthogonalProjectionOnto (A f.1)‖ ≤
        ‖A f.1‖ :=
      (suzukiApertureHilbert a).norm_orthogonalProjectionOnto_apply_le (A f.1)
    _ ≤ ‖A‖ * ‖f.1‖ := A.le_opNorm f.1
    _ = ‖A‖ * ‖f‖ := rfl

theorem norm_ccmPrimeTransportOperator_le
    (a : SuzukiPositiveAperture) {n : ℕ} (hn : 1 ≤ n) :
    ‖ccmPrimeTransportOperator a n‖ ≤ 2 / Real.sqrt n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖((1 / Real.sqrt n : ℝ) : ℂ) •
      ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n)) f‖ ≤
    (2 / Real.sqrt n) * ‖f‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hsqrt)]
  have hcompression :
      ‖ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))‖ ≤ 2 :=
    (norm_ccmApertureCompression_le a _).trans
      (norm_ccmSymmetricLogTranslation_le_two _)
  calc
    (1 / Real.sqrt (n : ℝ)) *
        ‖ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n)) f‖ ≤
      (1 / Real.sqrt (n : ℝ)) *
        (‖ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        ((ccmApertureCompression a
          (ccmSymmetricLogTranslation (Real.log n))).le_opNorm f)
        (one_div_nonneg.mpr hsqrt.le)
    _ ≤ (1 / Real.sqrt (n : ℝ)) * (2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcompression (norm_nonneg f))
        (one_div_nonneg.mpr hsqrt.le)
    _ = (2 / Real.sqrt n) * ‖f‖ := by ring

theorem norm_smul_continuousLinearMap_le {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℂ) (T : E →L[ℂ] E) :
    ‖c • T‖ ≤ ‖c‖ * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg c) (norm_nonneg T))
  intro f
  change ‖c • T f‖ ≤ (‖c‖ * ‖T‖) * ‖f‖
  calc
    ‖c • T f‖ = ‖c‖ * ‖T f‖ := norm_smul c (T f)
    _ ≤ ‖c‖ * (‖T‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm f) (norm_nonneg c)
    _ = (‖c‖ * ‖T‖) * ‖f‖ := by ring

theorem norm_ccmPolarOperator_le (a : SuzukiPositiveAperture) :
    ‖ccmPolarOperator a‖ ≤ 4 * a.1 * Real.exp a.1 := by
  let xp := ‖ccmPolarApertureVector a (1 / 2)‖
  let xm := ‖ccmPolarApertureVector a (-1 / 2)‖
  let B := 2 * a.1 * Real.exp a.1
  have hp : xp ^ 2 ≤ B := by
    exact norm_sq_ccmPolarApertureVector_le a (by norm_num)
  have hm : xm ^ 2 ≤ B := by
    exact norm_sq_ccmPolarApertureVector_le a (by norm_num)
  have hxp : 0 ≤ xp := norm_nonneg _
  have hxm : 0 ≤ xm := norm_nonneg _
  have hprod : xp * xm ≤ B := by
    nlinarith [sq_nonneg (xp - xm)]
  unfold ccmPolarOperator
  calc
    ‖InnerProductSpace.rankOne ℂ (ccmPolarApertureVector a (1 / 2))
          (ccmPolarApertureVector a (-1 / 2)) +
        InnerProductSpace.rankOne ℂ (ccmPolarApertureVector a (-1 / 2))
          (ccmPolarApertureVector a (1 / 2))‖ ≤
      ‖InnerProductSpace.rankOne ℂ (ccmPolarApertureVector a (1 / 2))
          (ccmPolarApertureVector a (-1 / 2))‖ +
        ‖InnerProductSpace.rankOne ℂ (ccmPolarApertureVector a (-1 / 2))
          (ccmPolarApertureVector a (1 / 2))‖ := by
      exact norm_add_le
        (InnerProductSpace.rankOne ℂ (ccmPolarApertureVector a (1 / 2))
          (ccmPolarApertureVector a (-1 / 2)) :
            suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)
        (InnerProductSpace.rankOne ℂ (ccmPolarApertureVector a (-1 / 2))
          (ccmPolarApertureVector a (1 / 2)) :
            suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)
    _ = xp * xm + xm * xp := by
      rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne]
    _ ≤ 2 * B := by nlinarith
    _ = 4 * a.1 * Real.exp a.1 := by dsimp [B]; ring

theorem norm_ccmFinitePrimeOperator_le_primeMassHalf
    (a : SuzukiPositiveAperture) :
    ‖ccmFinitePrimeOperator a‖ ≤ 2 * primeMassHalf (Real.exp (2 * a.1)) := by
  classical
  let N := Nat.floor (Real.exp (2 * a.1))
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) •
          ccmPrimeTransportOperator a n‖ ≤
        2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1.trans' (by omega)
    have hvm := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    calc
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) •
          ccmPrimeTransportOperator a n‖ ≤
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ *
          ‖ccmPrimeTransportOperator a n‖ := by
        exact norm_smul_continuousLinearMap_le
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          (ccmPrimeTransportOperator a n :
            suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)
      _ = ArithmeticFunction.vonMangoldt n *
          ‖ccmPrimeTransportOperator a n‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hvm]
      _ ≤ ArithmeticFunction.vonMangoldt n * (2 / Real.sqrt n) :=
        mul_le_mul_of_nonneg_left (norm_ccmPrimeTransportOperator_le a hn1) hvm
      _ = 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by ring
  have hsubset : Finset.Icc 2 N ⊆ Finset.Icc 0 N := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  have hmass :
      (∑ n ∈ Finset.Icc 2 N,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n) ≤
        primeMassHalf (Real.exp (2 * a.1)) := by
    unfold primeMassHalf
    change (∑ n ∈ Finset.Icc 2 N,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n) ≤
      ∑ n ∈ Finset.Icc 0 N,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro n hn hnot
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
  unfold ccmFinitePrimeOperator
  change ‖∑ n ∈ Finset.Icc 2 N,
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) •
      ccmPrimeTransportOperator a n‖ ≤ _
  calc
    _ ≤ ∑ n ∈ Finset.Icc 2 N,
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) •
          ccmPrimeTransportOperator a n‖ := by
      exact norm_sum_le (Finset.Icc 2 N)
        (fun n => (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) •
          ccmPrimeTransportOperator a n :
            suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a))
    _ ≤ ∑ n ∈ Finset.Icc 2 N,
        2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) :=
      Finset.sum_le_sum hterm
    _ = 2 * ∑ n ∈ Finset.Icc 2 N,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n := by rw [Finset.mul_sum]
    _ ≤ 2 * primeMassHalf (Real.exp (2 * a.1)) :=
      mul_le_mul_of_nonneg_left hmass (by norm_num)

theorem norm_ccmFinitePrimeOperator_le_exp (a : SuzukiPositiveAperture) :
    ‖ccmFinitePrimeOperator a‖ ≤ 42 * Real.exp a.1 := by
  have hX : 1 ≤ Real.exp (2 * a.1) := by
    exact Real.one_le_exp (by linarith [a.property])
  have hmass := primeMassHalf_le_sqrt hX
  have hsqrt : Real.sqrt (Real.exp (2 * a.1)) = Real.exp a.1 := by
    rw [show Real.exp (2 * a.1) = Real.exp a.1 ^ 2 by
      rw [← Real.exp_nat_mul]; norm_num]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hsqrt] at hmass
  exact (norm_ccmFinitePrimeOperator_le_primeMassHalf a).trans (by nlinarith)

/-- Closed physical envelope for every bounded term in the exact restricted-Weil source. -/
def ccmRestrictedWeilRemainderEnvelope (a : SuzukiPositiveAperture) : ℝ :=
  |2 * gammaHardyPhaseRate 0 - 1| +
    4 * a.1 * Real.exp a.1 + 42 * Real.exp a.1

theorem ccmRestrictedWeilRemainderEnvelope_nonneg (a : SuzukiPositiveAperture) :
    0 ≤ ccmRestrictedWeilRemainderEnvelope a := by
  unfold ccmRestrictedWeilRemainderEnvelope
  have ha : 0 ≤ a.1 := a.property.le
  have hexp : 0 ≤ Real.exp a.1 := (Real.exp_pos _).le
  have hprod : 0 ≤ a.1 * Real.exp a.1 := mul_nonneg ha hexp
  nlinarith [abs_nonneg (2 * gammaHardyPhaseRate 0 - 1)]

theorem norm_ccmRestrictedWeilBoundedRemainder_le_envelope
    (a : SuzukiPositiveAperture) :
    ‖ccmRestrictedWeilBoundedRemainder a‖ ≤
      ccmRestrictedWeilRemainderEnvelope a := by
  let I : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a := 1
  let S : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
    ccmArchimedeanRemainderScalar • I
  have hS : ‖S‖ ≤ |2 * gammaHardyPhaseRate 0 - 1| := by
    calc
      ‖S‖ ≤ ‖ccmArchimedeanRemainderScalar‖ * ‖I‖ :=
        norm_smul_continuousLinearMap_le ccmArchimedeanRemainderScalar I
      _ = |2 * gammaHardyPhaseRate 0 - 1| := by
        simp only [I, norm_one, mul_one]
        unfold ccmArchimedeanRemainderScalar
        rw [Complex.norm_real, Real.norm_eq_abs]
  have hsum : ‖S + ccmPolarOperator a‖ ≤
      |2 * gammaHardyPhaseRate 0 - 1| + 4 * a.1 * Real.exp a.1 := by
    calc
      ‖S + ccmPolarOperator a‖ ≤ ‖S‖ + ‖ccmPolarOperator a‖ := by
        exact norm_add_le S (ccmPolarOperator a)
      _ ≤ |2 * gammaHardyPhaseRate 0 - 1| + 4 * a.1 * Real.exp a.1 :=
        add_le_add hS (norm_ccmPolarOperator_le a)
  change ‖S + ccmPolarOperator a - ccmFinitePrimeOperator a‖ ≤ _
  calc
    ‖S + ccmPolarOperator a - ccmFinitePrimeOperator a‖ ≤
        ‖S + ccmPolarOperator a‖ + ‖ccmFinitePrimeOperator a‖ := by
      exact norm_sub_le (S + ccmPolarOperator a) (ccmFinitePrimeOperator a)
    _ ≤ (|2 * gammaHardyPhaseRate 0 - 1| + 4 * a.1 * Real.exp a.1) +
        42 * Real.exp a.1 :=
      add_le_add hsum (norm_ccmFinitePrimeOperator_le_exp a)
    _ = ccmRestrictedWeilRemainderEnvelope a := by
      unfold ccmRestrictedWeilRemainderEnvelope
      ring

/-- Fully explicit prime--polar budget dominating the exact normalized ground form norm. -/
def ccmRestrictedWeilGroundEnvelopeBudget (a : SuzukiPositiveAperture) : ℝ :=
  max 0 (ccmRestrictedWeilGroundEnergy a + ccmRestrictedWeilRemainderEnvelope a)

theorem norm_sq_ccmRestrictedWeilNormalizedGroundFormVector_le_envelopeBudget
    (a : SuzukiPositiveAperture) :
    ‖(ccmRestrictedWeilNormalizedGroundFormVector a).1‖ ^ 2 ≤
      ccmRestrictedWeilGroundEnvelopeBudget a := by
  have hrem := norm_ccmRestrictedWeilBoundedRemainder_le_envelope a
  exact (norm_sq_ccmRestrictedWeilNormalizedGroundFormVector_le a).trans (by
    unfold ccmRestrictedWeilGroundEnvelopeBudget
    exact max_le_max_left 0 (add_le_add le_rfl hrem))

/-- Canonical weight level attached to any real quadratic budget. -/
def ccmArchimedeanBudgetFrequencyLevel (B : ℝ)
    (epsilon : {x : ℝ // 0 < x}) : ℝ :=
  max 0 B / epsilon.1 ^ 2 + 1

/-- Canonical Gamma radius attached to any real quadratic budget. -/
def ccmArchimedeanBudgetFrequencyRadius (B : ℝ)
    (epsilon : {x : ℝ // 0 < x}) : ℝ :=
  Real.exp (ccmArchimedeanLogComparisonConstant *
    (ccmArchimedeanBudgetFrequencyLevel B epsilon + 1))

theorem ccmArchimedeanBudgetFrequencyLevel_pos (B : ℝ)
    (epsilon : {x : ℝ // 0 < x}) :
    0 < ccmArchimedeanBudgetFrequencyLevel B epsilon := by
  unfold ccmArchimedeanBudgetFrequencyLevel
  have hepssq : 0 < epsilon.1 ^ 2 := sq_pos_of_pos epsilon.property
  have hbudget : 0 ≤ max 0 B := le_max_left _ _
  positivity

theorem ccmArchimedeanBudgetFrequencyRadius_pos (B : ℝ)
    (epsilon : {x : ℝ // 0 < x}) :
    0 < ccmArchimedeanBudgetFrequencyRadius B epsilon := by
  exact Real.exp_pos _

theorem ccmArchimedeanBudgetFrequencyLevel_lt_weight_radius (B : ℝ)
    (epsilon : {x : ℝ // 0 < x}) :
    ccmArchimedeanBudgetFrequencyLevel B epsilon <
      ccmArchimedeanFormWeight
        (ccmArchimedeanBudgetFrequencyRadius B epsilon) := by
  let A := ccmArchimedeanBudgetFrequencyLevel B epsilon
  let C := ccmArchimedeanLogComparisonConstant
  let R := ccmArchimedeanBudgetFrequencyRadius B epsilon
  have hA : 0 < A := ccmArchimedeanBudgetFrequencyLevel_pos B epsilon
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one
    one_le_ccmArchimedeanLogComparisonConstant
  have hR : 0 < R := ccmArchimedeanBudgetFrequencyRadius_pos B epsilon
  have hlogR : Real.log R = C * (A + 1) := by
    simp [R, ccmArchimedeanBudgetFrequencyRadius, C, A]
  have hE : 0 < C * (A + 1) := mul_pos hC (by linarith)
  have hsuzuki : suzukiLogWeight R = 1 + C * (A + 1) := by
    rw [suzukiLogWeight, abs_of_pos hR, hlogR, max_eq_left hE.le]
  have hreverse := suzukiLogWeight_le_ccmArchimedeanComparison R
  rw [hsuzuki] at hreverse
  have hstrict : C * A < 1 + C * (A + 1) := by nlinarith
  have hscaled : C * A < C * ccmArchimedeanFormWeight R :=
    hstrict.trans_le hreverse
  by_contra hnot
  have hweight : ccmArchimedeanFormWeight R ≤ A := le_of_not_gt hnot
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left hweight hC.le)) hscaled

theorem ccmArchimedeanFormEmbedding_fourierTail_lt_of_norm_sq_le_budget
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) (B : ℝ)
    (epsilon : {x : ℝ // 0 < x}) (hf : ‖f.1‖ ^ 2 ≤ max 0 B) :
    ‖ccmArchimedeanFormEmbedding a f -
        fourierCutoff
          (centralInterval (ccmArchimedeanBudgetFrequencyRadius B epsilon))
          (measurableSet_centralInterval
            (ccmArchimedeanBudgetFrequencyRadius B epsilon))
          (ccmArchimedeanFormEmbedding a f)‖ < epsilon.1 := by
  let M := max 0 B
  let A := ccmArchimedeanBudgetFrequencyLevel B epsilon
  let R := ccmArchimedeanBudgetFrequencyRadius B epsilon
  let n := ‖ccmArchimedeanFormEmbedding a f -
    fourierCutoff (centralInterval R) (measurableSet_centralInterval R)
      (ccmArchimedeanFormEmbedding a f)‖
  have hmul0 := mul_norm_sq_sub_fourierCutoff_ccmArchimedeanFormEmbedding_le
    a f (ccmArchimedeanBudgetFrequencyRadius_pos B epsilon)
      (ccmArchimedeanBudgetFrequencyLevel_lt_weight_radius B epsilon)
  have hmul : A * n ^ 2 ≤ M := hmul0.trans hf
  have hM : 0 ≤ M := le_max_left _ _
  have hA : 0 < A := ccmArchimedeanBudgetFrequencyLevel_pos B epsilon
  have heps : 0 < epsilon.1 := epsilon.property
  have hepssq : 0 < epsilon.1 ^ 2 := sq_pos_of_pos heps
  have hAeps : A * epsilon.1 ^ 2 = M + epsilon.1 ^ 2 := by
    dsimp [A, M, ccmArchimedeanBudgetFrequencyLevel]
    field_simp [ne_of_gt heps]
  by_contra hnlt
  have hen : epsilon.1 ≤ n := le_of_not_gt hnlt
  have hnnonneg : 0 ≤ n := norm_nonneg _
  have hsq : epsilon.1 ^ 2 ≤ n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hen) (add_nonneg hnnonneg heps.le)]
  have hscaled : A * epsilon.1 ^ 2 ≤ A * n ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hA.le
  have hcontr : M + epsilon.1 ^ 2 ≤ M := by
    rw [← hAeps]
    exact hscaled.trans hmul
  nlinarith

/-- Explicit physical Gamma window: only exact ground energy, the fixed archimedean scalar,
aperture, and `exp a` enter the radius. -/
def ccmRestrictedWeilGroundEnvelopeFrequencyRadius (a : SuzukiPositiveAperture)
    (epsilon : {x : ℝ // 0 < x}) : ℝ :=
  ccmArchimedeanBudgetFrequencyRadius
    (ccmRestrictedWeilGroundEnergy a + ccmRestrictedWeilRemainderEnvelope a) epsilon

theorem ccmRestrictedWeilNormalizedGround_fourierTail_lt_envelope
    (a : SuzukiPositiveAperture) (epsilon : {x : ℝ // 0 < x}) :
    ‖ccmArchimedeanFormEmbedding a
          (ccmRestrictedWeilNormalizedGroundFormVector a) -
        fourierCutoff
          (centralInterval
            (ccmRestrictedWeilGroundEnvelopeFrequencyRadius a epsilon))
          (measurableSet_centralInterval
            (ccmRestrictedWeilGroundEnvelopeFrequencyRadius a epsilon))
          (ccmArchimedeanFormEmbedding a
            (ccmRestrictedWeilNormalizedGroundFormVector a))‖ < epsilon.1 := by
  unfold ccmRestrictedWeilGroundEnvelopeFrequencyRadius
  exact ccmArchimedeanFormEmbedding_fourierTail_lt_of_norm_sq_le_budget a
    (ccmRestrictedWeilNormalizedGroundFormVector a)
    (ccmRestrictedWeilGroundEnergy a + ccmRestrictedWeilRemainderEnvelope a)
    epsilon (norm_sq_ccmRestrictedWeilNormalizedGroundFormVector_le_envelopeBudget a)

end RHTower
