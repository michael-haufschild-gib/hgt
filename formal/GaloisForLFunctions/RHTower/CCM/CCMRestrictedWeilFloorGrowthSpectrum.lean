import GaloisForLFunctions.RHTower.CCM.CCMInwardRegularizationFloor
import GaloisForLFunctions.RHTower.NonnegativeMonotoneDirichletAbscissa

/-!
# Restricted-Weil floor growth spectrum

The inward regularization bridge transfers the exact rectangular transverse spectrum to the
actual negative restricted-Weil floor.  This file records the resulting sharp lower abscissa,
sampled and continuous logarithmic growth bounds, and the zero-power/zero-exponential-type RH
criteria.  It also specializes the generic monotone nonnegative Dirichlet-abscissa identity to
the spectral floor, including the zero sequence under RH.
-/

open Complex Filter Function Set LSeries
open scoped Topology ENNReal

namespace RHTower

noncomputable section

theorem restrictedWeilFloor_abscissa_lower_of_not_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis) {eta : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta) :
    (((1 + xiRightTransverseSup : ℝ) : EReal)) ≤
      LSeries.abscissaOfAbsConv (fun n => ((eta n : ℝ) : ℂ)) := by
  rw [← xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh hL hN hnot]
  calc
    LSeries.abscissaOfAbsConv
        (xiRectangularWeilTailNegativeDirichletCoefficient L N) ≤
        LSeries.abscissaOfAbsConv
          (fun n => ((((2 * L) * eta n : ℝ)) : ℂ)) := by
      apply abscissaOfAbsConv_le_of_nonnegative_domination
      · exact xiRectangularWeilTailNegativePart_nonneg L N
      · intro n
        exact mul_nonneg (by positivity) (henv.1 n)
      · exact henv.2
    _ ≤ LSeries.abscissaOfAbsConv (fun n => ((eta n : ℝ) : ℂ)) := by
      apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
      intro sigma hsigma
      have heta : LSeriesSummable (fun n => ((eta n : ℝ) : ℂ)) (sigma : ℂ) :=
        LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
          simpa only [ofReal_re] using hsigma)
      have hscaled := heta.smul (((2 * L : ℝ) : ℂ))
      simpa only [Pi.smul_apply, smul_eq_mul, ofReal_mul] using! hscaled

theorem inwardRestrictedWeilFloor_abscissa_lower_of_not_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis) {lambda : ℕ → ℝ}
    (hvariational : ∀ n : ℕ, ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      lambda n * inwardRegularizedTwoEdgeSquaredMass L epsilon ≤
        (xiWeilPolarization
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)).re) :
    (((1 + xiRightTransverseSup : ℝ) : EReal)) ≤
      LSeries.abscissaOfAbsConv
        (fun n => ((inwardRestrictedWeilNegativeFloor lambda n : ℝ) : ℂ)) := by
  exact restrictedWeilFloor_abscissa_lower_of_not_rh hL hN hnot
    (xiRestrictedWeilNegativeFloorEnvelope_of_inwardRegularization
      hL N lambda hvariational)

/-- A nonnegative sampled carrier has zero power type when every positive power eventually
dominates it up to a fixed constant. -/
def SubpowerAtNatInfinity (eta : ℕ → ℝ) : Prop :=
  ∀ alpha : ℝ, 0 < alpha → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ n : ℕ in atTop, eta n ≤ C * (n : ℝ) ^ alpha

theorem not_subpower_restrictedWeilFloor_of_false_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ} (hnot : ¬ RiemannHypothesis)
    {eta : ℕ → ℝ} (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta) :
    ¬ SubpowerAtNatInfinity eta := by
  intro hsubpower
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot
  let alpha : ℝ := xiRightTransverseSup / 2
  have halpha0 : 0 ≤ alpha := by
    dsimp only [alpha]
    linarith [xiRightTransverseSup_pos hne]
  have halphaPos : 0 < alpha := by
    dsimp only [alpha]
    linarith [xiRightTransverseSup_pos hne]
  have halphaSup : alpha < xiRightTransverseSup := by
    dsimp only [alpha]
    linarith [xiRightTransverseSup_pos hne]
  obtain ⟨C, hC, hupper⟩ := hsubpower alpha halphaPos
  rw [eventually_atTop] at hupper
  obtain ⟨N0, hN0⟩ := hupper
  obtain ⟨n, hn0, _hLn, hlower⟩ :=
    not_riemannHypothesis_implies_inwardRestrictedWeilFloor_cofinally_exceeds_power
      hL halpha0 hnot halphaSup henv C hC N0
  exact (not_lt_of_ge (hN0 n hn0)) hlower

theorem riemannHypothesis_iff_restrictedWeilFloor_subpower
    {L : ℝ} (hL : 0 < L) {N : ℕ} {eta : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta)
    (hzero : RiemannHypothesis → ∀ n, eta n = 0) :
    RiemannHypothesis ↔ SubpowerAtNatInfinity eta := by
  constructor
  · intro hRH alpha halpha
    refine ⟨0, le_rfl, ?_⟩
    filter_upwards with n
    rw [hzero hRH n]
    exact mul_nonneg le_rfl (Real.rpow_nonneg (Nat.cast_nonneg n) alpha)
  · intro hsubpower
    by_contra hnot
    exact not_subpower_restrictedWeilFloor_of_false_rh hL hnot henv hsubpower

theorem riemannHypothesis_iff_inwardRestrictedWeilFloor_subpower
    {L : ℝ} (hL : 0 < L) {N : ℕ} {lambda : ℕ → ℝ}
    (hvariational : ∀ n : ℕ, ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      lambda n * inwardRegularizedTwoEdgeSquaredMass L epsilon ≤
        (xiWeilPolarization
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)).re)
    (hpositive : RiemannHypothesis → ∀ n, 0 ≤ lambda n) :
    RiemannHypothesis ↔
      SubpowerAtNatInfinity (inwardRestrictedWeilNegativeFloor lambda) := by
  apply riemannHypothesis_iff_restrictedWeilFloor_subpower hL
    (xiRestrictedWeilNegativeFloorEnvelope_of_inwardRegularization
      hL N lambda hvariational)
  intro hRH n
  rw [inwardRestrictedWeilNegativeFloor, negPart_def,
    max_eq_right (neg_nonpos.mpr (hpositive hRH n))]

/-- Extended upper logarithmic power exponent of a sampled nonnegative carrier. -/
noncomputable def SampledUpperLogPowerExponent (eta : ℕ → ℝ) : ℝ≥0∞ :=
  limsup (fun n : ℕ => ENNReal.ofReal (Real.log (1 + eta n) / Real.log n)) atTop

theorem alpha_le_sampledUpperLogPowerExponent_of_false_rh
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hnot : ¬ RiemannHypothesis) (halpha : alpha < xiRightTransverseSup)
    {N : ℕ} {eta : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta) :
    ENNReal.ofReal alpha ≤ SampledUpperLogPowerExponent eta := by
  apply le_limsup_of_frequently_le'
  rw [frequently_atTop]
  intro N0
  obtain ⟨n, hn0, hLn, hlower⟩ :=
    not_riemannHypothesis_implies_inwardRestrictedWeilFloor_cofinally_exceeds_power
      hL halpha0 hnot halpha henv 1 (by positivity) N0
  refine ⟨n, hn0, ?_⟩
  have hlogn : 0 < Real.log n := by linarith
  have hn1 : (1 : ℝ) < n := (Real.log_pos_iff (Nat.cast_nonneg n)).mp hlogn
  have hnpos : (0 : ℝ) < n := lt_trans zero_lt_one hn1
  have heta0 : 0 ≤ eta n := henv.1 n
  have hpowlt : (n : ℝ) ^ alpha < 1 + eta n := by
    simpa only [one_mul] using hlower.trans (lt_add_of_pos_left _ zero_lt_one)
  have hloglt : Real.log ((n : ℝ) ^ alpha) < Real.log (1 + eta n) := by
    exact Real.strictMonoOn_log
      (Real.rpow_pos_of_pos hnpos alpha) (add_pos_of_pos_of_nonneg zero_lt_one heta0) hpowlt
  rw [Real.log_rpow hnpos] at hloglt
  apply ENNReal.ofReal_le_ofReal
  exact (le_div_iff₀ hlogn).mpr (le_of_lt (by simpa [mul_comm] using hloglt))

theorem transverseSup_le_sampledUpperLogPowerExponent_of_false_rh
    {L : ℝ} (hL : 0 < L) (hnot : ¬ RiemannHypothesis)
    {N : ℕ} {eta : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta) :
    ENNReal.ofReal xiRightTransverseSup ≤ SampledUpperLogPowerExponent eta := by
  by_cases htop : SampledUpperLogPowerExponent eta = ⊤
  · simp [htop]
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  by_contra hnotle
  have hexpLt : (SampledUpperLogPowerExponent eta).toReal < xiRightTransverseSup :=
    lt_of_not_ge hnotle
  let alpha : ℝ :=
    ((SampledUpperLogPowerExponent eta).toReal + xiRightTransverseSup) / 2
  have halpha0 : 0 ≤ alpha := by
    dsimp only [alpha]
    exact div_nonneg
      (add_nonneg ENNReal.toReal_nonneg xiRightTransverseSup_nonneg) (by norm_num)
  have halphaSup : alpha < xiRightTransverseSup := by
    dsimp only [alpha]
    linarith
  have hexpAlpha : (SampledUpperLogPowerExponent eta).toReal < alpha := by
    dsimp only [alpha]
    linarith
  have halpha := alpha_le_sampledUpperLogPowerExponent_of_false_rh
    hL halpha0 hnot halphaSup henv
  have halphaReal : alpha ≤ (SampledUpperLogPowerExponent eta).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal htop).mp halpha
  linarith

/-- Extended upper logarithmic exponent of a continuous aperture floor. -/
noncomputable def ApertureUpperLogGrowthExponent (eta : ℝ → ℝ) : ℝ≥0∞ :=
  limsup (fun a : ℝ => ENNReal.ofReal (Real.log (1 + eta a) / (2 * a))) atTop

theorem alpha_le_apertureUpperLogGrowthExponent_of_false_rh
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hnot : ¬ RiemannHypothesis) (halpha : alpha < xiRightTransverseSup)
    {N : ℕ} {eta : ℝ → ℝ}
    (heta0 : ∀ a, 0 ≤ eta a)
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (fun n => eta (Real.log n / 2))) :
    ENNReal.ofReal alpha ≤ ApertureUpperLogGrowthExponent eta := by
  apply le_limsup_of_frequently_le'
  rw [frequently_atTop]
  intro a0
  have hlog : Tendsto (fun n : ℕ => Real.log n / 2) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 2)
  have hsamples : ∀ᶠ n : ℕ in atTop, a0 ≤ Real.log n / 2 :=
    hlog.eventually_ge_atTop a0
  rw [eventually_atTop] at hsamples
  obtain ⟨N0, hN0⟩ := hsamples
  obtain ⟨n, hn0, hLn, hlower⟩ :=
    not_riemannHypothesis_implies_inwardRestrictedWeilFloor_cofinally_exceeds_power
      hL halpha0 hnot halpha henv 1 (by positivity) N0
  refine ⟨Real.log n / 2, hN0 n hn0, ?_⟩
  have hlogn : 0 < Real.log n := by linarith
  have hn1 : (1 : ℝ) < n := (Real.log_pos_iff (Nat.cast_nonneg n)).mp hlogn
  have hnpos : (0 : ℝ) < n := lt_trans zero_lt_one hn1
  have hpowlt : (n : ℝ) ^ alpha < 1 + eta (Real.log n / 2) := by
    simpa only [one_mul] using hlower.trans (lt_add_of_pos_left _ zero_lt_one)
  have hloglt : Real.log ((n : ℝ) ^ alpha) <
      Real.log (1 + eta (Real.log n / 2)) := by
    exact Real.strictMonoOn_log
      (Real.rpow_pos_of_pos hnpos alpha)
      (add_pos_of_pos_of_nonneg zero_lt_one (heta0 _)) hpowlt
  rw [Real.log_rpow hnpos] at hloglt
  apply ENNReal.ofReal_le_ofReal
  have hratio : alpha ≤
      Real.log (1 + eta (Real.log n / 2)) / Real.log n :=
    (le_div_iff₀ hlogn).mpr (le_of_lt (by simpa [mul_comm] using hloglt))
  have hdenominator : 2 * (Real.log n / 2) = Real.log n := by ring
  rw [hdenominator]
  exact hratio

theorem transverseSup_le_apertureUpperLogGrowthExponent_of_false_rh
    {L : ℝ} (hL : 0 < L) (hnot : ¬ RiemannHypothesis)
    {N : ℕ} {eta : ℝ → ℝ} (heta0 : ∀ a, 0 ≤ eta a)
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (fun n => eta (Real.log n / 2))) :
    ENNReal.ofReal xiRightTransverseSup ≤ ApertureUpperLogGrowthExponent eta := by
  by_cases htop : ApertureUpperLogGrowthExponent eta = ⊤
  · simp [htop]
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  by_contra hnotle
  have hexpLt : (ApertureUpperLogGrowthExponent eta).toReal < xiRightTransverseSup :=
    lt_of_not_ge hnotle
  let alpha : ℝ :=
    ((ApertureUpperLogGrowthExponent eta).toReal + xiRightTransverseSup) / 2
  have halpha0 : 0 ≤ alpha := by
    dsimp only [alpha]
    exact div_nonneg
      (add_nonneg ENNReal.toReal_nonneg xiRightTransverseSup_nonneg) (by norm_num)
  have halphaSup : alpha < xiRightTransverseSup := by
    dsimp only [alpha]
    linarith
  have hexpAlpha : (ApertureUpperLogGrowthExponent eta).toReal < alpha := by
    dsimp only [alpha]
    linarith
  have halpha := alpha_le_apertureUpperLogGrowthExponent_of_false_rh
    hL halpha0 hnot halphaSup heta0 henv
  have halphaReal : alpha ≤ (ApertureUpperLogGrowthExponent eta).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal htop).mp halpha
  linarith

theorem riemannHypothesis_iff_apertureUpperLogGrowthExponent_eq_zero
    {L : ℝ} (hL : 0 < L) {N : ℕ} {eta : ℝ → ℝ}
    (heta0 : ∀ a, 0 ≤ eta a)
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (fun n => eta (Real.log n / 2)))
    (hzero : RiemannHypothesis → ∀ a, eta a = 0) :
    RiemannHypothesis ↔ ApertureUpperLogGrowthExponent eta = 0 := by
  constructor
  · intro hRH
    simp [ApertureUpperLogGrowthExponent, hzero hRH]
  · intro hexponent
    by_contra hnot
    have hne : Nonempty XiRightZeroCopy :=
      nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot
    have hlower := transverseSup_le_apertureUpperLogGrowthExponent_of_false_rh
      hL hnot heta0 henv
    rw [hexponent] at hlower
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (xiRightTransverseSup_pos hne))) hlower

/-- Zero exponential type for a continuous aperture carrier. -/
def SubexponentialAtApertureInfinity (eta : ℝ → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ a : ℝ in atTop, eta a ≤ C * Real.exp (epsilon * a)

theorem not_aperture_subexponential_of_false_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ} (hnot : ¬ RiemannHypothesis)
    {eta : ℝ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (fun n => eta (Real.log n / 2))) :
    ¬ SubexponentialAtApertureInfinity eta := by
  intro hsubexponential
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot
  let alpha : ℝ := xiRightTransverseSup / 2
  have halpha0 : 0 ≤ alpha := by
    dsimp only [alpha]
    linarith [xiRightTransverseSup_pos hne]
  have halphaPos : 0 < alpha := by
    dsimp only [alpha]
    linarith [xiRightTransverseSup_pos hne]
  have halphaSup : alpha < xiRightTransverseSup := by
    dsimp only [alpha]
    linarith [xiRightTransverseSup_pos hne]
  obtain ⟨C, hC, hupper⟩ := hsubexponential (2 * alpha) (by positivity)
  have hlog : Tendsto (fun n : ℕ => Real.log n / 2) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 2)
  have hsampleUpper : ∀ᶠ n : ℕ in atTop,
      eta (Real.log n / 2) ≤ C * Real.exp ((2 * alpha) * (Real.log n / 2)) :=
    hlog.eventually hupper
  rw [eventually_atTop] at hsampleUpper
  obtain ⟨N0, hN0⟩ := hsampleUpper
  obtain ⟨n, hn0, hLn, hlower⟩ :=
    not_riemannHypothesis_implies_inwardRestrictedWeilFloor_cofinally_exceeds_power
      hL halpha0 hnot halphaSup henv C hC N0
  have hlogn : 0 < Real.log n := by linarith
  have hn1 : (1 : ℝ) < n := (Real.log_pos_iff (Nat.cast_nonneg n)).mp hlogn
  have hnpos : (0 : ℝ) < n := lt_trans zero_lt_one hn1
  have hpow : Real.exp ((2 * alpha) * (Real.log n / 2)) = (n : ℝ) ^ alpha := by
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have hnupper := hN0 n hn0
  rw [hpow] at hnupper
  exact (not_lt_of_ge hnupper) hlower

theorem riemannHypothesis_iff_aperture_subexponential
    {L : ℝ} (hL : 0 < L) {N : ℕ} {eta : ℝ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (fun n => eta (Real.log n / 2)))
    (hzero : RiemannHypothesis → ∀ a, eta a = 0) :
    RiemannHypothesis ↔ SubexponentialAtApertureInfinity eta := by
  constructor
  · intro hRH epsilon hepsilon
    refine ⟨0, le_rfl, ?_⟩
    filter_upwards with a
    rw [hzero hRH a]
    exact mul_nonneg le_rfl (Real.exp_pos _).le
  · intro hsubexponential
    by_contra hnot
    exact not_aperture_subexponential_of_false_rh
      hL hnot henv hsubexponential

theorem restrictedWeilFloor_not_eventually_zero_of_not_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ} (hnot : ¬ RiemannHypothesis)
    {eta : ℕ → ℝ} (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta) :
    ¬ ∀ᶠ n : ℕ in atTop, eta n = 0 := by
  intro hzero
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot
  rw [eventually_atTop] at hzero
  obtain ⟨N0, hN0⟩ := hzero
  obtain ⟨n, hn0, _hLn, hlower⟩ :=
    not_riemannHypothesis_implies_inwardRestrictedWeilFloor_cofinally_exceeds_power
      hL (alpha := 0) le_rfl hnot (xiRightTransverseSup_pos hne) henv 0 le_rfl N0
  rw [hN0 n hn0] at hlower
  norm_num at hlower

/-- The exact monotone floor specialization of the nonnegative Dirichlet-abscissa identity. -/
theorem restrictedWeilFloor_abscissa_eq_one_add_logPowerExponent_of_not_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ} (hnot : ¬ RiemannHypothesis)
    {eta : ℕ → ℝ} (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta)
    (hmono : Monotone eta) :
    LSeries.abscissaOfAbsConv (fun n => ((eta n : ℝ) : ℂ)) =
      1 + NonnegativeCoefficientLogPowerExponent eta := by
  exact monotone_nonnegative_abscissa_eq_one_add_logPowerExponent
    henv.1 hmono (restrictedWeilFloor_not_eventually_zero_of_not_rh hL hnot henv)

theorem restrictedWeilFloor_abscissa_eq_bot_of_rh
    {eta : ℕ → ℝ} (hzero : ∀ n, eta n = 0) :
    LSeries.abscissaOfAbsConv (fun n => ((eta n : ℝ) : ℂ)) = ⊥ := by
  apply le_antisymm
  · apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
    intro sigma _hsigma
    have hz : (fun n => ((eta n : ℝ) : ℂ)) = 0 := by
      funext n
      simp [hzero n]
    rw [hz]
    exact LSeriesSummable_zero
  · exact bot_le

theorem inwardRestrictedWeilFloor_abscissa_eq_bot_of_rh
    {lambda : ℕ → ℝ} (hRH : RiemannHypothesis)
    (hpositive : RiemannHypothesis → ∀ n, 0 ≤ lambda n) :
    LSeries.abscissaOfAbsConv
        (fun n => ((inwardRestrictedWeilNegativeFloor lambda n : ℝ) : ℂ)) = ⊥ := by
  apply restrictedWeilFloor_abscissa_eq_bot_of_rh
  intro n
  rw [inwardRestrictedWeilNegativeFloor, negPart_def,
    max_eq_right (neg_nonpos.mpr (hpositive hRH n))]

end

end RHTower
