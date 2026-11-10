import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw

/-!
# The sharp floor of an exceptional real pair

The two real exponential moments form one positive square minus one
negative square. On packets supported in `[-a,a]`, the optimal mass
floor is `sinh(2δa)/δ - 2a`. Even smooth cutoffs of `sinh(δu)` approach
the lower edge, so restricting to smooth packets does not improve it.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open SquareRootThreshold

/-- The contribution of a simple real zero and its reflection. -/
def realPairForm (δ : ℝ) (f : ℝ → ℝ) : ℝ :=
  2 * (∫ u, f u * Real.exp (δ * u)) * ∫ u, f u * Real.exp (-(δ * u))

theorem realPairForm_eq_hyperbolic_squares (δ : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    realPairForm δ f = 2 * ((∫ u, f u * Real.cosh (δ * u)) ^ 2 -
      (∫ u, f u * Real.sinh (δ * u)) ^ 2) := by
  have hc : Integrable (fun u => f u * Real.cosh (δ * u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hs : Integrable (fun u => f u * Real.sinh (δ * u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hp : (∫ u, f u * Real.exp (δ * u)) =
      (∫ u, f u * Real.cosh (δ * u)) + ∫ u, f u * Real.sinh (δ * u) := by
    rw [← integral_add hc hs]
    apply integral_congr_ae
    filter_upwards with u
    rw [← mul_add, Real.cosh_add_sinh]
  have hn : (∫ u, f u * Real.exp (-(δ * u))) =
      (∫ u, f u * Real.cosh (δ * u)) - ∫ u, f u * Real.sinh (δ * u) := by
    rw [← integral_sub hc hs]
    apply integral_congr_ae
    filter_upwards with u
    rw [← mul_sub, Real.cosh_sub_sinh]
  rw [realPairForm, hp, hn]
  ring

theorem pairEnergy_pos_of_pos {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) :
    0 < pairEnergy δ a := by
  have h := Real.self_lt_sinh_iff.mpr (by positivity : 0 < 2 * δ * a)
  have he : a < Real.sinh (2 * δ * a) / (2 * δ) :=
    (lt_div_iff₀ (by positivity : 0 < 2 * δ)).mpr (by nlinarith only [h])
  exact sub_pos.mpr he

/-- Cauchy–Schwarz bounds the only negative hyperbolic coordinate. -/
theorem realPairForm_ge_neg_two_pairEnergy {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a)
    {f : ℝ → ℝ} (hf : Continuous f) (hfs : tsupport f ⊆ Icc (-a) a) :
    -2 * pairEnergy δ a * (∫ u, f u ^ 2) ≤ realPairForm δ f := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  let g : ℝ → ℝ := (Icc (-a) a).indicator (fun u => Real.sinh (δ * u))
  have hgsq (u : ℝ) : g u ^ 2 =
      (Icc (-a) a).indicator (fun u => Real.sinh (δ * u) ^ 2) u := by
    by_cases hu : u ∈ Icc (-a) a <;> simp only [g, indicator_of_mem, indicator_of_notMem, hu, zero_pow two_ne_zero]
  have hgi : Integrable (fun u => g u ^ 2) := by
    simp_rw [hgsq]
    exact ((by fun_prop : Continuous fun u => Real.sinh (δ * u) ^ 2).integrableOn_Icc
      ).integrable_indicator measurableSet_Icc
  have hfi : Integrable (fun u => f u ^ 2) := by
    simpa only [pow_two] using
      (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
  have hgm : AEStronglyMeasurable g :=
    (by fun_prop : Continuous fun u => Real.sinh (δ * u)).aestronglyMeasurable.indicator
      measurableSet_Icc
  have hcs := HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
    hf.aestronglyMeasurable hgm hfi hgi
  have hfg : (∫ u, f u * g u) = ∫ u, f u * Real.sinh (δ * u) := by
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Icc (-a) a
    · rw [g, indicator_of_mem hu]
    · rw [g, indicator_of_notMem hu, eq_zero_of_not_mem_Icc hfs hu, zero_mul, zero_mul]
  have hgv : (∫ u, g u ^ 2) = pairEnergy δ a := by
    simp_rw [hgsq]
    rw [integral_indicator measurableSet_Icc, integral_sinh_sq_Icc hδ ha]
  rw [hfg, hgv] at hcs
  rw [realPairForm_eq_hyperbolic_squares δ hf hfc]
  nlinarith only [hcs, sq_nonneg (∫ u, f u * Real.cosh (δ * u))]

/-- Smooth odd packets approach the negative edge of the real-pair form. -/
theorem exists_smooth_realPairForm_below {δ a L : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hL : 0 ≤ L) (hS : L < pairEnergy δ a) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      realPairForm δ f < -2 * L * (∫ u, f u ^ 2) := by
  let S := pairEnergy δ
  have hSa : L * S a < S a ^ 2 := by
    have hpos : 0 < S a := hL.trans_lt hS
    nlinarith only [hS, hpos]
  have hev : ∀ᶠ x in 𝓝[<] a, L * S a < S x ^ 2 ∧ a / 2 < x := by
    exact ((((continuous_pairEnergy δ).pow 2).continuousAt.eventually
      (lt_mem_nhds hSa)).and (continuous_id.continuousAt.eventually
      (lt_mem_nhds (by linarith only [ha] : a / 2 < a)))).filter_mono nhdsWithin_le_nhds
  obtain ⟨a', ⟨hSa', ha'2⟩, ha'a⟩ := (hev.and self_mem_nhdsWithin).exists
  have ha' : 0 < a' := by linarith only [ha, ha'2]
  let φ : ContDiffBump (0 : ℝ) := ⟨a', a, ha', ha'a⟩
  let f : ℝ → ℝ := fun u => Real.sinh (δ * u) * φ u
  have hf : ContDiff ℝ 2 f :=
    (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).mul φ.contDiff
  have hz (u : ℝ) (hu : u ∉ Icc (-a) a) : f u = 0 := by
    have hφ : φ u = 0 := by
      apply φ.zero_of_le_dist
      rw [Real.dist_eq, sub_zero]
      by_contra hn
      exact hu (abs_le.mp (le_of_lt (lt_of_not_ge hn)))
    simp only [f, hφ, mul_zero]
  have hfs : tsupport f ⊆ Icc (-a) a :=
    closure_minimal (fun u hu => by by_contra hn; exact hu (hz u hn)) isClosed_Icc
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  let J : ℝ := ∫ u, φ u * Real.sinh (δ * u) ^ 2
  have hodd : (∫ u, f u * Real.cosh (δ * u)) = 0 :=
    _root_.RHTower.integral_odd_mul_cosh (fun u => by
      simp only [f, φ.neg, mul_neg, Real.sinh_neg, neg_mul]) δ
  have hmoment : (∫ u, f u * Real.sinh (δ * u)) = J := by
    apply integral_congr_ae
    filter_upwards with u
    dsimp [f]
    ring
  have hpair : realPairForm δ f = -2 * J ^ 2 := by
    rw [realPairForm_eq_hyperbolic_squares δ hf.continuous hfc, hodd, hmoment]
    ring
  have hupper : (∫ u, f u ^ 2) ≤ S a := by
    rw [show S a = pairEnergy δ a from rfl, ← integral_sinh_sq_Icc hδ ha.le,
      ← integral_indicator measurableSet_Icc]
    apply integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
      (((by fun_prop : Continuous fun u => Real.sinh (δ * u) ^ 2).integrableOn_Icc
        ).integrable_indicator measurableSet_Icc)
    filter_upwards with u
    by_cases hu : u ∈ Icc (-a) a
    · rw [indicator_of_mem hu]
      dsimp [f]
      rw [mul_pow]
      have hφ : φ u ^ 2 ≤ 1 := by
        nlinarith only [φ.le_one (x := u), φ.nonneg (x := u)]
      exact (mul_le_mul_of_nonneg_left hφ (sq_nonneg _)).trans_eq (mul_one _)
    · rw [indicator_of_notMem hu, hz u hu]
      norm_num
  have hlower : S a' ≤ J := by
    rw [show S a' = pairEnergy δ a' from rfl, ← integral_sinh_sq_Icc hδ ha'.le,
      ← integral_indicator measurableSet_Icc]
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun u => Set.indicator_nonneg (fun _ _ => sq_nonneg _) u)
      ((φ.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right)
    filter_upwards with u
    by_cases hu : u ∈ Icc (-a') a'
    · rw [indicator_of_mem hu, φ.one_of_mem_closedBall]
      · rw [one_mul]
      · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
        exact hu
    · rw [indicator_of_notMem hu]
      exact mul_nonneg φ.nonneg (sq_nonneg _)
  have hJ := pow_le_pow_left₀ (pairEnergy_nonneg hδ ha'.le) hlower 2
  have hLM := mul_le_mul_of_nonneg_left hupper hL
  refine ⟨f, hf, hfs, ?_⟩
  rw [hpair]
  nlinarith only [hJ, hLM, hSa']

/-- The exact mass-floor coefficient, even when only smooth packets are tested. -/
theorem realPairForm_mass_floor_iff {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) (c : ℝ) :
    (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      -c * (∫ u, f u ^ 2) ≤ realPairForm δ f) ↔ 2 * pairEnergy δ a ≤ c := by
  constructor
  · intro h
    by_contra hn
    have hc : c / 2 < pairEnergy δ a := by linarith only [lt_of_not_ge hn]
    have hmax : max (c / 2) 0 < pairEnergy δ a :=
      max_lt hc (pairEnergy_pos_of_pos hδ ha)
    obtain ⟨f, hf, hfs, hbad⟩ := exists_smooth_realPairForm_below hδ ha
      (le_max_right (c / 2) 0) hmax
    have hbound := h f hf hfs
    have hmass : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hcoef : c ≤ 2 * max (c / 2) 0 := by
      linarith only [le_max_left (c / 2) 0]
    have hm := mul_le_mul_of_nonneg_right hcoef hmass
    nlinarith only [hbad, hbound, hm]
  · intro hc f hf hfs
    apply le_trans _ (realPairForm_ge_neg_two_pairEnergy hδ ha.le hf.continuous hfs)
    have hm := mul_le_mul_of_nonneg_right hc (integral_nonneg fun u => sq_nonneg (f u))
    linarith only [hm]

/-- Unit-mass smooth packets approach the exact lower edge arbitrarily closely. -/
theorem exists_unit_realPairForm_near_lower_edge {δ a ε : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (∫ u, f u ^ 2) = 1 ∧ realPairForm δ f < -2 * pairEnergy δ a + ε := by
  classical
  have hn : ¬ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      -(2 * pairEnergy δ a - ε) * (∫ u, f u ^ 2) ≤ realPairForm δ f := by
    rw [realPairForm_mass_floor_iff hδ ha]
    linarith only [hε]
  push_neg at hn
  obtain ⟨f, hf, hfs, hbad⟩ := hn
  let M : ℝ := ∫ u, f u ^ 2
  have hM0 : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  have hM : 0 < M := by
    by_contra hn
    have he : M = 0 := le_antisymm (le_of_not_gt hn) hM0
    have hlo := realPairForm_ge_neg_two_pairEnergy hδ ha.le hf.continuous hfs
    change -2 * pairEnergy δ a * M ≤ realPairForm δ f at hlo
    change realPairForm δ f < -(2 * pairEnergy δ a - ε) * M at hbad
    rw [he, mul_zero] at hlo hbad
    exact (not_lt_of_ge hlo) hbad
  let r : ℝ := (Real.sqrt M)⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hM)
  have hrM : r ^ 2 * M = 1 := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hM0, inv_mul_cancel₀ hM.ne']
  let g : ℝ → ℝ := fun u => r * f u
  have hg : ContDiff ℝ 2 g := contDiff_const.mul hf
  have hgs : tsupport g ⊆ Icc (-a) a := by
    apply closure_minimal _ isClosed_Icc
    intro u hu
    by_contra hn
    exact hu (by simp only [g, eq_zero_of_not_mem_Icc hfs hn, mul_zero])
  have hmass : (∫ u, g u ^ 2) = 1 := by
    simp only [g, mul_pow, integral_const_mul]
    exact hrM
  have hform : realPairForm δ g = r ^ 2 * realPairForm δ f := by
    simp only [realPairForm, g, mul_assoc, integral_const_mul]
    ring
  have hh := mul_lt_mul_of_pos_left hbad (sq_pos_of_pos hr)
  change r ^ 2 * realPairForm δ f < r ^ 2 * (-(2 * pairEnergy δ a - ε) * M) at hh
  have he : r ^ 2 * (-(2 * pairEnergy δ a - ε) * M) =
      -2 * pairEnergy δ a + ε := by
    calc _ = -(2 * pairEnergy δ a - ε) * (r ^ 2 * M) := by ring
      _ = _ := by rw [hrM]; ring
  rw [he] at hh
  exact ⟨g, hg, hgs, hmass, hform.trans_lt hh⟩

#print axioms realPairForm_ge_neg_two_pairEnergy
#print axioms exists_smooth_realPairForm_below
#print axioms realPairForm_mass_floor_iff
#print axioms exists_unit_realPairForm_near_lower_edge

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
