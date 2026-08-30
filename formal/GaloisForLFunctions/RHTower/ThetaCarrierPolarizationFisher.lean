import GaloisForLFunctions.RHTower.ThetaCarrierHassePacket
import GaloisForLFunctions.HTGeometry.ReflectedExponentialFisher
import GaloisForLFunctions.HTGeometry.ReflectedLikelihoodJuliaRealization
import GaloisForLFunctions.HTGeometry.BoundedMultiplierNonclosedRange
import GaloisForLFunctions.HTGeometry.TanhSelfBound

/-!
# The literal theta carrier of the reflected exponential family

The completed even positive theta source, normalized to a probability, together with the identity
statistic and the sign reflection, is a reflected exponential family.  Corollary 8.2 of the
likelihood-polarization law therefore holds literally: the posterior contrast of the reflected
tilt pair is `tanh(a·x)` with visibility `sech(a·x)`, the canonical coherence energy is strictly
positive off the centre, the sign-blind and polarized Julia lifts agree exactly at the centre, the
second-order coherence response is four times the variance of the theta source, and the contrast
multiplier is injective with dense nonclosed range at every noncentral tilt because the positive
theta density meets every neighbourhood of the origin.
-/

namespace RHTower

open MeasureTheory ProbabilityTheory Real GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

/-- **Corollary 8.2.**  The completed even positive theta source, normalized to a probability,
with the identity statistic and the sign reflection, is a reflected exponential family. -/
def thetaCarrier : ReflectedExponentialFamily ℝ where
  base := thetaTiltProb 0
  isProb := thetaTiltProb_isProbabilityMeasure (by norm_num)
  reflection := fun x => -x
  measurable_reflection := measurable_neg
  reflection_involutive := neg_neg
  map_base := by simpa using map_neg_thetaTiltProb (a := 0) (by norm_num)
  stat := id
  measurable_stat := measurable_id
  stat_odd := fun _ => rfl

@[simp] theorem thetaCarrier_base : thetaCarrier.base = thetaTiltProb 0 := rfl

@[simp] theorem thetaCarrier_stat (x : ℝ) : thetaCarrier.stat x = x := rfl

@[simp] theorem thetaCarrier_reflection (x : ℝ) : thetaCarrier.reflection x = -x := rfl

/-- The abstract tilt of the theta carrier is the literal positive theta tilt. -/
theorem thetaCarrier_tilt (a : ℝ) : thetaCarrier.tilt a = thetaTiltProb a := by
  rw [ReflectedExponentialFamily.tilt, thetaCarrier_base]
  have h := thetaTiltProb_tilt (a := a) (b := 0) (by norm_num)
  rw [← h]
  refine tilted_congr ?_
  filter_upwards with x
  show a * thetaCarrier.stat x = (a - 0) * x
  simp

/-- Every tilt in the closed unit interval is integrable against the theta carrier. -/
theorem integrable_exp_mul_thetaCarrier {a : ℝ} (ha : |a| ≤ 1) :
    Integrable (fun x => Real.exp (a * thetaCarrier.stat x)) thetaCarrier.base := by
  rw [thetaCarrier_base]
  refine integrable_thetaTiltProb (a := 0) (by norm_num) ?_
  have h := integrable_thetaTiltIntegrand ha 0
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  show x ^ 0 * Real.exp (a * x) * thetaCuspFullSource x
    = Real.exp (a * thetaCarrier.stat x) * Real.exp (0 * x) * thetaCuspFullSource x
  show x ^ 0 * Real.exp (a * x) * thetaCuspFullSource x
    = Real.exp (a * x) * Real.exp (0 * x) * thetaCuspFullSource x
  simp

theorem thetaCarrier_mem_integrableExpSet {a : ℝ} (ha : |a| ≤ 1) :
    a ∈ integrableExpSet thetaCarrier.stat thetaCarrier.base :=
  integrable_exp_mul_thetaCarrier ha

/-- The open unit interval lies in the interior of the integrability set. -/
theorem thetaCarrier_Ioo_subset_interior :
    Set.Ioo (-1 : ℝ) 1 ⊆ interior (integrableExpSet thetaCarrier.stat thetaCarrier.base) :=
  interior_maximal
    (fun _ ha => thetaCarrier_mem_integrableExpSet (abs_le.mpr ⟨ha.1.le, ha.2.le⟩)) isOpen_Ioo

theorem thetaCarrier_mem_interior {a : ℝ} (ha : |a| < 1) :
    a ∈ interior (integrableExpSet thetaCarrier.stat thetaCarrier.base) :=
  thetaCarrier_Ioo_subset_interior (by
    rw [Set.mem_Ioo]
    exact ⟨neg_lt_of_abs_lt ha, lt_of_abs_lt ha⟩)

/-! ## Item 1: the exact functional-equation polarization -/

/-- `(LPC.39)`  The posterior contrast of the reflected theta tilt pair is `tanh(a·x)`. -/
theorem thetaCarrier_posteriorContrast {a : ℝ} (ha : |a| ≤ 1) :
    posteriorContrast (thetaTiltProb a) (thetaTiltProb (-a))
      =ᵐ[balancedLaw (thetaTiltProb a) (thetaTiltProb (-a))] fun x => Real.tanh (a * x) := by
  have h := thetaCarrier.posteriorContrast_tilt a (integrable_exp_mul_thetaCarrier ha)
  simpa only [thetaCarrier_tilt, thetaCarrier_stat] using h

/-- The visibility of the reflected theta tilt pair is `sech(a·x)`. -/
theorem thetaCarrier_visibilityDensity {a : ℝ} (ha : |a| ≤ 1) :
    visibilityDensity (thetaTiltProb a) (thetaTiltProb (-a))
      =ᵐ[balancedLaw (thetaTiltProb a) (thetaTiltProb (-a))]
        fun x => 1 / Real.cosh (a * x) := by
  filter_upwards [thetaCarrier_posteriorContrast ha] with x hx
  have hc := Real.cosh_pos (a * x)
  have hkey : 1 - Real.tanh (a * x) ^ 2 = (1 / Real.cosh (a * x)) ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq (a * x)]
  rw [visibilityDensity, hx, hkey]
  exact Real.sqrt_sq (by positivity)

/-! ## Item 2: strict canonical coherence energy off the centre -/

theorem thetaTiltProb_absolutelyContinuous_volume {a : ℝ} (ha : |a| ≤ 1) :
    thetaTiltProb a ≪ (volume : Measure ℝ) := by
  rw [thetaTiltProb_eq_withDensity ha]
  exact withDensity_absolutelyContinuous _ _

theorem thetaCarrier_base_singleton_zero : thetaCarrier.base {(0 : ℝ)} = 0 :=
  thetaTiltProb_absolutelyContinuous_volume (a := 0) (by norm_num) (by simp)

theorem thetaCarrier_base_ne_zero : thetaCarrier.base {x : ℝ | x ≠ 0} = 1 := by
  haveI := thetaCarrier.isProb
  have hset : {x : ℝ | x ≠ 0} = ({(0 : ℝ)} : Set ℝ)ᶜ := by ext x; simp
  rw [hset, prob_compl_eq_one_sub (μ := thetaCarrier.base) (measurableSet_singleton (0 : ℝ)),
    thetaCarrier_base_singleton_zero, tsub_zero]

theorem integrable_cosh_thetaCarrier {a : ℝ} (ha : |a| ≤ 1) :
    Integrable (fun x : ℝ => Real.cosh (a * x)) thetaCarrier.base := by
  have h1 := integrable_exp_mul_thetaCarrier ha
  have h2 := integrable_exp_mul_thetaCarrier (a := -a) (by rwa [abs_neg])
  refine ((h1.add h2).div_const 2).congr (Filter.Eventually.of_forall fun x => ?_)
  show (Real.exp (a * x) + Real.exp (-a * x)) / 2 = Real.cosh (a * x)
  rw [Real.cosh_eq, neg_mul]

theorem integrable_sinhSq_div_cosh_thetaCarrier {a : ℝ} (ha : |a| ≤ 1) :
    Integrable (fun x : ℝ => Real.sinh (a * x) ^ 2 / Real.cosh (a * x)) thetaCarrier.base := by
  refine (integrable_cosh_thetaCarrier ha).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).pow 2).div
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
      (fun x => (Real.cosh_pos _).ne')).aestronglyMeasurable
  · have hc := Real.cosh_pos (a * x)
    have hs : Real.sinh (a * x) ^ 2 ≤ Real.cosh (a * x) ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq (a * x)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hc]
    nlinarith [hs]

theorem integral_sinhSq_div_cosh_pos {a : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0) :
    0 < ∫ x : ℝ, Real.sinh (a * x) ^ 2 / Real.cosh (a * x) ∂thetaCarrier.base := by
  rw [integral_pos_iff_support_of_nonneg
    (fun x => by positivity) (integrable_sinhSq_div_cosh_thetaCarrier ha)]
  have hsupp : (Function.support
      fun x : ℝ => Real.sinh (a * x) ^ 2 / Real.cosh (a * x)) = {x : ℝ | x ≠ 0} := by
    ext x
    simp only [Function.mem_support, Set.mem_setOf_eq]
    constructor
    · intro h hx
      exact h (by rw [hx, mul_zero, Real.sinh_zero]; simp)
    · intro hx h
      have hc := Real.cosh_pos (a * x)
      have hs : Real.sinh (a * x) ^ 2 = 0 := by
        rcases div_eq_zero_iff.mp h with h1 | h1
        · exact h1
        · exact absurd h1 hc.ne'
      have : Real.sinh (a * x) = 0 := by nlinarith [hs]
      rw [Real.sinh_eq_zero] at this
      exact hx (by
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 ha0
        · exact h0)
  rw [hsupp, thetaCarrier_base_ne_zero]
  norm_num

/-- `(LPC.40)`  The canonical coherence energy of the reflected theta tilt pair. -/
theorem thetaCarrier_coherenceWork {a : ℝ} (ha : |a| ≤ 1) :
    coherenceWork (thetaTiltProb a) (thetaTiltProb (-a))
      = 4 / mgf thetaCarrier.stat thetaCarrier.base a
        * ∫ x : ℝ, Real.sinh (a * x) ^ 2 / Real.cosh (a * x) ∂thetaCarrier.base := by
  have h := thetaCarrier.coherenceWork_tilt a (integrable_exp_mul_thetaCarrier ha)
  simpa only [thetaCarrier_tilt, thetaCarrier_stat] using h

/-- **Corollary 8.2 (2).**  The coherence energy is strictly positive off the centre. -/
theorem thetaCarrier_coherenceWork_pos {a : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0) :
    0 < coherenceWork (thetaTiltProb a) (thetaTiltProb (-a)) := by
  rw [thetaCarrier_coherenceWork ha]
  have hmgf := thetaCarrier.mgf_pos a (integrable_exp_mul_thetaCarrier ha)
  have hint := integral_sinhSq_div_cosh_pos ha ha0
  positivity

theorem thetaCarrier_coherenceWork_centre :
    coherenceWork (thetaTiltProb 0) (thetaTiltProb (-0)) = 0 := by
  haveI := thetaTiltProb_isProbabilityMeasure (a := 0) (by norm_num)
  rw [neg_zero, coherenceWork]
  rw [integral_congr_ae (g := fun _ : ℝ => (0 : ℝ)) ?_]
  · simp
  · filter_upwards [posteriorContrast_self (thetaTiltProb 0)] with x hx
    rw [hx]
    norm_num

/-- **Corollary 8.2 (2).**  Exact centre selection by the coherence energy. -/
theorem thetaCarrier_coherenceWork_eq_zero_iff {a : ℝ} (ha : |a| ≤ 1) :
    coherenceWork (thetaTiltProb a) (thetaTiltProb (-a)) = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha0
    exact absurd h (thetaCarrier_coherenceWork_pos ha ha0).ne'
  · rintro rfl
    exact thetaCarrier_coherenceWork_centre

/-! ## The cumulant generating function is the theta log partition -/

theorem thetaCarrier_mgf (a : ℝ) :
    mgf thetaCarrier.stat thetaCarrier.base a = thetaTiltMoment a 0 / thetaTiltMoment 0 0 := by
  simp only [mgf, thetaCarrier_stat, thetaCarrier_base]
  rw [integral_thetaTiltProb (a := 0) (by norm_num) (fun x => Real.exp (a * x))]
  congr 1
  rw [thetaTiltMoment]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (a * x) * Real.exp (0 * x) * thetaCuspFullSource x
      = x ^ 0 * Real.exp (a * x) * thetaCuspFullSource x
  simp

theorem thetaCarrier_cgf {a : ℝ} (ha : |a| ≤ 1) :
    cgf thetaCarrier.stat thetaCarrier.base a
      = thetaTiltLogPartition a - thetaTiltLogPartition 0 := by
  rw [cgf, thetaCarrier_mgf,
    Real.log_div (thetaTiltMoment_zero_pos a ha).ne'
      (thetaTiltMoment_zero_pos 0 (by norm_num)).ne',
    thetaTiltLogPartition, thetaTiltLogPartition]

theorem thetaCarrier_deriv_cgf {a : ℝ} (ha : |a| < 1) :
    deriv (cgf thetaCarrier.stat thetaCarrier.base) a = thetaTiltMean a := by
  have heq : cgf thetaCarrier.stat thetaCarrier.base
      =ᶠ[nhds a] fun b => thetaTiltLogPartition b - thetaTiltLogPartition 0 := by
    have hnhds : Set.Ioo (-1 : ℝ) 1 ∈ nhds a :=
      Ioo_mem_nhds (neg_lt_of_abs_lt ha) (lt_of_abs_lt ha)
    filter_upwards [hnhds] with b hb
    exact thetaCarrier_cgf (abs_le.mpr ⟨hb.1.le, hb.2.le⟩)
  rw [heq.deriv_eq]
  exact ((hasDerivAt_thetaTiltLogPartition ha).sub_const _).deriv

/-! ## The symmetric information work of the reflected theta pair -/

/-- `(LPC.41)`  Jeffreys information of the reflected theta tilt pair is `4a·F'(a)`. -/
theorem thetaCarrier_formationJeffreys {a : ℝ} (ha : |a| < 1) :
    formationJeffreys (thetaTiltProb a) (thetaTiltProb (-a))
      = ENNReal.ofReal (4 * a * thetaTiltMean a) := by
  have h := thetaCarrier.formationJeffreys_tilt a (thetaCarrier_mem_interior ha)
  simpa only [thetaCarrier_tilt, thetaCarrier_deriv_cgf ha] using h

theorem thetaTiltReflectedWork_nonneg {a : ℝ} (ha : |a| < 1) : 0 ≤ 4 * a * thetaTiltMean a := by
  rw [abs_lt] at ha
  rcases lt_trichotomy a 0 with hlt | heq | hgt
  · have hpos : 0 < thetaTiltMean (-a) := thetaTiltMean_pos_of_pos (by linarith) (by linarith)
    rw [thetaTiltMean_neg] at hpos
    nlinarith
  · rw [heq]; ring_nf; exact le_refl 0
  · have hpos : 0 < thetaTiltMean a := thetaTiltMean_pos_of_pos hgt (by linarith)
    nlinarith

/-- **Corollary 8.2.**  The symmetric information work vanishes exactly at the centre. -/
theorem thetaCarrier_formationJeffreys_eq_zero_iff {a : ℝ} (ha : |a| < 1) :
    formationJeffreys (thetaTiltProb a) (thetaTiltProb (-a)) = 0 ↔ a = 0 := by
  rw [thetaCarrier_formationJeffreys ha, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    exact (thetaTiltReflectedWork_eq_zero_iff ha).mp
      (le_antisymm h (thetaTiltReflectedWork_nonneg ha))
  · rintro rfl
    rw [thetaTiltMean_zero]
    norm_num

/-! ## Item 4: Fisher curvature at the centre -/

theorem thetaCarrier_integral_sq :
    ∫ x : ℝ, x ^ 2 ∂thetaCarrier.base = thetaTiltVariance 0 := by
  have h2 : thetaTiltMean 0 ^ 2 = 0 := by rw [thetaTiltMean_zero]; ring
  rw [thetaCarrier_base, integral_thetaTiltProb (a := 0) (by norm_num) (fun x => x ^ 2),
    thetaTiltVariance, h2, sub_zero]
  congr 1

/-- **Corollary 8.2 (4).**  The second-order coherence response at the centre is four times the
variance of the theta source. -/
theorem thetaCarrier_tendsto_coherenceWork_div_sq :
    Filter.Tendsto (fun a => coherenceWork (thetaTiltProb a) (thetaTiltProb (-a)) / a ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * thetaTiltVariance 0)) := by
  have hhalf : |(1 : ℝ) / 2| < 1 := by rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; norm_num
  have hneg : |(-((1 : ℝ) / 2))| < 1 := by
    rw [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; norm_num
  have hzero : |(0 : ℝ)| < 1 := by norm_num
  have hsub : ∀ t : ℝ, |t| ≤ (1 : ℝ) / 2 →
      Integrable (fun x => Real.exp (t * thetaCarrier.stat x)) thetaCarrier.base :=
    fun t ht => integrable_exp_mul_thetaCarrier (le_trans ht (by norm_num))
  have h := thetaCarrier.tendsto_coherenceWork_div_sq ((1 : ℝ) / 2) (by norm_num)
    (thetaCarrier_mem_interior hhalf)
    (thetaCarrier_mem_interior hneg)
    (thetaCarrier_mem_interior hzero) hsub
  simpa only [thetaCarrier_tilt, thetaCarrier_stat, thetaCarrier_integral_sq] using h

/-! ## The reflected theta experiment -/

/-- The reflected binary experiment carried by the theta tilt `a`. -/
def thetaPair {a : ℝ} (ha : |a| ≤ 1) : ReflectedPair ℝ where
  source := thetaTiltProb a
  isProb := thetaTiltProb_isProbabilityMeasure ha
  reflection := fun x => -x
  measurable_reflection := measurable_neg
  reflection_involutive := neg_neg

@[simp] theorem thetaPair_source {a : ℝ} (ha : |a| ≤ 1) :
    (thetaPair ha).source = thetaTiltProb a := rfl

theorem thetaPair_target {a : ℝ} (ha : |a| ≤ 1) :
    (thetaPair ha).target = thetaTiltProb (-a) :=
  map_neg_thetaTiltProb ha

theorem thetaPair_balancedLaw {a : ℝ} (ha : |a| ≤ 1) :
    balancedLaw (thetaPair ha).source (thetaPair ha).target
      = balancedLaw (thetaTiltProb a) (thetaTiltProb (-a)) := by
  rw [thetaPair_source, thetaPair_target ha]

theorem abs_tanh_le_abs (y : ℝ) : |Real.tanh y| ≤ |y| := by
  rcases le_total 0 y with hy | hy
  · have h0 : 0 ≤ Real.tanh y := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hy) (Real.cosh_pos y).le
    rw [abs_of_nonneg h0, abs_of_nonneg hy]
    exact tanh_le_self hy
  · have h0 : Real.tanh y ≤ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hy) (Real.cosh_pos y).le
    rw [abs_of_nonpos h0, abs_of_nonpos hy, ← Real.tanh_neg]
    exact tanh_le_self (by linarith)

/-- `(LPC.3)`  The contrast symbol of the reflected theta experiment is `tanh(a·x)`. -/
theorem thetaPair_contrastSymbol_ae {a : ℝ} (ha : |a| ≤ 1) :
    (thetaPair ha).contrastSymbol
      =ᵐ[balancedLaw (thetaPair ha).source (thetaPair ha).target]
        fun x => ((Real.tanh (a * x) : ℝ) : ℂ) := by
  rw [thetaPair_balancedLaw ha]
  have hst : (thetaPair ha).target = thetaTiltProb (-a) := thetaPair_target ha
  filter_upwards [thetaCarrier_posteriorContrast ha] with x hx
  simp only [ReflectedPair.contrastSymbol, truncContrast, thetaPair_source, hst, hx]
  have h1 : Real.tanh (a * x) < 1 := Real.tanh_lt_one _
  have h2 : (-1 : ℝ) < Real.tanh (a * x) := Real.neg_one_lt_tanh _
  rw [min_eq_right h1.le, max_eq_right h2.le]

/-! ## Item 5: the coherence range is injective, dense and nonclosed -/

theorem thetaTiltProb_Ioo_ne_zero {a : ℝ} (ha : |a| ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    thetaTiltProb a (Set.Ioo (-δ) δ) ≠ 0 := by
  have hM := thetaTiltMoment_zero_pos a ha
  have hne : ∀ x : ℝ, ENNReal.ofReal
      (Real.exp (a * x) * thetaCuspFullSource x / thetaTiltMoment a 0) ≠ 0 := by
    intro x
    have hp : 0 < Real.exp (a * x) * thetaCuspFullSource x / thetaTiltMoment a 0 := by
      have := thetaCuspFullSource_pos_all x
      positivity
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hp]
  rw [thetaTiltProb_eq_withDensity ha, withDensity_apply _ measurableSet_Ioo]
  intro h0
  rw [lintegral_eq_zero_iff (measurable_thetaTiltProbDensity a)] at h0
  have huniv : (volume.restrict (Set.Ioo (-δ) δ)) Set.univ = 0 := by
    have h := ae_iff.mp h0
    simpa [hne] using h
  rw [Measure.restrict_apply_univ, Real.volume_Ioo] at huniv
  rw [ENNReal.ofReal_eq_zero] at huniv
  linarith

theorem balancedLaw_thetaTilt_Ioo_ne_zero {a : ℝ} (ha : |a| ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    balancedLaw (thetaTiltProb a) (thetaTiltProb (-a)) (Set.Ioo (-δ) δ) ≠ 0 := by
  rw [balancedLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  intro h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 (by simp)
  · exact thetaTiltProb_Ioo_ne_zero ha hδ (add_eq_zero.mp h1).1

theorem thetaPair_balancedLaw_singleton_zero {a : ℝ} (ha : |a| ≤ 1) :
    balancedLaw (thetaTiltProb a) (thetaTiltProb (-a)) {(0 : ℝ)} = 0 := by
  have habs : |(-a)| ≤ 1 := by rwa [abs_neg]
  rw [balancedLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    thetaTiltProb_absolutelyContinuous_volume ha (by simp),
    thetaTiltProb_absolutelyContinuous_volume habs (by simp)]
  simp

theorem thetaPair_contrastSymbol_ne_zero {a : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0) :
    ∀ᵐ x ∂balancedLaw (thetaPair ha).source (thetaPair ha).target,
      (thetaPair ha).contrastSymbol x ≠ 0 := by
  have hzero : ∀ᵐ x ∂balancedLaw (thetaPair ha).source (thetaPair ha).target, x ≠ 0 := by
    rw [thetaPair_balancedLaw ha, ae_iff]
    simpa using thetaPair_balancedLaw_singleton_zero ha
  filter_upwards [thetaPair_contrastSymbol_ae ha, hzero] with x hx hx0
  rw [hx]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  intro htan
  have hs : Real.sinh (a * x) = 0 := by
    have hc := Real.cosh_pos (a * x)
    rw [Real.tanh_eq_sinh_div_cosh] at htan
    rcases div_eq_zero_iff.mp htan with h1 | h1
    · exact h1
    · exact absurd h1 hc.ne'
  rw [Real.sinh_eq_zero] at hs
  rcases mul_eq_zero.mp hs with h1 | h1
  · exact ha0 h1
  · exact hx0 h1

/-- **Corollary 8.2 (5).**  Off the centre the contrast multiplier is injective. -/
theorem thetaPair_contrastOp_injective {a : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0) :
    Function.Injective (thetaPair ha).contrastOp :=
  lpBoundedMulCLM_injective_of_ae_ne_zero _ _ _ (thetaPair_contrastSymbol_ne_zero ha ha0)

/-- **Corollary 8.2 (5).**  Off the centre the contrast multiplier has dense range. -/
theorem thetaPair_contrastOp_denseRange {a : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0) :
    DenseRange (thetaPair ha).contrastOp :=
  denseRange_lpBoundedMulCLM_of_ae_ne_zero _ _ _ (thetaPair ha).conj_contrastSymbol
    (thetaPair_contrastSymbol_ne_zero ha ha0)

theorem thetaPair_contrastSymbol_small {a : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0) :
    ∀ c : ℝ, 0 < c → ∃ S : Set ℝ, MeasurableSet S ∧
      balancedLaw (thetaPair ha).source (thetaPair ha).target S ≠ 0 ∧
      balancedLaw (thetaPair ha).source (thetaPair ha).target S ≠ ∞ ∧
      ∀ᵐ x ∂balancedLaw (thetaPair ha).source (thetaPair ha).target,
        x ∈ S → ‖(thetaPair ha).contrastSymbol x‖ ≤ c := by
  intro c hc
  have habs : 0 < |a| := abs_pos.mpr ha0
  refine ⟨Set.Ioo (-(c / |a|)) (c / |a|), measurableSet_Ioo, ?_, ?_, ?_⟩
  · rw [thetaPair_balancedLaw ha]
    exact balancedLaw_thetaTilt_Ioo_ne_zero ha (by positivity)
  · haveI := (thetaPair ha).isProb
    exact measure_ne_top _ _
  · filter_upwards [thetaPair_contrastSymbol_ae ha] with x hx hmem
    rw [hx, Complex.norm_real, Real.norm_eq_abs]
    refine le_trans (abs_tanh_le_abs _) ?_
    rw [abs_mul]
    rw [Set.mem_Ioo] at hmem
    have hxabs : |x| ≤ c / |a| := abs_le.mpr ⟨hmem.1.le, hmem.2.le⟩
    calc |a| * |x| ≤ |a| * (c / |a|) := by nlinarith [habs, hxabs]
      _ = c := by field_simp

/-- **Corollary 8.2 (5).**  The dense injective contrast range is not closed: the positive theta
density meets every neighbourhood of the origin, so the likelihood gap vanishes. -/
theorem thetaPair_contrastOp_not_isClosed_range {a : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0) :
    ¬ IsClosed (Set.range (thetaPair ha).contrastOp) :=
  not_isClosed_range_lpBoundedMulCLM _ _ _ (thetaPair_contrastOp_injective ha ha0)
    (thetaPair_contrastSymbol_small ha ha0)

/-- **Corollary 8.2 (5), Theorem 7.1.**  The global coherence defect of the theta carrier has
dense nonclosed range at every noncentral tilt. -/
theorem thetaPair_coherenceDefect_not_isClosed_range {a : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0) :
    ¬ IsClosed (Set.range (thetaPair ha).juliaDatum.coherenceDefect) := by
  rw [LikelihoodJuliaDatum.isClosed_range_coherenceDefect_iff]
  exact thetaPair_contrastOp_not_isClosed_range ha ha0

/-! ## Item 3: exact centre selection by coherence of the two lift doctrines -/

theorem thetaPair_contrastOp_eq_zero (h0 : |(0 : ℝ)| ≤ 1) : (thetaPair h0).contrastOp = 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  have hzero : (thetaPair h0).contrastOp f = 0 := by
    refine Lp.ext ?_
    filter_upwards [(thetaPair h0).contrastOp_coeFn f, thetaPair_contrastSymbol_ae h0,
      Lp.coeFn_zero ℂ 2 (balancedLaw (thetaPair h0).source (thetaPair h0).target)] with x h1 h2 h3
    rw [h1, h2, h3]
    simp
  rw [zero_apply]
  exact hzero

theorem thetaPair_exists_ne_zero {a : ℝ} (ha : |a| ≤ 1) :
    ∃ f : Lp ℂ 2 (balancedLaw (thetaPair ha).source (thetaPair ha).target), f ≠ 0 := by
  haveI := (thetaPair ha).isProb
  haveI := (thetaPair ha).isProbabilityMeasure_target
  refine ⟨indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) (1 : ℂ), ?_⟩
  intro hzero
  have hnorm : ‖indicatorConstLp 2 MeasurableSet.univ
      (measure_ne_top (balancedLaw (thetaPair ha).source (thetaPair ha).target) Set.univ)
      (1 : ℂ)‖ = 1 := by
    haveI : IsProbabilityMeasure (balancedLaw (thetaPair ha).source (thetaPair ha).target) :=
      isProbabilityMeasure_balancedLaw _ _
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), measureReal_def, measure_univ]
    simp
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- **Corollary 8.2 (3).**  The sign-blind Julia extension and the polarized lift agree on the whole
canonical packet exactly at the critical centre. -/
theorem thetaPair_blindLift_eq_polarizedLift_iff {a : ℝ} (ha : |a| ≤ 1) :
    (∀ f, (thetaPair ha).juliaDatum.blindLift ((thetaPair ha).juliaDatum.dilation f)
        = (thetaPair ha).juliaDatum.polarizedLift ((thetaPair ha).juliaDatum.dilation f))
      ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha0
    obtain ⟨f, hf⟩ := thetaPair_exists_ne_zero ha
    have hc : (thetaPair ha).contrastOp f = 0 :=
      ((thetaPair ha).juliaDatum.blindLift_eq_polarizedLift_iff f).mp (h f)
    have hz : (thetaPair ha).contrastOp 0 = 0 := map_zero _
    exact hf (thetaPair_contrastOp_injective ha ha0 (hc.trans hz.symm))
  · rintro rfl
    intro f
    refine ((thetaPair ha).juliaDatum.blindLift_eq_polarizedLift_iff f).mpr ?_
    show (thetaPair ha).contrastOp f = 0
    rw [thetaPair_contrastOp_eq_zero ha]
    rfl

end

end RHTower
