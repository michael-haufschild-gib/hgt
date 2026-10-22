import GaloisForLFunctions.RHTower.Suzuki.SuzukiSafeBoundaryThetaCumulantWall
import GaloisForLFunctions.HTGeometry.MomentHankelStrict

/-!
# The theta-carrier tilt family and its reflected work

The completed theta source is positive, even and exponentially decaying, so it carries an
exponential family on the whole open unit tilt interval.  Its log partition is even and strictly
convex, and the symmetric reflected work `4 a F'(a)` therefore vanishes exactly at the centre.
-/

open MeasureTheory Set Filter Real

namespace RHTower

noncomputable section

/-! ## Moments of the tilted theta source -/

/-- The raw moments of the theta source under the exponential tilt `a`. -/
def thetaTiltMoment (a : ℝ) (k : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ k * Real.exp (a * x) * thetaCuspFullSource x

theorem continuous_thetaTiltIntegrand (a : ℝ) (k : ℕ) :
    Continuous (fun x : ℝ => x ^ k * Real.exp (a * x) * thetaCuspFullSource x) :=
  ((continuous_id.pow k).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
    contDiff_thetaCuspFullSource.continuous

/-- The two-sided exponential majorant of the tilted integrand. -/
def thetaTiltBound (k : ℕ) (x : ℝ) : ℝ :=
  |x ^ k| * Real.exp x * thetaCuspFullSource x + |x ^ k| * Real.exp (-x) * thetaCuspFullSource x

theorem integrable_thetaTiltBound (k : ℕ) : Integrable (thetaTiltBound k) := by
  have h1 : Integrable (fun x : ℝ => |x ^ k| * Real.exp x * thetaCuspFullSource x) := by
    have hab := (integrable_pow_mul_exp_mul_thetaCuspFullSource k).abs
    refine hab.congr (Filter.Eventually.of_forall fun x => ?_)
    show |x ^ k * Real.exp x * thetaCuspFullSource x|
      = |x ^ k| * Real.exp x * thetaCuspFullSource x
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos x),
      abs_of_pos (thetaCuspFullSource_pos_all x)]
  have h2 : Integrable (fun x : ℝ => |x ^ k| * Real.exp (-x) * thetaCuspFullSource x) := by
    have hab := (integrable_pow_mul_exp_neg_mul_thetaCuspFullSource k).abs
    refine hab.congr (Filter.Eventually.of_forall fun x => ?_)
    show |x ^ k * Real.exp (-x) * thetaCuspFullSource x|
      = |x ^ k| * Real.exp (-x) * thetaCuspFullSource x
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-x)),
      abs_of_pos (thetaCuspFullSource_pos_all x)]
  exact h1.add h2

theorem norm_thetaTiltIntegrand_le {a : ℝ} (ha : |a| ≤ 1) (k : ℕ) (x : ℝ) :
    ‖x ^ k * Real.exp (a * x) * thetaCuspFullSource x‖ ≤ thetaTiltBound k x := by
  have hΦ : 0 < thetaCuspFullSource x := thetaCuspFullSource_pos_all x
  have hax : a * x ≤ |x| := by
    calc a * x ≤ |a * x| := le_abs_self _
      _ = |a| * |x| := abs_mul a x
      _ ≤ 1 * |x| := by
          have := abs_nonneg x
          nlinarith [ha, this]
      _ = |x| := one_mul _
  have hexp : Real.exp (a * x) ≤ Real.exp x + Real.exp (-x) := by
    refine le_trans (Real.exp_le_exp.2 hax) ?_
    rcases le_total (0 : ℝ) x with hx | hx
    · rw [abs_of_nonneg hx]
      linarith [Real.exp_pos (-x)]
    · rw [abs_of_nonpos hx]
      linarith [Real.exp_pos x]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hΦ,
    thetaTiltBound]
  have hk : (0 : ℝ) ≤ |x ^ k| := abs_nonneg _
  calc |x ^ k| * Real.exp (a * x) * thetaCuspFullSource x
      = (|x ^ k| * thetaCuspFullSource x) * Real.exp (a * x) := by ring
    _ ≤ (|x ^ k| * thetaCuspFullSource x) * (Real.exp x + Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hk hΦ.le)
    _ = |x ^ k| * Real.exp x * thetaCuspFullSource x
        + |x ^ k| * Real.exp (-x) * thetaCuspFullSource x := by ring

theorem integrable_thetaTiltIntegrand {a : ℝ} (ha : |a| ≤ 1) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (a * x) * thetaCuspFullSource x) := by
  refine (integrable_thetaTiltBound k).mono
    (continuous_thetaTiltIntegrand a k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  refine le_trans (norm_thetaTiltIntegrand_le ha k x) ?_
  exact le_abs_self _

/-! ## Differentiation in the tilt -/

theorem hasDerivAt_thetaTiltMoment {a : ℝ} (ha : |a| < 1) (k : ℕ) :
    HasDerivAt (fun t : ℝ => thetaTiltMoment t k) (thetaTiltMoment a (k + 1)) a := by
  set ε : ℝ := (1 - |a|) / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    linarith
  have hball : ∀ t ∈ Metric.ball a ε, |t| ≤ 1 := by
    intro t ht
    have : |t - a| < ε := by simpa [Real.dist_eq] using ht
    have habs : |t| - |a| ≤ |t - a| := abs_sub_abs_le_abs_sub t a
    linarith [habs, this, hεpos]
  have hmeas : ∀ᶠ t in nhds a,
      AEStronglyMeasurable
        (fun x : ℝ => x ^ k * Real.exp (t * x) * thetaCuspFullSource x) volume :=
    Filter.Eventually.of_forall fun t =>
      (continuous_thetaTiltIntegrand t k).aestronglyMeasurable
  have hint : Integrable (fun x : ℝ => x ^ k * Real.exp (a * x) * thetaCuspFullSource x) :=
    integrable_thetaTiltIntegrand ha.le k
  have hmeas' : AEStronglyMeasurable
      (fun x : ℝ => x ^ (k + 1) * Real.exp (a * x) * thetaCuspFullSource x) volume :=
    (continuous_thetaTiltIntegrand a (k + 1)).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ, ∀ t ∈ Metric.ball a ε,
      ‖x ^ (k + 1) * Real.exp (t * x) * thetaCuspFullSource x‖ ≤ thetaTiltBound (k + 1) x :=
    Filter.Eventually.of_forall fun x t ht =>
      norm_thetaTiltIntegrand_le (hball t ht) (k + 1) x
  have hdiff : ∀ᵐ x : ℝ, ∀ t ∈ Metric.ball a ε,
      HasDerivAt (fun t : ℝ => x ^ k * Real.exp (t * x) * thetaCuspFullSource x)
        (x ^ (k + 1) * Real.exp (t * x) * thetaCuspFullSource x) t := by
    refine Filter.Eventually.of_forall fun x t _ => ?_
    have hlin : HasDerivAt (fun t : ℝ => t * x) x t := by
      simpa using (hasDerivAt_id t).mul_const x
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (t * x)) (Real.exp (t * x) * x) t := hlin.exp
    have := ((hexp.const_mul (x ^ k)).mul_const (thetaCuspFullSource x))
    refine this.congr_deriv ?_
    ring
  have hnhds : Metric.ball a ε ∈ nhds a := Metric.ball_mem_nhds a hεpos
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun t x =>
      x ^ k * Real.exp (t * x) * thetaCuspFullSource x)
    (F' := fun t x => x ^ (k + 1) * Real.exp (t * x) * thetaCuspFullSource x)
    hnhds hmeas hint hmeas' hbound (integrable_thetaTiltBound (k + 1)) hdiff
  exact hres.2

/-! ## Positivity and evenness -/

theorem thetaTiltMoment_neg (a : ℝ) (k : ℕ) :
    thetaTiltMoment (-a) k = (-1) ^ k * thetaTiltMoment a k := by
  have hcomp := integral_neg_eq_self
    (fun x : ℝ => x ^ k * Real.exp (a * x) * thetaCuspFullSource x) volume
  have hstep : thetaTiltMoment (-a) k
      = ∫ x : ℝ, (-1 : ℝ) ^ k * ((-x) ^ k * Real.exp (a * -x) * thetaCuspFullSource (-x)) := by
    rw [thetaTiltMoment]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show x ^ k * Real.exp (-a * x) * thetaCuspFullSource x
      = (-1 : ℝ) ^ k * ((-x) ^ k * Real.exp (a * -x) * thetaCuspFullSource (-x))
    have hnx : ((-x) : ℝ) ^ k = (-1 : ℝ) ^ k * x ^ k := by
      rw [← neg_one_mul x, mul_pow]
    have hone : ((-1 : ℝ)) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    rw [thetaCuspFullSource_neg, hnx, show a * -x = -a * x by ring]
    calc x ^ k * Real.exp (-a * x) * thetaCuspFullSource x
        = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k)
            * (x ^ k * Real.exp (-a * x) * thetaCuspFullSource x) := by
          rw [hone, one_mul]
      _ = (-1 : ℝ) ^ k
            * ((-1 : ℝ) ^ k * x ^ k * Real.exp (-a * x) * thetaCuspFullSource x) := by ring
  rw [hstep, integral_const_mul, hcomp, thetaTiltMoment]

theorem thetaTiltMoment_zero_pos (a : ℝ) (ha : |a| ≤ 1) : 0 < thetaTiltMoment a 0 := by
  have hpos : ∀ x : ℝ, 0 < x ^ 0 * Real.exp (a * x) * thetaCuspFullSource x := by
    intro x
    have := thetaCuspFullSource_pos_all x
    positivity
  rw [thetaTiltMoment,
    integral_pos_iff_support_of_nonneg (fun x => (hpos x).le)
      (integrable_thetaTiltIntegrand ha 0)]
  have hsupp : (Function.support
      fun x : ℝ => x ^ 0 * Real.exp (a * x) * thetaCuspFullSource x) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hpos x).ne'
  rw [hsupp]
  simp

/-! ## The tilted measure and strict convexity -/

/-- The unnormalized tilted theta measure. -/
def thetaTiltMeasure (a : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (Real.exp (a * x) * thetaCuspFullSource x)

theorem measurable_thetaTiltDensity (a : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x) * thetaCuspFullSource x)) :=
  ENNReal.measurable_ofReal.comp
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      contDiff_thetaCuspFullSource.continuous)).measurable

theorem thetaTiltDensity_pos (a x : ℝ) : 0 < Real.exp (a * x) * thetaCuspFullSource x :=
  mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)

theorem integrable_pow_thetaTiltMeasure {a : ℝ} (ha : |a| ≤ 1) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (thetaTiltMeasure a) := by
  rw [thetaTiltMeasure,
    integrable_withDensity_iff_integrable_smul₀'
      (measurable_thetaTiltDensity a).aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (thetaTiltDensity_pos a _).le, smul_eq_mul]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using integrable_thetaTiltIntegrand ha k

theorem thetaTiltMoment_eq_integral_measure {a : ℝ} (k : ℕ) :
    thetaTiltMoment a k = ∫ x : ℝ, x ^ k ∂(thetaTiltMeasure a) := by
  rw [thetaTiltMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_thetaTiltDensity a)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (thetaTiltDensity_pos a _).le, smul_eq_mul]
  rw [thetaTiltMoment]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

theorem thetaTiltMeasure_compl_finset_pos (a : ℝ) (F : Finset ℝ) :
    0 < thetaTiltMeasure a {x : ℝ | x ∉ F} := by
  classical
  rw [pos_iff_ne_zero]
  intro hzero
  have hpos : ∀ᵐ x : ℝ ∂volume,
      ENNReal.ofReal (Real.exp (a * x) * thetaCuspFullSource x) ≠ 0 := by
    filter_upwards with x
    exact (ENNReal.ofReal_pos.mpr (thetaTiltDensity_pos a x)).ne'
  have hvolcomp : volume {x : ℝ | x ∉ F} = 0 :=
    (GaloisForLFunctions.HTGeometry.measure_withDensity_eq_zero_iff volume
      (measurable_thetaTiltDensity a) hpos _).mp hzero
  have hF : volume (↑F : Set ℝ) = 0 := F.measure_zero volume
  have huniv : (volume : Measure ℝ) Set.univ = 0 := by
    rw [show Set.univ = (↑F : Set ℝ) ∪ {x : ℝ | x ∉ F} by
      ext x
      exact ⟨fun _ => Classical.em (x ∈ F), fun _ => Set.mem_univ x⟩]
    exact measure_union_null hF hvolcomp
  simp at huniv

theorem det_thetaTilt_momentHankelMatrix_pos {a : ℝ} (ha : |a| ≤ 1) (n : ℕ) :
    0 < (HTGeometry.momentHankelMatrix (thetaTiltMoment a) n).det :=
  (HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
    (thetaTiltMoment a) (fun k => thetaTiltMoment_eq_integral_measure k)
    (fun k => integrable_pow_thetaTiltMeasure ha k)
    (thetaTiltMeasure_compl_finset_pos a) n).det_pos

/-- The tilted theta source has strictly positive moment discriminant. -/
theorem thetaTiltMoment_discriminant_pos {a : ℝ} (ha : |a| ≤ 1) :
    0 < thetaTiltMoment a 0 * thetaTiltMoment a 2 - thetaTiltMoment a 1 ^ 2 := by
  have hdet := det_thetaTilt_momentHankelMatrix_pos ha 2
  simpa [HTGeometry.momentHankelMatrix, Matrix.det_fin_two, pow_two]
    using hdet

/-! ## Log partition, mean and variance -/

/-- The log partition of the theta tilt family. -/
def thetaTiltLogPartition (a : ℝ) : ℝ := Real.log (thetaTiltMoment a 0)

/-- The mean of the normalized tilted theta law. -/
def thetaTiltMean (a : ℝ) : ℝ := thetaTiltMoment a 1 / thetaTiltMoment a 0

/-- The variance of the normalized tilted theta law. -/
def thetaTiltVariance (a : ℝ) : ℝ :=
  thetaTiltMoment a 2 / thetaTiltMoment a 0 - thetaTiltMean a ^ 2

theorem thetaTiltVariance_pos {a : ℝ} (ha : |a| ≤ 1) : 0 < thetaTiltVariance a := by
  have hdisc := thetaTiltMoment_discriminant_pos ha
  have h0 := thetaTiltMoment_zero_pos a ha
  rw [thetaTiltVariance, thetaTiltMean]
  rw [show thetaTiltMoment a 2 / thetaTiltMoment a 0
      - (thetaTiltMoment a 1 / thetaTiltMoment a 0) ^ 2
      = (thetaTiltMoment a 0 * thetaTiltMoment a 2 - thetaTiltMoment a 1 ^ 2)
        / thetaTiltMoment a 0 ^ 2 by field_simp [h0.ne']]
  positivity

/-- **(FEL.19).**  The first derivative of the log partition is the tilted mean. -/
theorem hasDerivAt_thetaTiltLogPartition {a : ℝ} (ha : |a| < 1) :
    HasDerivAt thetaTiltLogPartition (thetaTiltMean a) a := by
  have h0 := hasDerivAt_thetaTiltMoment ha 0
  have hpos := thetaTiltMoment_zero_pos a ha.le
  exact h0.log (ne_of_gt hpos)

/-- **(FEL.19).**  The second derivative of the log partition is the tilted variance. -/
theorem hasDerivAt_thetaTiltMean {a : ℝ} (ha : |a| < 1) :
    HasDerivAt thetaTiltMean (thetaTiltVariance a) a := by
  have h1 := hasDerivAt_thetaTiltMoment ha 1
  have h0 := hasDerivAt_thetaTiltMoment ha 0
  have hpos := thetaTiltMoment_zero_pos a ha.le
  have hdiv := h1.div h0 (ne_of_gt hpos)
  refine hdiv.congr_deriv ?_
  rw [thetaTiltVariance, thetaTiltMean]
  field_simp

/-! ## Evenness of the log partition -/

theorem thetaTiltMoment_zero_neg (a : ℝ) : thetaTiltMoment (-a) 0 = thetaTiltMoment a 0 := by
  simpa using thetaTiltMoment_neg a 0

theorem thetaTiltMoment_one_neg (a : ℝ) : thetaTiltMoment (-a) 1 = -thetaTiltMoment a 1 := by
  simpa using thetaTiltMoment_neg a 1

/-- **(FEL.11).**  The log partition is even. -/
theorem thetaTiltLogPartition_neg (a : ℝ) :
    thetaTiltLogPartition (-a) = thetaTiltLogPartition a := by
  rw [thetaTiltLogPartition, thetaTiltLogPartition, thetaTiltMoment_zero_neg]

theorem thetaTiltMean_neg (a : ℝ) : thetaTiltMean (-a) = -thetaTiltMean a := by
  rw [thetaTiltMean, thetaTiltMean, thetaTiltMoment_zero_neg, thetaTiltMoment_one_neg, neg_div]

theorem thetaTiltMean_zero : thetaTiltMean 0 = 0 := by
  have h := thetaTiltMean_neg 0
  simp only [neg_zero] at h
  linarith

/-! ## The exact reflected-work classification -/

theorem thetaTiltMean_pos_of_pos {a : ℝ} (h0 : 0 < a) (ha : a < 1) : 0 < thetaTiltMean a := by
  have hsub : ∀ x ∈ Set.Icc (0 : ℝ) a, |x| < 1 := by
    intro x hx
    rw [abs_lt]
    constructor <;> [linarith [hx.1]; linarith [hx.2]]
  have hcont : ContinuousOn thetaTiltMean (Set.Icc 0 a) := fun x hx =>
    (hasDerivAt_thetaTiltMean (hsub x hx)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) a,
      HasDerivAt thetaTiltMean (thetaTiltVariance x) x := fun x hx =>
    hasDerivAt_thetaTiltMean (hsub x ⟨hx.1.le, hx.2.le⟩)
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope thetaTiltMean thetaTiltVariance h0 hcont hderiv
  have hvar : 0 < thetaTiltVariance c := thetaTiltVariance_pos (le_of_lt (hsub c ⟨hc.1.le, hc.2.le⟩))
  rw [thetaTiltMean_zero, sub_zero, sub_zero] at hslope
  have : 0 < thetaTiltMean a / a := by rw [← hslope]; exact hvar
  exact (div_pos_iff_of_pos_right h0).1 this

/-- **(FEL.22)–(FEL.23).**  The symmetric reflected work of the theta carrier vanishes exactly at
the critical centre. -/
theorem thetaTiltReflectedWork_eq_zero_iff {a : ℝ} (ha : |a| < 1) :
    4 * a * thetaTiltMean a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra hne
    rcases lt_trichotomy a 0 with hlt | heq | hgt
    · have hpos : 0 < thetaTiltMean (-a) :=
        thetaTiltMean_pos_of_pos (by linarith) (by
          rw [abs_lt] at ha
          linarith [ha.1])
      rw [thetaTiltMean_neg] at hpos
      nlinarith [h, hpos, hlt]
    · exact hne heq
    · have hpos : 0 < thetaTiltMean a :=
        thetaTiltMean_pos_of_pos hgt (by
          rw [abs_lt] at ha
          linarith [ha.2])
      nlinarith [h, hpos, hgt]
  · rintro rfl
    rw [thetaTiltMean_zero]
    ring

/-- **(FEL.24).**  The directed reflected costs are equal at every tilt, so the functional-equation
action has zero information chirality. -/
theorem thetaTiltReflectedChirality_eq_zero (a : ℝ) :
    2 * a * thetaTiltMean a - 2 * (-a) * thetaTiltMean (-a) = 0 := by
  rw [thetaTiltMean_neg]
  ring

end

end RHTower
