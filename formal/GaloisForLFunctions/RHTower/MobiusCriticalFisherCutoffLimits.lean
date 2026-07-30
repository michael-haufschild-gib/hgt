import GaloisForLFunctions.RHTower.MobiusCriticalFisherCutoffWard
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Slope

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open ContinuousLinearMap

/-- Positive clock clipped at a finite window. -/
def positiveClockCap (u x : ℝ) : ℝ := min (max x 0) u

theorem continuous_positiveClockCap (u : ℝ) :
    Continuous (positiveClockCap u) :=
  (continuous_id.max continuous_const).min continuous_const

private theorem positiveClockCap_nonneg {u : ℝ} (hu : 0 ≤ u) (x : ℝ) :
    0 ≤ positiveClockCap u x := by
  unfold positiveClockCap
  exact le_min (le_max_right _ _) hu

private theorem positiveClockCap_le {u : ℝ} (x : ℝ) :
    positiveClockCap u x ≤ u := by
  exact min_le_right _ _

def positiveClockCapBCF (u : ℝ) (hu : 0 ≤ u) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨positiveClockCap u, continuous_positiveClockCap u⟩
    (2 * u)
    (fun x y => by
      rw [Real.dist_eq]
      have hx0 := positiveClockCap_nonneg hu x
      have hy0 := positiveClockCap_nonneg hu y
      have hxu := positiveClockCap_le (u := u) x
      have hyu := positiveClockCap_le (u := u) y
      calc
        |positiveClockCap u x - positiveClockCap u y| ≤
            |positiveClockCap u x| + |positiveClockCap u y| := abs_sub _ _
        _ = positiveClockCap u x + positiveClockCap u y := by
          rw [abs_of_nonneg hx0, abs_of_nonneg hy0]
        _ ≤ 2 * u := by linarith)

/-- Bounded continuous powers of the clipped positive clock. -/
def positiveClockCapPowBCF (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    BoundedContinuousFunction ℝ ℝ :=
  positiveClockCapBCF u hu ^ k

@[simp] theorem positiveClockCapPowBCF_apply
    (k : ℕ) (u : ℝ) (hu : 0 ≤ u) (x : ℝ) :
    positiveClockCapPowBCF k u hu x = positiveClockCap u x ^ k := by
  rfl

private theorem integrableOn_exp_neg_Ioi (u : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi u) := by
  simpa only [neg_mul, one_mul] using
    integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) u

private theorem integral_exp_neg_Ioi (u : ℝ) :
    (∫ x : ℝ in Ioi u, Real.exp (-x)) = Real.exp (-u) := by
  have h := integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) u
  simpa only [neg_mul, one_mul, neg_neg, div_neg, div_one] using h

private theorem intervalIntegral_id_mul_exp_neg (u : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..u, x * Real.exp (-x)) =
      1 - (u + 1) * Real.exp (-u) := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => -(y + 1) * Real.exp (-y))
      (x * Real.exp (-x)) x := by
    intro x
    have hraw := ((hasDerivAt_id x).add_const 1).neg.mul
      (hasDerivAt_id x).neg.exp
    have hclean : HasDerivAt _ (x * Real.exp (-x)) x :=
      hraw.congr_deriv (by
        simp only [Function.id_def, Pi.neg_apply]
        ring)
    simpa only [Function.id_def, Function.comp_apply, Pi.neg_apply,
      Pi.add_apply, Pi.mul_apply] using! hclean
  have hint : IntervalIntegrable (fun x : ℝ => x * Real.exp (-x)) volume 0 u :=
    (by fun_prop : Continuous (fun x : ℝ => x * Real.exp (-x))).intervalIntegrable 0 u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hderiv x) hint]
  norm_num
  ring

private theorem intervalIntegral_sq_mul_exp_neg (u : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..u, x ^ 2 * Real.exp (-x)) =
      2 - (u ^ 2 + 2 * u + 2) * Real.exp (-u) := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => -(y ^ 2 + 2 * y + 2) * Real.exp (-y))
      (x ^ 2 * Real.exp (-x)) x := by
    intro x
    have hraw := ((((hasDerivAt_id x).pow 2).add
      ((hasDerivAt_id x).const_mul 2)).add_const 2).neg.mul
        (hasDerivAt_id x).neg.exp
    have hclean : HasDerivAt _ (x ^ 2 * Real.exp (-x)) x :=
      hraw.congr_deriv (by
        simp only [Function.id_def, Pi.neg_apply, Pi.add_apply, Pi.pow_apply]
        ring)
    simpa only [Function.id_def, Function.comp_apply, Pi.neg_apply,
      Pi.add_apply, Pi.mul_apply, Pi.pow_apply] using! hclean
  have hint : IntervalIntegrable (fun x : ℝ => x ^ 2 * Real.exp (-x)) volume 0 u :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 2 * Real.exp (-x))).intervalIntegrable 0 u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hderiv x) hint]
  norm_num
  ring

private theorem integral_positiveClockCap_expMeasure
    {u : ℝ} (hu : 0 ≤ u) :
    (∫ x : ℝ, positiveClockCap u x
      ∂(mobiusCriticalExponentialProbabilityMeasure : Measure ℝ)) =
      1 - Real.exp (-u) := by
  unfold mobiusCriticalExponentialProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  unfold ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
  change (∫ x : ℝ, positiveClockCap u x
    ∂(volume.withDensity (ProbabilityTheory.exponentialPDF 1))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := ProbabilityTheory.exponentialPDF 1)
    (ProbabilityTheory.measurable_exponentialPDFReal 1).ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => by
      rw [ProbabilityTheory.exponentialPDF]
      exact ENNReal.ofReal_lt_top))]
  rw [show (fun x : ℝ =>
      (ProbabilityTheory.exponentialPDF 1 x).toReal • positiveClockCap u x) =
      (Ici 0).indicator (fun x : ℝ => min x u * Real.exp (-x)) by
    funext x
    rw [ProbabilityTheory.exponentialPDF_eq]
    by_cases hx : 0 ≤ x
    · have hxmem : x ∈ Ici (0 : ℝ) := hx
      rw [if_pos hx, indicator_of_mem hxmem]
      simp only [one_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
      rw [positiveClockCap, max_eq_left hx]
      ring
    · have hxmem : x ∉ Ici (0 : ℝ) := hx
      rw [if_neg hx, indicator_of_notMem hxmem]
      simp]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have hinterval : IntervalIntegrable (fun x : ℝ => min x u * Real.exp (-x))
      volume 0 u := by
    exact (by fun_prop : Continuous (fun x : ℝ => min x u * Real.exp (-x)))
      |>.intervalIntegrable 0 u
  have htail : IntegrableOn (fun x : ℝ => min x u * Real.exp (-x)) (Ioi u) := by
    refine ((integrableOn_exp_neg_Ioi u).const_mul u).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [min_eq_right hx.le]
  rw [← intervalIntegral.integral_interval_add_Ioi' hinterval htail]
  rw [show (∫ x : ℝ in (0 : ℝ)..u, min x u * Real.exp (-x)) =
      ∫ x : ℝ in (0 : ℝ)..u, x * Real.exp (-x) by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hu] at hx
    change min x u * Real.exp (-x) = x * Real.exp (-x)
    rw [min_eq_left hx.2]]
  rw [show (∫ x : ℝ in Ioi u, min x u * Real.exp (-x)) =
      u * ∫ x : ℝ in Ioi u, Real.exp (-x) by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change min x u * Real.exp (-x) = u * Real.exp (-x)
    rw [min_eq_right hx.le]]
  rw [intervalIntegral_id_mul_exp_neg u, integral_exp_neg_Ioi]
  ring

private theorem integral_positiveClockCap_sq_expMeasure
    {u : ℝ} (hu : 0 ≤ u) :
    (∫ x : ℝ, positiveClockCap u x ^ 2
      ∂(mobiusCriticalExponentialProbabilityMeasure : Measure ℝ)) =
      2 - 2 * (u + 1) * Real.exp (-u) := by
  unfold mobiusCriticalExponentialProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  unfold ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
  change (∫ x : ℝ, positiveClockCap u x ^ 2
    ∂(volume.withDensity (ProbabilityTheory.exponentialPDF 1))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := ProbabilityTheory.exponentialPDF 1)
    (ProbabilityTheory.measurable_exponentialPDFReal 1).ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => by
      rw [ProbabilityTheory.exponentialPDF]
      exact ENNReal.ofReal_lt_top))]
  rw [show (fun x : ℝ =>
      (ProbabilityTheory.exponentialPDF 1 x).toReal • positiveClockCap u x ^ 2) =
      (Ici 0).indicator (fun x : ℝ => min x u ^ 2 * Real.exp (-x)) by
    funext x
    rw [ProbabilityTheory.exponentialPDF_eq]
    by_cases hx : 0 ≤ x
    · have hxmem : x ∈ Ici (0 : ℝ) := hx
      rw [if_pos hx, indicator_of_mem hxmem]
      simp only [one_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
      rw [positiveClockCap, max_eq_left hx]
      ring
    · have hxmem : x ∉ Ici (0 : ℝ) := hx
      rw [if_neg hx, indicator_of_notMem hxmem]
      simp]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have hinterval : IntervalIntegrable (fun x : ℝ => min x u ^ 2 * Real.exp (-x))
      volume 0 u := by
    exact (by fun_prop : Continuous (fun x : ℝ => min x u ^ 2 * Real.exp (-x)))
      |>.intervalIntegrable 0 u
  have htail : IntegrableOn (fun x : ℝ => min x u ^ 2 * Real.exp (-x)) (Ioi u) := by
    refine ((integrableOn_exp_neg_Ioi u).const_mul (u ^ 2)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [min_eq_right hx.le]
  rw [← intervalIntegral.integral_interval_add_Ioi' hinterval htail]
  rw [show (∫ x : ℝ in (0 : ℝ)..u, min x u ^ 2 * Real.exp (-x)) =
      ∫ x : ℝ in (0 : ℝ)..u, x ^ 2 * Real.exp (-x) by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hu] at hx
    change min x u ^ 2 * Real.exp (-x) = x ^ 2 * Real.exp (-x)
    rw [min_eq_left hx.2]]
  rw [show (∫ x : ℝ in Ioi u, min x u ^ 2 * Real.exp (-x)) =
      u ^ 2 * ∫ x : ℝ in Ioi u, Real.exp (-x) by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change min x u ^ 2 * Real.exp (-x) = u ^ 2 * Real.exp (-x)
    rw [min_eq_right hx.le]]
  rw [intervalIntegral_sq_mul_exp_neg u, integral_exp_neg_Ioi]
  ring

/-- The `k`-th raw critical-clock moment below the hard window. -/
def squarefreeMobiusCriticalClockCutMoment (k : ℕ) (sigma u : ℝ) : ℝ :=
  ∑' n : ℕ, (squarefreeMobiusCriticalClockCut sigma u).indicator
    (fun n => squarefreeMobiusProbability sigma n *
      squarefreeMobiusCriticalClock sigma n ^ k) n

/-- The `k`-th moment of the positively clipped critical clock. -/
def squarefreeMobiusCriticalClockCappedMoment (k : ℕ) (sigma u : ℝ) : ℝ :=
  ∑' n : ℕ, squarefreeMobiusProbability sigma n *
    positiveClockCap u (squarefreeMobiusCriticalClock sigma n) ^ k

theorem integral_positiveClockCap_pow_squarefreeMobiusCriticalClock
    (k : ℕ) {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    (∫ y : ℝ, positiveClockCap u y ^ k
      ∂(squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)) =
      squarefreeMobiusCriticalClockCappedMoment k sigma u := by
  let p := squarefreeMobiusCriticalPMF sigma
  let Y := squarefreeMobiusCriticalClock sigma
  have hsource : Integrable (fun n : ℕ => positiveClockCap u (Y n) ^ k)
      p.toMeasure := by
    have hmap := BoundedContinuousFunction.integrable
      (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)
      (positiveClockCapPowBCF k u hu)
    rw [squarefreeMobiusCriticalClockProbabilityMeasure] at hmap
    exact (integrable_map_measure
      (positiveClockCapPowBCF k u hu).continuous.aestronglyMeasurable
      (Measurable.of_discrete.aemeasurable : AEMeasurable Y p.toMeasure)).1 hmap
  unfold squarefreeMobiusCriticalClockProbabilityMeasure
    squarefreeMobiusCriticalIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  have htarget : AEStronglyMeasurable
      (fun y : ℝ => positiveClockCap u y ^ k) (Measure.map Y p.toMeasure) := by
    simpa only [Pi.pow_apply] using!
      ((continuous_positiveClockCap u).pow k).aestronglyMeasurable
  rw [integral_map
    (Measurable.of_discrete.aemeasurable : AEMeasurable Y p.toMeasure)
    htarget]
  rw [PMF.integral_eq_tsum p _ hsource]
  simp only [smul_eq_mul, p, squarefreeMobiusCriticalPMF_toReal hsigma]
  rfl

private theorem summable_squarefreeMobiusCriticalClockMoment
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ => squarefreeMobiusProbability sigma n *
      squarefreeMobiusCriticalClock sigma n ^ k) := by
  have h := (summable_squarefreeMobiusLogMoment k hsigma).mul_left
    ((sigma - 1) ^ k)
  apply h.congr
  intro n
  unfold squarefreeMobiusCriticalClock
  rw [mul_pow]
  ring

/-- General cap--cut law: every capped moment is its raw hard-cut moment plus the constant
tail carried by the cap. -/
theorem squarefreeMobiusCriticalClockCappedMoment_eq_cutMoment_add_tail
    (k : ℕ) {sigma u : ℝ} (hsigma : 1 < sigma) :
    squarefreeMobiusCriticalClockCappedMoment k sigma u =
      squarefreeMobiusCriticalClockCutMoment k sigma u +
        u ^ k * (1 - squarefreeMobiusCriticalClockCutMass sigma u) := by
  let cut := squarefreeMobiusCriticalClockCut sigma u
  let p := squarefreeMobiusProbability sigma
  let Y := squarefreeMobiusCriticalClock sigma
  have hp : Summable p := summable_squarefreeMobiusProbability hsigma
  have hpCut : Summable (cut.indicator p) := hp.indicator cut
  have hY : Summable (fun n : ℕ => p n * Y n ^ k) :=
    summable_squarefreeMobiusCriticalClockMoment k hsigma
  have hYCut : Summable (cut.indicator (fun n : ℕ => p n * Y n ^ k)) :=
    hY.indicator cut
  have htail : Summable (fun n : ℕ => p n - cut.indicator p n) := hp.sub hpCut
  unfold squarefreeMobiusCriticalClockCappedMoment
  change (∑' n : ℕ, p n * positiveClockCap u (Y n) ^ k) = _
  calc
    _ = ∑' n : ℕ, (cut.indicator (fun j => p j * Y j ^ k) n +
        u ^ k * (p n - cut.indicator p n)) := by
      apply tsum_congr
      intro n
      have hYn : 0 ≤ Y n := by
        unfold Y squarefreeMobiusCriticalClock
        exact mul_nonneg (sub_nonneg.mpr hsigma.le)
          (Real.log_natCast_nonneg n)
      by_cases hn : n ∈ cut
      · have hYnu : Y n ≤ u := hn
        rw [indicator_of_mem hn, indicator_of_mem hn]
        rw [positiveClockCap, max_eq_left hYn, min_eq_left hYnu]
        ring
      · have huYn : u ≤ Y n := le_of_not_ge hn
        rw [indicator_of_notMem hn, indicator_of_notMem hn]
        rw [positiveClockCap, max_eq_left hYn, min_eq_right huYn]
        ring
    _ = (∑' n : ℕ, cut.indicator (fun j => p j * Y j ^ k) n) +
        (∑' n : ℕ, u ^ k * (p n - cut.indicator p n)) :=
      hYCut.tsum_add ((Summable.mul_left (u ^ k)) htail)
    _ = (∑' n : ℕ, cut.indicator (fun j => p j * Y j ^ k) n) +
        u ^ k * (∑' n : ℕ, (p n - cut.indicator p n)) := by
      rw [tsum_mul_left]
    _ = (∑' n : ℕ, cut.indicator (fun j => p j * Y j ^ k) n) +
        u ^ k * ((∑' n : ℕ, p n) - (∑' n : ℕ, cut.indicator p n)) := by
      rw [hp.tsum_sub hpCut]
    _ = squarefreeMobiusCriticalClockCutMoment k sigma u +
        u ^ k * (1 - squarefreeMobiusCriticalClockCutMass sigma u) := by
      rw [tsum_squarefreeMobiusProbability hsigma]
      rfl

/-- The clipped first critical-clock moment converges by the weak clock law alone. -/
theorem tendsto_squarefreeMobiusCriticalClockCappedMoment_one
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalClockCappedMoment 1 sigma u)
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - Real.exp (-u))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      tendsto_squarefreeMobiusCriticalClockProbabilityMeasure)
      (positiveClockCapBCF u hu)
  change Tendsto (fun sigma : ℝ =>
    ∫ y : ℝ, positiveClockCap u y
      ∂(squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ))
    (nhdsWithin 1 (Ioi 1))
    (nhds (∫ y : ℝ, positiveClockCap u y
      ∂(mobiusCriticalExponentialProbabilityMeasure : Measure ℝ))) at h
  rw [integral_positiveClockCap_expMeasure hu] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  simpa only [pow_one] using
    (integral_positiveClockCap_pow_squarefreeMobiusCriticalClock 1 hsigma hu)

/-- The clipped second critical-clock moment converges by the weak clock law alone. -/
theorem tendsto_squarefreeMobiusCriticalClockCappedMoment_two
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalClockCappedMoment 2 sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (2 - 2 * (u + 1) * Real.exp (-u))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      tendsto_squarefreeMobiusCriticalClockProbabilityMeasure)
      (positiveClockCapPowBCF 2 u hu)
  change Tendsto (fun sigma : ℝ =>
    ∫ y : ℝ, positiveClockCap u y ^ 2
      ∂(squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ))
    (nhdsWithin 1 (Ioi 1))
    (nhds (∫ y : ℝ, positiveClockCap u y ^ 2
      ∂(mobiusCriticalExponentialProbabilityMeasure : Measure ℝ))) at h
  rw [integral_positiveClockCap_sq_expMeasure hu] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  exact integral_positiveClockCap_pow_squarefreeMobiusCriticalClock 2 hsigma hu

/-- Exact hard-cut first-moment limit for the squarefree critical clock. -/
theorem tendsto_squarefreeMobiusCriticalClockCutMoment_one
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalClockCutMoment 1 sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (1 - (u + 1) * Real.exp (-u))) := by
  have hmass : Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalClockCutMass sigma u)
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - Real.exp (-u))) := by
    simpa only [if_pos hu] using tendsto_squarefreeMobiusCriticalClockCutMass u
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := tendsto_const_nhds
  have hu' : Tendsto (fun _ : ℝ => u)
      (nhdsWithin 1 (Ioi 1)) (nhds u) := tendsto_const_nhds
  have h := tendsto_squarefreeMobiusCriticalClockCappedMoment_one hu |>.sub
    (hu'.mul (hone.sub hmass))
  have hvalue :
      (1 - Real.exp (-u)) - u * (1 - (1 - Real.exp (-u))) =
        1 - (u + 1) * Real.exp (-u) := by
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  rw [squarefreeMobiusCriticalClockCappedMoment_eq_cutMoment_add_tail 1 hsigma]
  simp only [pow_one]
  ring

/-- Exact hard-cut second-moment limit for the squarefree critical clock. -/
theorem tendsto_squarefreeMobiusCriticalClockCutMoment_two
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalClockCutMoment 2 sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (2 - (u ^ 2 + 2 * u + 2) * Real.exp (-u))) := by
  have hmass : Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalClockCutMass sigma u)
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - Real.exp (-u))) := by
    simpa only [if_pos hu] using tendsto_squarefreeMobiusCriticalClockCutMass u
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := tendsto_const_nhds
  have hu' : Tendsto (fun _ : ℝ => u ^ 2)
      (nhdsWithin 1 (Ioi 1)) (nhds (u ^ 2)) := tendsto_const_nhds
  have h := tendsto_squarefreeMobiusCriticalClockCappedMoment_two hu |>.sub
    (hu'.mul (hone.sub hmass))
  have hvalue :
      (2 - 2 * (u + 1) * Real.exp (-u)) -
          u ^ 2 * (1 - (1 - Real.exp (-u))) =
        2 - (u ^ 2 + 2 * u + 2) * Real.exp (-u) := by
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  rw [squarefreeMobiusCriticalClockCappedMoment_eq_cutMoment_add_tail 2 hsigma]
  ring

/-- Summable weighted centering is determined by mass and first moment. -/
theorem tsum_weighted_centered
    {I : Type*} {w y : I → ℝ} (m : ℝ)
    (hw : Summable w) (hwy : Summable (fun i => w i * y i)) :
    (∑' i, w i * (y i - m)) =
      (∑' i, w i * y i) - m * ∑' i, w i := by
  calc
    _ = ∑' i, (w i * y i - m * w i) := by
      apply tsum_congr
      intro i
      ring
    _ = (∑' i, w i * y i) - (∑' i, m * w i) :=
      hwy.tsum_sub (hw.mul_left m)
    _ = _ := by rw [tsum_mul_left]

/-- Summable weighted quadratic centering is determined by its first three raw moments. -/
theorem tsum_weighted_centered_sq
    {I : Type*} {w y : I → ℝ} (m : ℝ)
    (hw : Summable w)
    (hwy : Summable (fun i => w i * y i))
    (hwy2 : Summable (fun i => w i * y i ^ 2)) :
    (∑' i, w i * (y i - m) ^ 2) =
      (∑' i, w i * y i ^ 2) -
        2 * m * (∑' i, w i * y i) + m ^ 2 * (∑' i, w i) := by
  have hlinear : Summable (fun i => (-2 * m) * (w i * y i)) :=
    hwy.mul_left (-2 * m)
  have hconstant : Summable (fun i => m ^ 2 * w i) :=
    hw.mul_left (m ^ 2)
  calc
    _ = ∑' i, ((w i * y i ^ 2 + (-2 * m) * (w i * y i)) +
        m ^ 2 * w i) := by
      apply tsum_congr
      intro i
      ring
    _ = (∑' i, (w i * y i ^ 2 + (-2 * m) * (w i * y i))) +
        (∑' i, m ^ 2 * w i) :=
      (hwy2.add hlinear).tsum_add hconstant
    _ = ((∑' i, w i * y i ^ 2) +
          (∑' i, (-2 * m) * (w i * y i))) +
        (∑' i, m ^ 2 * w i) := by
      rw [hwy2.tsum_add hlinear]
    _ = _ := by
      rw [tsum_mul_left, tsum_mul_left]
      ring

/-- The truncated Fisher overlap is exactly the centered hard-cut first moment. -/
theorem squarefreeMobiusCriticalFisherCutOverlap_eq_cutMoments
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    squarefreeMobiusCriticalFisherCutOverlap sigma u =
      -2 * (squarefreeMobiusCriticalClockCutMoment 1 sigma u -
        ((sigma - 1) * squarefreeMobiusLogMoment 1 sigma) *
          squarefreeMobiusCriticalClockCutMass sigma u) := by
  let cut := squarefreeMobiusCriticalClockCut sigma u
  let p := squarefreeMobiusProbability sigma
  let Y := squarefreeMobiusCriticalClock sigma
  let m := (sigma - 1) * squarefreeMobiusLogMoment 1 sigma
  let w := cut.indicator p
  have hw : Summable w :=
    (summable_squarefreeMobiusProbability hsigma).indicator cut
  have hYCut :=
    (summable_squarefreeMobiusCriticalClockMoment 1 hsigma).indicator cut
  have hwy : Summable (fun n => w n * Y n) := by
    apply hYCut.congr
    intro n
    by_cases hn : n ∈ cut <;> simp [w, p, Y, hn]
  have hM1 : (∑' n, w n * Y n) =
      squarefreeMobiusCriticalClockCutMoment 1 sigma u := by
    unfold squarefreeMobiusCriticalClockCutMoment
    apply tsum_congr
    intro n
    by_cases hn : n ∈ cut <;> simp [w, p, Y, cut, hn]
  have hmass : (∑' n, w n) =
      squarefreeMobiusCriticalClockCutMass sigma u := by
    rfl
  unfold squarefreeMobiusCriticalFisherCutOverlap
  calc
    (∑' n : ℕ, (squarefreeMobiusCriticalClockCut sigma u).indicator
        (fun n => -2 * (sigma - 1) * squarefreeMobiusProbability sigma n *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma)) n) =
        -2 * ∑' n : ℕ, w n * (Y n - m) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      by_cases hn : n ∈ cut
      · rw [indicator_of_mem hn]
        simp only [w, indicator_of_mem hn]
        unfold Y m squarefreeMobiusCriticalClock
        ring
      · rw [indicator_of_notMem hn]
        simp [w, hn]
    _ = -2 * ((∑' n, w n * Y n) - m * ∑' n, w n) := by
      rw [tsum_weighted_centered m hw hwy]
    _ = _ := by rw [hM1, hmass]

/-- The truncated Fisher energy is exactly the centered hard-cut second moment. -/
theorem squarefreeMobiusCriticalFisherCutEnergy_eq_cutMoments
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    squarefreeMobiusCriticalFisherCutEnergy sigma u =
      4 * (squarefreeMobiusCriticalClockCutMoment 2 sigma u -
        2 * ((sigma - 1) * squarefreeMobiusLogMoment 1 sigma) *
          squarefreeMobiusCriticalClockCutMoment 1 sigma u +
        ((sigma - 1) * squarefreeMobiusLogMoment 1 sigma) ^ 2 *
          squarefreeMobiusCriticalClockCutMass sigma u) := by
  let cut := squarefreeMobiusCriticalClockCut sigma u
  let p := squarefreeMobiusProbability sigma
  let Y := squarefreeMobiusCriticalClock sigma
  let m := (sigma - 1) * squarefreeMobiusLogMoment 1 sigma
  let w := cut.indicator p
  have hw : Summable w :=
    (summable_squarefreeMobiusProbability hsigma).indicator cut
  have hYCut :=
    (summable_squarefreeMobiusCriticalClockMoment 1 hsigma).indicator cut
  have hY2Cut :=
    (summable_squarefreeMobiusCriticalClockMoment 2 hsigma).indicator cut
  have hwy : Summable (fun n => w n * Y n) := by
    apply hYCut.congr
    intro n
    by_cases hn : n ∈ cut <;> simp [w, p, Y, hn]
  have hwy2 : Summable (fun n => w n * Y n ^ 2) := by
    apply hY2Cut.congr
    intro n
    by_cases hn : n ∈ cut <;> simp [w, p, Y, hn]
  have hM1 : (∑' n, w n * Y n) =
      squarefreeMobiusCriticalClockCutMoment 1 sigma u := by
    unfold squarefreeMobiusCriticalClockCutMoment
    apply tsum_congr
    intro n
    by_cases hn : n ∈ cut <;> simp [w, p, Y, cut, hn]
  have hM2 : (∑' n, w n * Y n ^ 2) =
      squarefreeMobiusCriticalClockCutMoment 2 sigma u := by
    unfold squarefreeMobiusCriticalClockCutMoment
    apply tsum_congr
    intro n
    by_cases hn : n ∈ cut <;> simp [w, p, Y, cut, hn]
  have hmass : (∑' n, w n) =
      squarefreeMobiusCriticalClockCutMass sigma u := by
    rfl
  unfold squarefreeMobiusCriticalFisherCutEnergy
  calc
    (∑' n : ℕ, (squarefreeMobiusCriticalClockCut sigma u).indicator
        (fun n => 4 * (sigma - 1) ^ 2 * squarefreeMobiusProbability sigma n *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma) ^ 2) n) =
        4 * ∑' n : ℕ, w n * (Y n - m) ^ 2 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      by_cases hn : n ∈ cut
      · rw [indicator_of_mem hn]
        simp only [w, indicator_of_mem hn]
        unfold Y m squarefreeMobiusCriticalClock
        ring
      · rw [indicator_of_notMem hn]
        simp [w, hn]
    _ = 4 * ((∑' n, w n * Y n ^ 2) -
        2 * m * (∑' n, w n * Y n) + m ^ 2 * (∑' n, w n)) := by
      rw [tsum_weighted_centered_sq m hw hwy hwy2]
    _ = _ := by rw [hM1, hM2, hmass]

/-- Exact critical limit of the real truncated state--tangent overlap. -/
theorem tendsto_squarefreeMobiusCriticalFisherCutOverlap
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalFisherCutOverlap sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (2 * u * Real.exp (-u))) := by
  have hmass : Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalClockCutMass sigma u)
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - Real.exp (-u))) := by
    simpa only [if_pos hu] using tendsto_squarefreeMobiusCriticalClockCutMass u
  have hfirst := tendsto_squarefreeMobiusCriticalClockCutMoment_one hu
  have hmean := tendsto_squarefreeMobiusLogMoment_one_critical
  have hnegTwo : Tendsto (fun _ : ℝ => (-2 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds (-2)) := tendsto_const_nhds
  have h := hnegTwo.mul (hfirst.sub (hmean.mul hmass))
  have hvalue :
      (-2 : ℝ) * ((1 - (u + 1) * Real.exp (-u)) -
        1 * (1 - Real.exp (-u))) = 2 * u * Real.exp (-u) := by
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  exact (squarefreeMobiusCriticalFisherCutOverlap_eq_cutMoments hsigma).symm

/-- Exact critical limit of the hard-cut Fisher tangent energy. -/
theorem tendsto_squarefreeMobiusCriticalFisherCutEnergy
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalFisherCutEnergy sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (4 * (1 - (1 + u ^ 2) * Real.exp (-u)))) := by
  have hmass : Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalClockCutMass sigma u)
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - Real.exp (-u))) := by
    simpa only [if_pos hu] using tendsto_squarefreeMobiusCriticalClockCutMass u
  have hfirst := tendsto_squarefreeMobiusCriticalClockCutMoment_one hu
  have hsecond := tendsto_squarefreeMobiusCriticalClockCutMoment_two hu
  have hmean := tendsto_squarefreeMobiusLogMoment_one_critical
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 2) := tendsto_const_nhds
  have hfour : Tendsto (fun _ : ℝ => (4 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 4) := tendsto_const_nhds
  have hcentered := hsecond.sub ((htwo.mul hmean).mul hfirst) |>.add
    ((hmean.pow 2).mul hmass)
  have h := hfour.mul hcentered
  have hvalue :
      (4 : ℝ) * ((2 - (u ^ 2 + 2 * u + 2) * Real.exp (-u)) -
        2 * 1 * (1 - (u + 1) * Real.exp (-u)) +
        1 ^ 2 * (1 - Real.exp (-u))) =
        4 * (1 - (1 + u ^ 2) * Real.exp (-u)) := by
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  exact (squarefreeMobiusCriticalFisherCutEnergy_eq_cutMoments hsigma).symm

/-- The completed finite-`sigma` hard-cutoff commutator energy, extended by zero outside the
strict Euler half-plane. -/
def squarefreeMobiusCriticalFisherCutoffCommutatorEnergy (sigma u : ℝ) : ℝ :=
  if hsigma : 1 < sigma then
    hsNormSq
      (cutoffCommutator (squarefreeMobiusCriticalClockCutoff sigma u)
        (pointedFisherConnection
          (infiniteMobiusSignedWeightLp sigma hsigma)
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma)))
  else 0

/-- The extended finite-`sigma` commutator energy is nonnegative everywhere. -/
theorem squarefreeMobiusCriticalFisherCutoffCommutatorEnergy_nonneg
    (sigma u : ℝ) :
    0 ≤ squarefreeMobiusCriticalFisherCutoffCommutatorEnergy sigma u := by
  rw [squarefreeMobiusCriticalFisherCutoffCommutatorEnergy]
  split_ifs
  · exact hsNormSq_nonneg _
  · exact le_rfl

/-- Exact value relation from the completed cutoff commutator to its four scalar Gram entries. -/
theorem squarefreeMobiusCriticalFisherCutoffCommutatorEnergy_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    squarefreeMobiusCriticalFisherCutoffCommutatorEnergy sigma u =
      (squarefreeMobiusCriticalProjectiveFisherEnergy sigma -
          squarefreeMobiusCriticalFisherCutEnergy sigma u) *
        squarefreeMobiusCriticalClockCutMass sigma u +
      (1 - squarefreeMobiusCriticalClockCutMass sigma u) *
        squarefreeMobiusCriticalFisherCutEnergy sigma u -
      2 * squarefreeMobiusCriticalFisherCutOverlap sigma u ^ 2 := by
  rw [squarefreeMobiusCriticalFisherCutoffCommutatorEnergy, dif_pos hsigma,
    hsNormSq_squarefreeMobiusCriticalFisherCutoffCommutator hsigma]

/-- Closed critical Ward profile selected by the squarefree exponential clock. -/
def squarefreeMobiusCriticalFisherCutoffWardLimit (u : ℝ) : ℝ :=
  4 * ((2 + u ^ 2) * Real.exp (-u) -
    2 * (1 + 2 * u ^ 2) * Real.exp (-2 * u))

/-- Scalar Gram form of the closed Ward profile. -/
theorem squarefreeMobiusCriticalFisherCutoffWardLimit_eq_gram (u : ℝ) :
    squarefreeMobiusCriticalFisherCutoffWardLimit u =
      (4 - 4 * (1 - (1 + u ^ 2) * Real.exp (-u))) *
          (1 - Real.exp (-u)) +
        Real.exp (-u) *
          (4 * (1 - (1 + u ^ 2) * Real.exp (-u))) -
        2 * (2 * u * Real.exp (-u)) ^ 2 := by
  have hexp : Real.exp (-2 * u) = Real.exp (-u) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold squarefreeMobiusCriticalFisherCutoffWardLimit
  rw [hexp]
  ring

/-- Exact critical limit of the completed hard-cutoff Fisher commutator energy. -/
theorem tendsto_squarefreeMobiusCriticalFisherCutoffCommutatorEnergy
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        squarefreeMobiusCriticalFisherCutoffCommutatorEnergy sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (squarefreeMobiusCriticalFisherCutoffWardLimit u)) := by
  have hmass : Tendsto
      (fun sigma : ℝ => squarefreeMobiusCriticalClockCutMass sigma u)
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - Real.exp (-u))) := by
    simpa only [if_pos hu] using tendsto_squarefreeMobiusCriticalClockCutMass u
  have htotal := tendsto_squarefreeMobiusCriticalProjectiveFisherEnergy
  have hcut := tendsto_squarefreeMobiusCriticalFisherCutEnergy hu
  have hoverlap := tendsto_squarefreeMobiusCriticalFisherCutOverlap hu
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 2) := tendsto_const_nhds
  have h := ((htotal.sub hcut).mul hmass).add
      ((hone.sub hmass).mul hcut) |>.sub
    (htwo.mul (hoverlap.pow 2))
  have hexp : Real.exp (-u) ^ 2 = Real.exp (-2 * u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hvalue :
      ((4 - 4 * (1 - (1 + u ^ 2) * Real.exp (-u))) *
          (1 - Real.exp (-u)) +
        (1 - (1 - Real.exp (-u))) *
          (4 * (1 - (1 + u ^ 2) * Real.exp (-u))) -
        2 * (2 * u * Real.exp (-u)) ^ 2) =
        squarefreeMobiusCriticalFisherCutoffWardLimit u := by
    unfold squarefreeMobiusCriticalFisherCutoffWardLimit
    rw [show Real.exp (-2 * u) = Real.exp (-u) ^ 2 from hexp.symm]
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  exact (squarefreeMobiusCriticalFisherCutoffCommutatorEnergy_eq hsigma).symm

/-- The closed critical Ward profile is nonnegative on every physical window. -/
theorem squarefreeMobiusCriticalFisherCutoffWardLimit_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ squarefreeMobiusCriticalFisherCutoffWardLimit u := by
  apply ge_of_tendsto
    (tendsto_squarefreeMobiusCriticalFisherCutoffCommutatorEnergy hu)
  exact Filter.Eventually.of_forall fun sigma =>
    squarefreeMobiusCriticalFisherCutoffCommutatorEnergy_nonneg sigma u

/-- **Global source Ward budget.**  The finite-window estimate from the paper in fact holds for
every nonnegative window, with no `u ≤ 2` restriction. -/
theorem squarefreeMobiusCriticalFisherCutoffWardLimit_le_eight_mul_CDF
    {u : ℝ} (hu : 0 ≤ u) :
    squarefreeMobiusCriticalFisherCutoffWardLimit u ≤
      8 * (1 - Real.exp (-u)) := by
  let a := 1 - Real.exp (-u)
  let b := 4 * (1 - (1 + u ^ 2) * Real.exp (-u))
  let c := 2 * u * Real.exp (-u)
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hb : 0 ≤ b := by
    apply ge_of_tendsto
      (tendsto_squarefreeMobiusCriticalFisherCutEnergy hu)
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact squarefreeMobiusCriticalFisherCutEnergy_nonneg hsigma
  have hba : b ≤ 4 * a := by
    dsimp only [a, b]
    nlinarith [mul_nonneg (sq_nonneg u) (Real.exp_pos (-u)).le]
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  rw [squarefreeMobiusCriticalFisherCutoffWardLimit_eq_gram]
  dsimp only [a, b, c] at ha hb hba hab hc ⊢
  nlinarith

/-- The Ward profile has the sharp four-unit one-sided boundary density after the native factor
two for the two commutator orientations. -/
theorem tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_two_mul :
    Tendsto
      (fun u : ℝ => squarefreeMobiusCriticalFisherCutoffWardLimit u / (2 * u))
      (nhdsWithin 0 (Ioi 0)) (nhds 4) := by
  have hderiv : HasDerivAt squarefreeMobiusCriticalFisherCutoffWardLimit 8 0 := by
    unfold squarefreeMobiusCriticalFisherCutoffWardLimit
    have hid := hasDerivAt_id (x := (0 : ℝ))
    have hleft := ((hid.pow 2).add_const 2).mul hid.neg.exp
    have hright := ((((hid.pow 2).const_mul 2).add_const 1).mul
      (hid.const_mul (-2)).exp).const_mul 2
    have hraw := (hleft.sub hright).const_mul 4
    have hclean : HasDerivAt _ (8 : ℝ) (0 : ℝ) :=
      hraw.congr_deriv (by norm_num [Function.id_def])
    simpa only [Function.id_def, Function.comp_apply, Pi.neg_apply,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, add_comm,
      neg_mul, mul_assoc] using! hclean
  have hslope := hderiv.tendsto_slope_zero_right
  have hhalf : Tendsto (fun _ : ℝ => (2 : ℝ)⁻¹)
      (nhdsWithin 0 (Ioi 0)) (nhds (2 : ℝ)⁻¹) := tendsto_const_nhds
  have h := hhalf.mul hslope
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [show squarefreeMobiusCriticalFisherCutoffWardLimit 0 = 0 by
    simp [squarefreeMobiusCriticalFisherCutoffWardLimit]]
  simp only [sub_zero]
  have hu' : 0 < u := hu
  field_simp [hu'.ne']

/-- The exponential clock CDF has unit one-sided boundary density. -/
theorem tendsto_mobiusCriticalExponentialCDF_div :
    Tendsto (fun u : ℝ => (1 - Real.exp (-u)) / u)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hderiv : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) 1 0 := by
    have hraw := (hasDerivAt_const (x := (0 : ℝ)) 1).sub
      (hasDerivAt_id (x := (0 : ℝ))).neg.exp
    simpa only [Function.id_def, Function.comp_apply, Pi.neg_apply,
      Pi.sub_apply] using!
        hraw.congr_deriv (by norm_num)
  have h := hderiv.tendsto_slope_zero_right
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : 0 < u := hu
  simp only [smul_eq_mul]
  norm_num
  field_simp [hu'.ne']

/-- The coefficient `8` in the global CDF budget is sharp at the clock boundary. -/
theorem tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_CDF :
    Tendsto
      (fun u : ℝ => squarefreeMobiusCriticalFisherCutoffWardLimit u /
        (1 - Real.exp (-u)))
      (nhdsWithin 0 (Ioi 0)) (nhds 8) := by
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds 2) := tendsto_const_nhds
  have hfactor := htwo.div tendsto_mobiusCriticalExponentialCDF_div (by norm_num)
  have h := tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_two_mul.mul
    hfactor
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : 0 < u := hu
  have hCDF : 1 - Real.exp (-u) ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  field_simp [hu'.ne', hCDF]

end RHTower
