import GaloisForLFunctions.HTGeometry.GibbsVariationalPrinciple

/-!
# The information projection onto an event

Among all probability laws carried by a fixed event, the conditioned law has the least relative
entropy against the ambient law, and that least value is the negative logarithm of the event's
mass.

The lower bound is the Gibbs bound applied to the potentials proportional to the indicator of the
event, whose partition functions interpolate between the total mass and the event mass; letting the
proportionality constant grow recovers the event's own logarithm.  Equality holds at the
conditioned law, whose density against the ambient law is the reciprocal mass on the event.
-/

open MeasureTheory Real Filter Topology ProbabilityTheory

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section InformationProjection

variable {α : Type*} [MeasurableSpace α]

theorem integrable_indicator_one_of_measurable (P : Measure α) [IsFiniteMeasure P] {E : Set α}
    (hE : MeasurableSet E) : Integrable (Set.indicator E (1 : α → ℝ)) P := by
  rw [integrable_indicator_iff hE]
  exact integrableOn_const (by simp [measure_ne_top])

/-- The density of the conditioned law against the ambient law is the reciprocal event mass on the
event and zero elsewhere. -/
theorem rnDeriv_cond_self (P : Measure α) [IsProbabilityMeasure P] {E : Set α}
    (hE : MeasurableSet E) :
    (P[|E]).rnDeriv P =ᵐ[P] fun x => (P E)⁻¹ * Set.indicator E (1 : α → ℝ≥0∞) x := by
  have hmeas : Measurable fun x => (P E)⁻¹ * Set.indicator E (1 : α → ℝ≥0∞) x :=
    (measurable_one.indicator hE).const_mul _
  have hcond : P[|E] = P.withDensity fun x => (P E)⁻¹ * Set.indicator E (1 : α → ℝ≥0∞) x := by
    rw [ProbabilityTheory.cond, ← withDensity_indicator_one hE,
      ← withDensity_smul _ (measurable_one.indicator hE)]
    rfl
  rw [hcond]
  exact Measure.rnDeriv_withDensity P hmeas

/-- The log-likelihood ratio of the conditioned law against the ambient law is the negative
logarithm of the event mass. -/
theorem llr_cond_self (P : Measure α) [IsProbabilityMeasure P] {E : Set α}
    (hE : MeasurableSet E) :
    llr (P[|E]) P =ᵐ[P[|E]] fun _ => -Real.log (P.real E) := by
  have hac : P[|E] ≪ P := ProbabilityTheory.cond_absolutelyContinuous
  filter_upwards [hac.ae_le (rnDeriv_cond_self P hE), ProbabilityTheory.ae_cond_mem hE]
    with x hx hxE
  rw [llr, hx, Set.indicator_of_mem hxE, Pi.one_apply, mul_one, ENNReal.toReal_inv,
    Real.log_inv, measureReal_def]

theorem integrable_llr_cond_self (P : Measure α) [IsProbabilityMeasure P] {E : Set α}
    (hE : MeasurableSet E) (hP : P E ≠ 0) : Integrable (llr (P[|E]) P) (P[|E]) := by
  have hprob : IsProbabilityMeasure (P[|E]) := ProbabilityTheory.cond_isProbabilityMeasure hP
  exact Integrable.congr (integrable_const (-Real.log (P.real E))) (llr_cond_self P hE).symm

/-- The relative entropy of the conditioned law against the ambient law is the negative logarithm
of the event mass. -/
theorem integral_llr_cond_self (P : Measure α) [IsProbabilityMeasure P] {E : Set α}
    (hE : MeasurableSet E) (hP : P E ≠ 0) :
    ∫ x, llr (P[|E]) P x ∂(P[|E]) = -Real.log (P.real E) := by
  have hprob : IsProbabilityMeasure (P[|E]) := ProbabilityTheory.cond_isProbabilityMeasure hP
  rw [integral_congr_ae (llr_cond_self P hE), integral_const]
  simp

/-- **Information-projection lower bound.**  Every law carried by the event has relative entropy at
least the negative logarithm of the event mass. -/
theorem le_integral_llr_of_measureReal_eq_one (P : Measure α) [IsProbabilityMeasure P]
    {E : Set α} (hE : MeasurableSet E) (hP : P E ≠ 0)
    {Q : Measure α} [IsProbabilityMeasure Q] (hQ : Q ≪ P) (hQE : Q.real E = 1)
    (hllr : Integrable (llr Q P) Q) :
    -Real.log (P.real E) ≤ ∫ x, llr Q P x ∂Q := by
  classical
  set p : ℝ := P.real E with hpdef
  have hp0 : 0 < p := ENNReal.toReal_pos hP (measure_ne_top _ _)
  have hp1 : p ≤ 1 := by
    rw [hpdef, measureReal_def, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have key : ∀ c : ℝ, 0 ≤ c → -Real.log (p + (1 - p) * Real.exp (-c)) ≤ ∫ x, llr Q P x ∂Q := by
    intro c hc
    have hindmeas : Measurable (Set.indicator E (1 : α → ℝ)) := measurable_one.indicator hE
    have hfmeas : Measurable fun x => c * Set.indicator E (1 : α → ℝ) x := hindmeas.const_mul c
    have hbound : ∀ x, c * Set.indicator E (1 : α → ℝ) x ≤ c := by
      intro x
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem hx, mul_zero]; exact hc
    have hnn : ∀ x, 0 ≤ c * Set.indicator E (1 : α → ℝ) x := by
      intro x
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]; exact hc
      · rw [Set.indicator_of_notMem hx, mul_zero]
    have hexp : Integrable (fun x => Real.exp (c * Set.indicator E (1 : α → ℝ) x)) P := by
      refine Integrable.of_bound hfmeas.exp.aestronglyMeasurable (Real.exp c) ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (hbound x)
    have hfq : Integrable (fun x => c * Set.indicator E (1 : α → ℝ) x) Q :=
      (integrable_indicator_one_of_measurable Q hE).const_mul c
    have hfP : Integrable (fun x => c * Set.indicator E (1 : α → ℝ) x) P :=
      (integrable_indicator_one_of_measurable P hE).const_mul c
    have hshift := llr_tilted_right Q P hexp hQ
    have hllr' : Integrable
        (llr Q (P.tilted fun x => c * Set.indicator E (1 : α → ℝ) x)) Q :=
      Integrable.congr ((hllr.sub hfq).add (integrable_const _)) hshift.symm
    have hg := neg_log_integral_exp_le_gibbsAction P hexp hQ hllr hfq hllr'
    have hfint : (∫ x, c * Set.indicator E (1 : α → ℝ) x ∂Q) = c := by
      rw [integral_const_mul, integral_indicator_one hE, hQE, mul_one]
    have hpt : ∀ x, Real.exp (c * Set.indicator E (1 : α → ℝ) x) =
        1 + (Real.exp c - 1) * Set.indicator E (1 : α → ℝ) x := by
      intro x
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, mul_one]; ring
      · rw [Set.indicator_of_notMem hx, mul_zero, mul_zero, Real.exp_zero, add_zero]
    have hZ : (∫ x, Real.exp (c * Set.indicator E (1 : α → ℝ) x) ∂P) =
        1 + (Real.exp c - 1) * p := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_add (integrable_const 1)
          ((integrable_indicator_one_of_measurable P hE).const_mul _),
        integral_const_mul, integral_indicator_one hE, integral_const]
      simp [hpdef]
    rw [gibbsAction, hfint, hZ] at hg
    have hpos : 0 < p + (1 - p) * Real.exp (-c) := by
      have : 0 ≤ (1 - p) * Real.exp (-c) := mul_nonneg (by linarith) (Real.exp_pos _).le
      linarith
    have hfactor : 1 + (Real.exp c - 1) * p = Real.exp c * (p + (1 - p) * Real.exp (-c)) := by
      rw [Real.exp_neg]
      field_simp
      ring
    rw [hfactor, Real.log_mul (Real.exp_pos c).ne' hpos.ne', Real.log_exp] at hg
    linarith
  have hinner : Tendsto (fun c : ℝ => p + (1 - p) * Real.exp (-c)) atTop (𝓝 p) := by
    have hz : Tendsto (fun c : ℝ => Real.exp (-c)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have := ((hz.const_mul (1 - p)).const_add p)
    simpa using this
  have hlog : Tendsto (fun c : ℝ => Real.log (p + (1 - p) * Real.exp (-c))) atTop
      (𝓝 (Real.log p)) := (Real.continuousAt_log hp0.ne').tendsto.comp hinner
  have hlim : Tendsto (fun c : ℝ => -Real.log (p + (1 - p) * Real.exp (-c))) atTop
      (𝓝 (-Real.log p)) := hlog.neg
  exact le_of_tendsto hlim
    (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc using key c hc)

/-- **Information projection onto an event.**  The negative logarithm of the mass of an event is
the least relative entropy of a probability law carried by that event, attained by the conditioned
law. -/
theorem isLeast_relativeEntropy_conditioned (P : Measure α) [IsProbabilityMeasure P]
    {E : Set α} (hE : MeasurableSet E) (hP : P E ≠ 0) :
    IsLeast {a : ℝ | ∃ Q : Measure α, ∃ _ : IsProbabilityMeasure Q, Q ≪ P ∧ Q.real E = 1 ∧
        Integrable (llr Q P) Q ∧ a = ∫ x, llr Q P x ∂Q}
      (-Real.log (P.real E)) := by
  have hprob : IsProbabilityMeasure (P[|E]) := ProbabilityTheory.cond_isProbabilityMeasure hP
  constructor
  · refine ⟨P[|E], hprob, ProbabilityTheory.cond_absolutelyContinuous, ?_,
      integrable_llr_cond_self P hE hP, (integral_llr_cond_self P hE hP).symm⟩
    rw [measureReal_def, ProbabilityTheory.cond_apply_self hP (measure_ne_top _ _)]
    simp
  · rintro a ⟨Q, hQprob, hQ, hQE, hllr, rfl⟩
    exact le_integral_llr_of_measureReal_eq_one P hE hP hQ hQE hllr

end InformationProjection

end

end GaloisForLFunctions.HTGeometry
