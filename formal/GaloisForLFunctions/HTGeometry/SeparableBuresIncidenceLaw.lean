import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# Separable Bures incidence coupling

The sheet and target synthesis maps may be placed on one common measure
carrier.  Their incidence trace is then exactly the diagonal `L²` pairing.
Since operator trace is dominated by nuclear norm and the rectangular nuclear
norm is exactly operator Bures fidelity, every such coupling supplies a
dimension-free lower certificate for the Bures incidence capacity.

This is the bridge needed to pass complete-target incidence from finite
carriers to separable Hilbert spaces while retaining source sheets.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap MeasureTheory
open scoped ComplexConjugate ComplexOrder ENNReal InnerProductSpace

variable {X H : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Antilinearity of observer analysis in its observed field -/

theorem l2ObserverAnalysis_add (μ : Measure X) (u v : Lp H 2 μ) :
    l2ObserverAnalysis μ (u + v) =
      l2ObserverAnalysis μ u + l2ObserverAnalysis μ v := by
  ext q
  filter_upwards [l2ObserverAnalysis_coeFn μ (u + v) q,
    l2ObserverAnalysis_coeFn μ u q,
    l2ObserverAnalysis_coeFn μ v q,
    Lp.coeFn_add u v,
    Lp.coeFn_add (l2ObserverAnalysis μ u q)
      (l2ObserverAnalysis μ v q)] with x huv hu hv huvPoint hsum
  rw [ContinuousLinearMap.add_apply, huv, hsum, huvPoint]
  simp [hu, hv, inner_add_left]

theorem l2ObserverAnalysis_sub (μ : Measure X) (u v : Lp H 2 μ) :
    l2ObserverAnalysis μ (u - v) =
      l2ObserverAnalysis μ u - l2ObserverAnalysis μ v := by
  ext q
  filter_upwards [l2ObserverAnalysis_coeFn μ (u - v) q,
    l2ObserverAnalysis_coeFn μ u q,
    l2ObserverAnalysis_coeFn μ v q,
    Lp.coeFn_sub u v,
    Lp.coeFn_sub (l2ObserverAnalysis μ u q)
      (l2ObserverAnalysis μ v q)] with x huv hu hv huvPoint hsub
  rw [ContinuousLinearMap.sub_apply, huv, hsub, huvPoint]
  simp [hu, hv, inner_sub_left]

/-- Observer analysis is conjugate-linear in the observed `L²` field. -/
theorem l2ObserverAnalysis_smul (μ : Measure X) (c : ℂ) (u : Lp H 2 μ) :
    l2ObserverAnalysis μ (c • u) =
      star c • l2ObserverAnalysis μ u := by
  ext q
  filter_upwards [l2ObserverAnalysis_coeFn μ (c • u) q,
    l2ObserverAnalysis_coeFn μ u q,
    Lp.coeFn_smul c u,
    Lp.coeFn_smul (star c) (l2ObserverAnalysis μ u q)] with x hcu hu hcuPoint hsmul
  rw [ContinuousLinearMap.smul_apply, hcu, hsmul, hcuPoint]
  simp [hu, inner_smul_left]

/-! ## Exact cross-energy and trace identities -/

/-- The Hilbert--Schmidt pairing of two observer analyses is the reversed
`L²` inner product.  Thus the analysis embedding is an exact conjugate-linear
Hilbert-space embedding, not merely an energy inequality. -/
theorem hsInner_l2ObserverAnalysis_eq_inner
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u v : Lp H 2 μ) :
    hsInner (l2ObserverAnalysis μ u) (l2ObserverAnalysis μ v) =
      inner ℂ v u := by
  let U := l2ObserverAnalysis μ u
  let V := l2ObserverAnalysis μ v
  have hU : U.IsHilbertSchmidt := l2ObserverAnalysis_isHilbertSchmidt μ u
  have hV : V.IsHilbertSchmidt := l2ObserverAnalysis_isHilbertSchmidt μ v
  have hUVadd : U + V = l2ObserverAnalysis μ (u + v) := by
    exact (l2ObserverAnalysis_add μ u v).symm
  have hUVsub : U - V = l2ObserverAnalysis μ (u - v) := by
    exact (l2ObserverAnalysis_sub μ u v).symm
  have hIstar : star (RCLike.I : ℂ) = -(RCLike.I : ℂ) := by simp
  have hIsq : (RCLike.I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hI_mul_I : (RCLike.I : ℂ) * (RCLike.I : ℂ) = -1 := by
    simpa [pow_two] using hIsq
  have hnegI_mul_I : (-(RCLike.I : ℂ)) * (RCLike.I : ℂ) = 1 := by
    rw [neg_mul, hI_mul_I]
    simp
  have hminusI : U - (RCLike.I : ℂ) • V =
      l2ObserverAnalysis μ (u + (RCLike.I : ℂ) • v) := by
    rw [l2ObserverAnalysis_add, l2ObserverAnalysis_smul, hIstar]
    module <;> simp [hIsq]
  have hplusI : U + (RCLike.I : ℂ) • V =
      l2ObserverAnalysis μ (u - (RCLike.I : ℂ) • v) := by
    rw [l2ObserverAnalysis_sub, l2ObserverAnalysis_smul, hIstar]
    module <;> simp [hIsq]
  have hnormPlusI : ‖u + (RCLike.I : ℂ) • v‖ =
      ‖v - (RCLike.I : ℂ) • u‖ := by
    have heq : u + (RCLike.I : ℂ) • v =
        (RCLike.I : ℂ) • (v - (RCLike.I : ℂ) • u) := by
      rw [smul_sub, smul_smul, hI_mul_I]
      module
    rw [heq, norm_smul]
    simp
  have hnormMinusI : ‖u - (RCLike.I : ℂ) • v‖ =
      ‖v + (RCLike.I : ℂ) • u‖ := by
    have heq : u - (RCLike.I : ℂ) • v =
        (-(RCLike.I : ℂ)) • (v + (RCLike.I : ℂ) • u) := by
      rw [smul_add, smul_smul, hnegI_mul_I]
      module
    rw [heq, norm_smul]
    simp
  rw [hsInner_eq_tsum_basis hU hV (hsBasis ℂ H),
    tsum_inner_basis_polarization hU hV (hsBasis ℂ H),
    hUVadd, hUVsub, hminusI, hplusI,
    hsNormSq_l2ObserverAnalysis_eq_norm_sq,
    hsNormSq_l2ObserverAnalysis_eq_norm_sq,
    hsNormSq_l2ObserverAnalysis_eq_norm_sq,
    hsNormSq_l2ObserverAnalysis_eq_norm_sq,
    add_comm u v, norm_sub_rev u v, hnormPlusI, hnormMinusI]
  simpa only [map_pow] using
    (inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) v u).symm

/-- Cross covariance trace is exactly the `L²` overlap of its two vector
fields. -/
theorem opTrace_l2Synthesis_comp_observer_eq_inner
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u v : Lp H 2 μ) :
    opTrace (l2Synthesis μ v ∘L l2ObserverAnalysis μ u) =
      inner ℂ u v := by
  rw [opTrace_comp_eq_hsInner, adjoint_l2Synthesis,
    hsInner_l2ObserverAnalysis_eq_inner]

/-- On a common sheet carrier, the trace of the sheet--target incidence
operator is its diagonal source--target `L²` overlap. -/
theorem opTrace_l2SheetTargetIncidence_eq_inner
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u v : Lp H 2 μ) :
    opTrace (l2SheetTargetIncidence μ μ u v) = inner ℂ u v := by
  have hObs : (l2ObserverAnalysis μ u).IsHilbertSchmidt :=
    l2ObserverAnalysis_isHilbertSchmidt μ u
  have hSyn : (l2Synthesis μ v).IsHilbertSchmidt :=
    l2Synthesis_isHilbertSchmidt μ v
  rw [l2SheetTargetIncidence, sheetTargetIncidence,
    adjoint_l2Synthesis]
  calc
    opTrace (l2ObserverAnalysis μ u ∘L l2Synthesis μ v) =
        opTrace (l2Synthesis μ v ∘L l2ObserverAnalysis μ u) :=
      opTrace_comp_comm hObs hSyn
    _ = inner ℂ u v := opTrace_l2Synthesis_comp_observer_eq_inner μ u v

/-- **Diagonal coupling lower bound.**  The nuclear mass of a sheet--target
incidence operator dominates every common-carrier diagonal coupling. -/
theorem norm_inner_le_rectTraceNorm_l2SheetTargetIncidence
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u v : Lp H 2 μ) :
    ‖inner ℂ u v‖ ≤
      rectTraceNorm (Lp ℂ 2 μ) (Lp ℂ 2 μ)
        (l2SheetTargetIncidence μ μ u v) := by
  let K := l2SheetTargetIncidence μ μ u v
  have hK : MemSchattenClass 1 K := by
    rw [← memRectSchattenClass_iff_memSchattenClass]
    exact l2SheetTargetIncidence_memRectSchattenClass_one μ μ u v
  have htrace := norm_opTrace_le_traceNorm hK
  rw [opTrace_l2SheetTargetIncidence_eq_inner μ u v,
    ← rectTraceNorm_eq_traceNorm] at htrace
  exact htrace

/-- **Infinite diagonal coupling/Bures law.**  For arbitrary Bochner `L²`
fields on a separable Hilbert space, the absolute diagonal overlap is bounded
by the exact operator Bures root fidelity of their trace-class covariances. -/
theorem norm_inner_le_operatorBuresRootFidelity
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u v : Lp H 2 μ) :
    ‖inner ℂ u v‖ ≤
      operatorBuresRootFidelity
        (rangeCovariance (l2Synthesis μ u))
        (rangeCovariance (l2Synthesis μ v)) := by
  rw [← rectTraceNorm_l2SheetTargetIncidence_eq_operatorBuresRootFidelity
    μ μ u v]
  exact norm_inner_le_rectTraceNorm_l2SheetTargetIncidence μ u v

/-! ## Phase-corrected occupied-sheet designs -/

/-- Canonical phase which rotates a nonzero complex number to its nonnegative
real norm.  The zero value is assigned phase one. -/
def overlapPhase (c : ℂ) : ℂ :=
  if c = 0 then 1 else star c / (‖c‖ : ℂ)

theorem overlapPhase_measurable : Measurable overlapPhase := by
  unfold overlapPhase
  refine Measurable.ite (by simpa using measurableSet_singleton (0 : ℂ))
    measurable_const ?_
  exact continuous_star.measurable.div
    (Complex.measurable_ofReal.comp measurable_norm)

theorem overlapPhase_norm (c : ℂ) : ‖overlapPhase c‖ = 1 := by
  by_cases hc : c = 0
  · simp [overlapPhase, hc]
  · rw [overlapPhase, if_neg hc, norm_div, norm_star,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg c), div_self]
    exact norm_ne_zero_iff.mpr hc

theorem overlapPhase_mul (c : ℂ) :
    overlapPhase c * c = (‖c‖ : ℂ) := by
  by_cases hc : c = 0
  · simp [overlapPhase, hc]
  · rw [overlapPhase, if_neg hc, div_mul_eq_mul_div]
    change (starRingEnd ℂ) c * c / (‖c‖ : ℂ) = (‖c‖ : ℂ)
    rw [Complex.conj_mul']
    rw [pow_two, mul_div_cancel_left₀]
    exact_mod_cast norm_ne_zero_iff.mpr hc

/-- Phase correction preserves target norm and turns source--target overlap
into its nonnegative real magnitude. -/
theorem inner_overlapPhase_smul (u z : H) :
    inner ℂ u (overlapPhase (inner ℂ u z) • z) =
      (‖inner ℂ u z‖ : ℂ) := by
  rw [inner_smul_right, overlapPhase_mul]

/-- Measurability of pointwise phase correction. -/
theorem measurable_overlapPhase_smul
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    {u z : X → H} (hu : Measurable u) (hz : Measurable z) :
    Measurable (fun x ↦ overlapPhase (inner ℂ (u x) (z x)) • z x) := by
  exact (overlapPhase_measurable.comp
    (continuous_inner.measurable.comp (hu.prodMk hz))).smul hz

/-- The occupied, phase-corrected target field is `L²` on every finite
measure carrier whenever its target vectors lie in the unit ball. -/
theorem memLp_indicator_overlapPhase_smul
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ]
    {E : Set X} (hE : MeasurableSet E)
    {u z : X → H} (hu : Measurable u) (hz : Measurable z)
    (hzNorm : ∀ x ∈ E, ‖z x‖ ≤ 1) :
    MemLp (E.indicator
      (fun x ↦ overlapPhase (inner ℂ (u x) (z x)) • z x)) 2 μ := by
  refine MemLp.of_bound
    ((measurable_overlapPhase_smul hu hz).indicator hE).aestronglyMeasurable 1 ?_
  filter_upwards with x
  by_cases hx : x ∈ E
  · rw [Set.indicator_of_mem hx, norm_smul, overlapPhase_norm, one_mul]
    exact hzNorm x hx
  · simp [Set.indicator_of_notMem hx]

/-- **Separable occupied-sheet incidence lower law.**  A measurable unit
target selected on an occupied event can be phase-corrected and normalized
into one target design.  Its exact operator Bures incidence captures at least
the squared overlap threshold times occupied source mass.  No dimension,
rank, or sheet-count factor occurs. -/
theorem exists_phaseCorrected_design_operatorBuresRootFidelity_sq_lower
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ]
    {E : Set X} (hE : MeasurableSet E)
    {u z : X → H} (hu : Measurable u) (hz : Measurable z)
    (huLp : MemLp u 2 μ)
    (hzNorm : ∀ x ∈ E, ‖z x‖ ≤ 1)
    (a : ℝ) (ha : 0 ≤ a)
    (hcapture : ∀ x ∈ E, a ≤ ‖inner ℂ (u x) (z x)‖)
    (hEmass : 0 < μ.real E) :
    ∃ v : Lp H 2 μ,
      ‖v‖ ≤ 1 ∧
      a ^ 2 * μ.real E ≤
        operatorBuresRootFidelity
          (rangeCovariance (l2Synthesis μ (huLp.toLp u)))
          (rangeCovariance (l2Synthesis μ v)) ^ 2 := by
  let wfun : X → H := E.indicator
    (fun x ↦ overlapPhase (inner ℂ (u x) (z x)) • z x)
  have hwMem : MemLp wfun 2 μ := by
    exact memLp_indicator_overlapPhase_smul μ hE hu hz hzNorm
  let u2 : Lp H 2 μ := huLp.toLp u
  let w : Lp H 2 μ := hwMem.toLp wfun
  let m : ℝ := μ.real E
  let r : ℝ := Real.sqrt m
  have hm : 0 < m := hEmass
  have hr : 0 < r := Real.sqrt_pos.2 hm
  have hmEq : r ^ 2 = m := by
    exact Real.sq_sqrt hm.le
  have hwNormSq : ‖w‖ ^ 2 ≤ m := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    calc
      ∫ x, ‖w x‖ ^ 2 ∂μ ≤
          ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x ∂μ := by
        apply integral_mono_ae
        · exact (memLp_two_iff_integrable_sq_norm
            (Lp.aestronglyMeasurable w)).mp (Lp.memLp w)
        · exact (integrable_const (1 : ℝ)).indicator hE
        filter_upwards [hwMem.coeFn_toLp] with x hx
        rw [show w x = wfun x by exact hx]
        by_cases hxE : x ∈ E
        · simp only [wfun, Set.indicator_of_mem hxE, norm_smul,
            overlapPhase_norm, one_mul]
          nlinarith [hzNorm x hxE, norm_nonneg (z x)]
        · simp [wfun, Set.indicator_of_notMem hxE]
      _ = m := by simp [hE, m, measureReal_def]
  have hwNormLe : ‖w‖ ≤ r := by
    nlinarith [norm_nonneg w, Real.sqrt_nonneg m]
  let g : X → ℝ := E.indicator
    (fun x ↦ ‖inner ℂ (u x) (z x)‖)
  have hinnerEq : inner ℂ u2 w = (∫ x, g x ∂μ : ℝ) := by
    rw [MeasureTheory.L2.inner_def]
    calc
      ∫ x, inner ℂ (u2 x) (w x) ∂μ =
          ∫ x, (g x : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [huLp.coeFn_toLp, hwMem.coeFn_toLp] with x hux hwx
        rw [show u2 x = u x by exact hux, show w x = wfun x by exact hwx]
        by_cases hxE : x ∈ E
        · rw [show wfun x =
              overlapPhase (inner ℂ (u x) (z x)) • z x by
                simp [wfun, Set.indicator_of_mem hxE],
            inner_overlapPhase_smul]
          simp [g, Set.indicator_of_mem hxE]
        · simp [wfun, g, Set.indicator_of_notMem hxE]
      _ = (∫ x, g x ∂μ : ℝ) := integral_ofReal
  have hgIntegrable : Integrable g μ := by
    have hint : Integrable (fun x ↦ ‖inner ℂ (u2 x) (w x)‖) μ :=
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) u2 w).norm
    refine hint.congr ?_
    filter_upwards [huLp.coeFn_toLp, hwMem.coeFn_toLp] with x hux hwx
    rw [show u2 x = u x by exact hux, show w x = wfun x by exact hwx]
    by_cases hxE : x ∈ E
    · rw [show wfun x =
          overlapPhase (inner ℂ (u x) (z x)) • z x by
            simp [wfun, Set.indicator_of_mem hxE],
        inner_overlapPhase_smul]
      simp [g, Set.indicator_of_mem hxE]
    · simp [wfun, g, Set.indicator_of_notMem hxE]
  have hconstIntegrable : Integrable
      (E.indicator (fun _ : X ↦ a)) μ :=
    (integrable_const a).indicator hE
  have hgLower : a * m ≤ ∫ x, g x ∂μ := by
    calc
      a * m = ∫ x, E.indicator (fun _ : X ↦ a) x ∂μ := by
        simp [hE, m, measureReal_def, mul_comm]
      _ ≤ ∫ x, g x ∂μ := by
        apply integral_mono_ae hconstIntegrable hgIntegrable
        filter_upwards with x
        by_cases hxE : x ∈ E
        · simpa [g, Set.indicator_of_mem hxE] using hcapture x hxE
        · simp [g, Set.indicator_of_notMem hxE]
  have hgNonneg : 0 ≤ ∫ x, g x ∂μ :=
    (mul_nonneg ha hm.le).trans hgLower
  let v : Lp H 2 μ := ((r : ℂ)⁻¹) • w
  have hvNorm : ‖v‖ ≤ 1 := by
    rw [show v = ((r : ℂ)⁻¹) • w by rfl, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
    simpa [div_eq_inv_mul] using (div_le_one hr).2 hwNormLe
  have hoverlapNorm :
      ‖inner ℂ u2 v‖ = (∫ x, g x ∂μ) / r := by
    rw [show v = ((r : ℂ)⁻¹) • w by rfl, inner_smul_right,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le,
      hinnerEq, Complex.norm_real, Real.norm_of_nonneg hgNonneg,
      div_eq_inv_mul]
  have hoverlapLower : a * r ≤ ‖inner ℂ u2 v‖ := by
    rw [hoverlapNorm, le_div_iff₀ hr]
    nlinarith [hmEq]
  have hoverlapSq :
      a ^ 2 * m ≤ ‖inner ℂ u2 v‖ ^ 2 := by
    have hsq := pow_le_pow_left₀ (mul_nonneg ha hr.le) hoverlapLower 2
    rw [mul_pow, hmEq] at hsq
    exact hsq
  refine ⟨v, hvNorm, hoverlapSq.trans ?_⟩
  have hcouple := norm_inner_le_operatorBuresRootFidelity μ u2 v
  exact pow_le_pow_left₀ (norm_nonneg (inner ℂ u2 v)) hcouple 2

/-- Complete capture event for a countable family of targets. -/
def countableOverlapCaptureEvent
    (target : ℕ → H) (u : X → H) (a : ℝ) : Set X :=
  {x | ∃ n, a ≤ ‖inner ℂ (u x) (target n)‖}

/-- Countable complete capture is measurable; no finite-union premise is
needed. -/
theorem measurableSet_countableOverlapCaptureEvent
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (target : ℕ → H) {u : X → H} (hu : Measurable u) (a : ℝ) :
    MeasurableSet (countableOverlapCaptureEvent target u a) := by
  rw [show countableOverlapCaptureEvent target u a =
      ⋃ n, {x | a ≤ ‖inner ℂ (u x) (target n)‖} by
    ext x
    simp [countableOverlapCaptureEvent]]
  exact MeasurableSet.iUnion fun n ↦ measurableSet_le measurable_const
    (measurable_norm.comp
      (continuous_inner.measurable.comp (hu.prodMk measurable_const)))

/-- **Complete countable-union separable incidence law.**  A first-hit
measurable selector converts the entire countable target union into one
normalized phase-corrected design.  Hence the complete union costs no target
cardinality factor, even for infinitely many targets. -/
theorem exists_countable_complete_design_operatorBuresRootFidelity_sq_lower
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → H} (hu : Measurable u) (huLp : MemLp u 2 μ)
    (target : ℕ → H) (htargetNorm : ∀ n, ‖target n‖ ≤ 1)
    (a : ℝ) (ha : 0 ≤ a)
    (hEmass : 0 < μ.real (countableOverlapCaptureEvent target u a)) :
    ∃ v : Lp H 2 μ,
      ‖v‖ ≤ 1 ∧
      a ^ 2 * μ.real (countableOverlapCaptureEvent target u a) ≤
        operatorBuresRootFidelity
          (rangeCovariance (l2Synthesis μ (huLp.toLp u)))
          (rangeCovariance (l2Synthesis μ v)) ^ 2 := by
  classical
  let E : Set X := countableOverlapCaptureEvent target u a
  have hE : MeasurableSet E :=
    measurableSet_countableOverlapCaptureEvent target hu a
  let p : X → ℕ → Prop := fun x n ↦
    (x ∈ E ∧ a ≤ ‖inner ℂ (u x) (target n)‖) ∨
      (x ∉ E ∧ n = 0)
  have hp : ∀ x, ∃ n, p x n := by
    intro x
    by_cases hx : x ∈ E
    · have hxCapture : ∃ n, a ≤ ‖inner ℂ (u x) (target n)‖ := by
        simpa [E, countableOverlapCaptureEvent] using hx
      obtain ⟨n, hn⟩ := hxCapture
      exact ⟨n, Or.inl ⟨hx, hn⟩⟩
    · exact ⟨0, Or.inr ⟨hx, rfl⟩⟩
  have hpMeasurable : ∀ n, MeasurableSet {x | p x n} := by
    intro n
    apply MeasurableSet.union
    · exact hE.inter (measurableSet_le measurable_const
        (measurable_norm.comp
          (continuous_inner.measurable.comp (hu.prodMk measurable_const))))
    · exact hE.compl.inter (MeasurableSet.const (n = 0))
  let select : X → ℕ := fun x ↦ Nat.find (hp x)
  have hselect : Measurable select := measurable_find hp hpMeasurable
  let z : X → H := fun x ↦ target (select x)
  have hz : Measurable z :=
    (measurable_of_countable target).comp hselect
  have hzNorm : ∀ x ∈ E, ‖z x‖ ≤ 1 := by
    intro x hx
    exact htargetNorm (select x)
  have hcapture : ∀ x ∈ E, a ≤ ‖inner ℂ (u x) (z x)‖ := by
    intro x hx
    have hfound : p x (select x) := Nat.find_spec (hp x)
    rcases hfound with hgood | hbad
    · exact hgood.2
    · exact False.elim (hbad.1 hx)
  exact exists_phaseCorrected_design_operatorBuresRootFidelity_sq_lower
    μ hE hu hz huLp hzNorm a ha hcapture hEmass

/-! ## Compact target families without measurable argmax selection -/

/-- Complete capture by an arbitrary target set. -/
def setOverlapCaptureEvent
    (V : Set H) (u : X → H) (a : ℝ) : Set X :=
  {x | ∃ z ∈ V, a ≤ ‖inner ℂ (u x) z‖}

/-- **Compact complete-union separable incidence law.**  Let `V` be a
nonempty norm-compact subset of the closed unit ball.  At every positive
threshold slack `δ`, a fixed countable dense sequence in `V` captures the
entire `a`-event at threshold `a - δ`.  The countable first-hit law then
produces one normalized design, with no cardinality, dimension, rank, or
measurable-argmax loss.

The slack is the honest boundary cost of replacing a compact continuum by a
dense sequence.  It can be made arbitrarily small, which is the correct input
for taking the supremum over target probability designs. -/
theorem exists_compact_complete_design_operatorBuresRootFidelity_sq_lower
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → H} (hu : Measurable u) (huLp : MemLp u 2 μ)
    (V : Set H) (hVcompact : IsCompact V) (hVnonempty : V.Nonempty)
    (hVnorm : ∀ z ∈ V, ‖z‖ ≤ 1)
    (a δ : ℝ) (hδ : 0 < δ) (hδa : δ ≤ a)
    (hEmass : 0 < μ.real (setOverlapCaptureEvent V u a)) :
    ∃ v : Lp H 2 μ,
      ‖v‖ ≤ 1 ∧
      (a - δ) ^ 2 * μ.real (setOverlapCaptureEvent V u a) ≤
        operatorBuresRootFidelity
          (rangeCovariance (l2Synthesis μ (huLp.toLp u)))
          (rangeCovariance (l2Synthesis μ v)) ^ 2 := by
  classical
  letI : Nonempty V := hVnonempty.to_subtype
  letI : TopologicalSpace.SeparableSpace V :=
    hVcompact.isSeparable.separableSpace
  let target : ℕ → H := fun n ↦
    (TopologicalSpace.denseSeq V n : H)
  let Ecount : Set X :=
    countableOverlapCaptureEvent target u (a - δ)
  have htargetNorm : ∀ n, ‖target n‖ ≤ 1 := by
    intro n
    exact hVnorm _ (TopologicalSpace.denseSeq V n).property
  have hsubset : setOverlapCaptureEvent V u a ⊆ Ecount := by
    intro x hx
    obtain ⟨z, hzV, hz⟩ := hx
    let zV : V := ⟨z, hzV⟩
    let O : Set V :=
      {w | a - δ < ‖inner ℂ (u x) (w : H)‖}
    have hcontinuous : Continuous
        (fun w : V ↦ ‖inner ℂ (u x) (w : H)‖) :=
      continuous_norm.comp
        (continuous_inner.comp (continuous_const.prodMk continuous_subtype_val))
    have hOopen : IsOpen O := isOpen_lt continuous_const hcontinuous
    have hzO : zV ∈ O := by
      change a - δ < ‖inner ℂ (u x) z‖
      linarith
    obtain ⟨n, hn⟩ :=
      (TopologicalSpace.denseRange_denseSeq V).exists_mem_open hOopen ⟨zV, hzO⟩
    exact ⟨n, le_of_lt hn⟩
  have hmeasure :
      μ.real (setOverlapCaptureEvent V u a) ≤ μ.real Ecount :=
    measureReal_mono hsubset
  have hEcountMass : 0 < μ.real Ecount := hEmass.trans_le hmeasure
  obtain ⟨v, hvNorm, hvLower⟩ :=
    exists_countable_complete_design_operatorBuresRootFidelity_sq_lower
      μ hu huLp target htargetNorm (a - δ) (sub_nonneg.mpr hδa) hEcountMass
  refine ⟨v, hvNorm, ?_⟩
  exact (mul_le_mul_of_nonneg_left hmeasure (sq_nonneg (a - δ))).trans hvLower

end RHTower
