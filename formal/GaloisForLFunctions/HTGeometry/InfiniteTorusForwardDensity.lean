import GaloisForLFunctions.HTGeometry.InfiniteTorusEquidistribution
import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity
import GaloisForLFunctions.HTGeometry.BohrMeanValue

/-!
# Forward orbits of an infinite Kronecker flow are dense

One-sided time averages along the flow converge to the Haar mean, by the same route as the symmetric
ones: on a character the average is the elementary one-sided mean of a phase, which the corpus
computes, and the characters span a dense subalgebra of the continuous functions.

A continuous nonnegative function vanishing on the closure of a forward orbit therefore has zero
Haar mean, so it vanishes identically.  Since Haar measure is positive on nonempty open sets, no
point escapes the closure: every forward orbit is dense, and by additivity of the flow so is every
tail of the orbit.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- One-sided time average of a continuous torus function along the phase flow. -/
def forwardFlowAverage (omega : ι → ℝ) (T : ℝ) (f : C(UnitAddTorus ι, ℂ)) : ℂ :=
  windowAverage (fun t => f (clockPhasePoint omega t)) T

theorem forwardFlowAverage_torusCharacter (omega : ι → ℝ) (n : ι →₀ ℤ) (T : ℝ) :
    forwardFlowAverage omega T (torusCharacter n)
      = windowAverage (expChar (characterDetuning n omega)) T := by
  rw [forwardFlowAverage]
  congr 1
  funext t
  rw [torusCharacter_clockPhasePoint, expChar]
  congr 2
  ring

/-- **The one-sided average of a character converges to its Haar mean.** -/
theorem tendsto_forwardFlowAverage_torusCharacter [Countable ι] [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) (n : ι →₀ ℤ) :
    Tendsto (fun T => forwardFlowAverage omega T (torusCharacter n)) atTop
      (nhds (∫ x, torusCharacter n x ∂(torusHaar ι))) := by
  classical
  have hfun : (fun T => forwardFlowAverage omega T (torusCharacter n))
      = fun T => windowAverage (expChar (characterDetuning n omega)) T :=
    funext fun T => forwardFlowAverage_torusCharacter omega n T
  rw [hfun, integral_torusCharacter]
  have hlim := tendsto_windowAverage_bohrMean (continuous_expChar (characterDetuning n omega))
    (isBohrAlmostPeriodic_expChar (characterDetuning n omega))
  rw [bohrMean_expChar] at hlim
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    rwa [if_pos (characterDetuning_zero omega)] at hlim
  · rw [if_neg hn]
    rwa [if_neg (fun hcon => hn ((characterDetuning_eq_zero_iff h n).mp hcon))] at hlim

theorem forwardFlowAverage_add (omega : ι → ℝ) (T : ℝ) (f g : C(UnitAddTorus ι, ℂ)) :
    forwardFlowAverage omega T (f + g)
      = forwardFlowAverage omega T f + forwardFlowAverage omega T g := by
  rw [forwardFlowAverage, forwardFlowAverage, forwardFlowAverage, windowAverage, windowAverage,
    windowAverage, ← smul_add]
  congr 1
  rw [← intervalIntegral.integral_add (intervalIntegrable_flow omega f 0 T)
    (intervalIntegrable_flow omega g 0 T)]
  rfl

theorem forwardFlowAverage_smul (omega : ι → ℝ) (T : ℝ) (c : ℂ) (f : C(UnitAddTorus ι, ℂ)) :
    forwardFlowAverage omega T (c • f) = c * forwardFlowAverage omega T f := by
  rw [forwardFlowAverage, forwardFlowAverage, windowAverage, windowAverage]
  rw [show (fun t => (c • f) (clockPhasePoint omega t))
      = fun t => c • f (clockPhasePoint omega t) from rfl]
  rw [intervalIntegral.integral_smul, smul_comm, smul_eq_mul]

theorem forwardFlowAverage_sub (omega : ι → ℝ) (T : ℝ) (f g : C(UnitAddTorus ι, ℂ)) :
    forwardFlowAverage omega T (f - g)
      = forwardFlowAverage omega T f - forwardFlowAverage omega T g := by
  have hsub : f - g = f + (-1 : ℂ) • g := by
    ext x
    simp [sub_eq_add_neg]
  rw [hsub, forwardFlowAverage_add, forwardFlowAverage_smul]
  ring

theorem norm_forwardFlowAverage_le (omega : ι → ℝ) {T : ℝ} (hT : 0 < T)
    (f : C(UnitAddTorus ι, ℂ)) : ‖forwardFlowAverage omega T f‖ ≤ ‖f‖ := by
  have hbound : ‖∫ t in (0 : ℝ)..T, f (clockPhasePoint omega t)‖ ≤ ‖f‖ * T := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)
      (C := ‖f‖) (f := fun t => f (clockPhasePoint omega t)) (fun t _ => f.norm_coe_le_norm _)
    rwa [sub_zero, abs_of_pos hT] at hb
  rw [forwardFlowAverage, windowAverage, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hT.le)]
  rw [inv_mul_le_iff₀ hT]
  calc ‖∫ t in (0 : ℝ)..T, f (clockPhasePoint omega t)‖ ≤ ‖f‖ * T := hbound
    _ = T * ‖f‖ := by ring

/-- Functions whose one-sided time average converges to their Haar mean. -/
def HasHaarForwardAverage [Countable ι] (omega : ι → ℝ) (f : C(UnitAddTorus ι, ℂ)) : Prop :=
  Tendsto (fun T => forwardFlowAverage omega T f) atTop (nhds (∫ x, f x ∂(torusHaar ι)))

theorem hasHaarForwardAverage_add [Countable ι] {omega : ι → ℝ} {f g : C(UnitAddTorus ι, ℂ)}
    (hf : HasHaarForwardAverage omega f) (hg : HasHaarForwardAverage omega g) :
    HasHaarForwardAverage omega (f + g) := by
  have hint : (∫ x, (f + g) x ∂(torusHaar ι))
      = (∫ x, f x ∂(torusHaar ι)) + ∫ x, g x ∂(torusHaar ι) := by
    rw [← MeasureTheory.integral_add (integrable_continuousMap f) (integrable_continuousMap g)]
    rfl
  unfold HasHaarForwardAverage
  rw [hint]
  refine (hf.add hg).congr fun T => ?_
  exact (forwardFlowAverage_add omega T f g).symm

theorem hasHaarForwardAverage_smul [Countable ι] {omega : ι → ℝ} (c : ℂ)
    {f : C(UnitAddTorus ι, ℂ)} (hf : HasHaarForwardAverage omega f) :
    HasHaarForwardAverage omega (c • f) := by
  have hint : (∫ x, (c • f) x ∂(torusHaar ι)) = c * ∫ x, f x ∂(torusHaar ι) := by
    rw [← MeasureTheory.integral_const_mul]
    rfl
  unfold HasHaarForwardAverage
  rw [hint]
  refine (hf.const_mul c).congr fun T => ?_
  exact (forwardFlowAverage_smul omega T c f).symm

theorem hasHaarForwardAverage_zero [Countable ι] (omega : ι → ℝ) :
    HasHaarForwardAverage omega (0 : C(UnitAddTorus ι, ℂ)) := by
  unfold HasHaarForwardAverage
  have hint : (∫ x, (0 : C(UnitAddTorus ι, ℂ)) x ∂(torusHaar ι)) = 0 := by simp
  rw [hint]
  refine tendsto_const_nhds.congr fun T => ?_
  rw [forwardFlowAverage, windowAverage]
  simp

theorem hasHaarForwardAverage_of_mem_span [Countable ι] [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) {f : C(UnitAddTorus ι, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (torusCharacter (ι := ι)))) :
    HasHaarForwardAverage omega f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      exact tendsto_forwardFlowAverage_torusCharacter h n
  | zero => exact hasHaarForwardAverage_zero omega
  | add x y _ _ hx hy => exact hasHaarForwardAverage_add hx hy
  | smul c x _ hx => exact hasHaarForwardAverage_smul c hx

/-- **One-sided unique ergodicity.**  Along a rationally independent phase flow the one-sided time
average of every continuous function converges to its Haar mean. -/
theorem hasHaarForwardAverage_of_continuous [Countable ι] [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) (f : C(UnitAddTorus ι, ℂ)) :
    HasHaarForwardAverage omega f := by
  classical
  rw [HasHaarForwardAverage, Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  have hmem : f ∈ (Submodule.span ℂ (Set.range (torusCharacter (ι := ι)))).topologicalClosure := by
    rw [span_torusCharacter_closure_eq_top ι]
    exact Submodule.mem_top
  obtain ⟨g, hgspan, hgclose⟩ : ∃ g ∈ Submodule.span ℂ (Set.range (torusCharacter (ι := ι))),
      dist f g < ε / 3 := by
    obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hmem (ε / 3) hε3
    exact ⟨g, hg, hdist⟩
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp
    (hasHaarForwardAverage_of_mem_span h hgspan) (ε / 3) hε3
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right T₀ 1) hT)
  have hT₀le : T₀ ≤ T := le_trans (le_max_left T₀ 1) hT
  have hdiff : dist (forwardFlowAverage omega T f) (forwardFlowAverage omega T g) < ε / 3 := by
    rw [dist_eq_norm, ← forwardFlowAverage_sub]
    calc ‖forwardFlowAverage omega T (f - g)‖ ≤ ‖f - g‖ := norm_forwardFlowAverage_le omega hTpos _
      _ = dist f g := (dist_eq_norm f g).symm
      _ < ε / 3 := hgclose
  have hint : dist (∫ x, g x ∂(torusHaar ι)) (∫ x, f x ∂(torusHaar ι)) < ε / 3 := by
    rw [dist_eq_norm, ← MeasureTheory.integral_sub (integrable_continuousMap g)
      (integrable_continuousMap f)]
    have hbound : ‖∫ x, (g x - f x) ∂(torusHaar ι)‖ ≤ ‖g - f‖ * (torusHaar ι).real Set.univ := by
      refine MeasureTheory.norm_integral_le_of_norm_le_const ?_
      exact Filter.Eventually.of_forall fun x => (g - f).norm_coe_le_norm x
    rw [MeasureTheory.probReal_univ, mul_one] at hbound
    calc ‖∫ x, (g x - f x) ∂(torusHaar ι)‖ ≤ ‖g - f‖ := hbound
      _ = dist g f := (dist_eq_norm g f).symm
      _ = dist f g := dist_comm g f
      _ < ε / 3 := hgclose
  calc dist (forwardFlowAverage omega T f) (∫ x, f x ∂(torusHaar ι))
      ≤ dist (forwardFlowAverage omega T f) (forwardFlowAverage omega T g)
        + dist (forwardFlowAverage omega T g) (∫ x, f x ∂(torusHaar ι)) := dist_triangle _ _ _
    _ ≤ dist (forwardFlowAverage omega T f) (forwardFlowAverage omega T g)
        + (dist (forwardFlowAverage omega T g) (∫ x, g x ∂(torusHaar ι))
          + dist (∫ x, g x ∂(torusHaar ι)) (∫ x, f x ∂(torusHaar ι))) := by
        gcongr
        exact dist_triangle _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by
        gcongr
        exact hT₀ T hT₀le
    _ = ε := by ring


/-! ## Forward density -/

/-- A nonnegative continuous function which is positive somewhere has positive Haar mean. -/
theorem integral_pos_of_torusHaar [Countable ι] {f : C(UnitAddTorus ι, ℝ)} (hf : ∀ x, 0 ≤ f x)
    {x₀ : UnitAddTorus ι} (hx₀ : 0 < f x₀) :
    0 < ∫ x, f x ∂(torusHaar ι) := by
  have hint : MeasureTheory.Integrable (fun x => f x) (torusHaar ι) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun x => hf x) hint]
  have hopen : IsOpen {x : UnitAddTorus ι | 0 < f x} := isOpen_lt continuous_const f.continuous
  have hsub : {x : UnitAddTorus ι | 0 < f x} ⊆ Function.support fun x => f x :=
    fun x hx => ne_of_gt hx
  exact lt_of_lt_of_le (hopen.measure_pos _ ⟨x₀, hx₀⟩) (measure_mono hsub)

/-- **Forward orbits of a rationally independent flow are dense.** -/
theorem dense_forwardOrbit_zero [Countable ι] [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) :
    Dense {x : UnitAddTorus ι | ∃ t : ℝ, 0 ≤ t ∧ clockPhasePoint omega t = x} := by
  classical
  by_contra hnd
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : UnitAddTorus ι,
      x₀ ∉ closure {x : UnitAddTorus ι | ∃ t : ℝ, 0 ≤ t ∧ clockPhasePoint omega t = x} := by
    by_contra hcon
    exact hnd fun x => not_not.mp fun hx => hcon ⟨x, hx⟩
  obtain ⟨f, hf0, hf1, hfIcc⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_closure (s := {x : UnitAddTorus ι | ∃ t : ℝ, 0 ≤ t ∧ clockPhasePoint omega t = x}))
    (isClosed_singleton (x := x₀)) (Set.disjoint_singleton_right.mpr hx₀)
  set F : C(UnitAddTorus ι, ℂ) := ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp
    f.continuous⟩ with hF
  have hvanish : ∀ t : ℝ, 0 ≤ t → F (clockPhasePoint omega t) = 0 := by
    intro t ht
    have hmem : clockPhasePoint omega t ∈
        closure {x : UnitAddTorus ι | ∃ s : ℝ, 0 ≤ s ∧ clockPhasePoint omega s = x} :=
      subset_closure ⟨t, ht, rfl⟩
    have := hf0 hmem
    simp [hF, this]
  have hzeroAvg : ∀ T : ℝ, 0 < T → forwardFlowAverage omega T F = 0 := by
    intro T hT
    rw [forwardFlowAverage, windowAverage]
    have hcongr : (∫ t in (0 : ℝ)..T, F (clockPhasePoint omega t)) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) ?_]
      · simp
      · intro t ht
        refine hvanish t ?_
        rcases le_total (0 : ℝ) T with hT' | hT'
        · exact (Set.uIcc_of_le hT' ▸ ht : t ∈ Set.Icc (0 : ℝ) T).1
        · exact absurd hT (not_lt.mpr hT')
    rw [hcongr, smul_zero]
  have hlim := hasHaarForwardAverage_of_continuous h F
  unfold HasHaarForwardAverage at hlim
  have hzero : (∫ x, F x ∂(torusHaar ι)) = 0 := by
    refine tendsto_nhds_unique hlim ?_
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
    exact (hzeroAvg T hT).symm
  have hreal : (∫ x, f x ∂(torusHaar ι)) = 0 := by
    have hcast : (∫ x, ((f x : ℝ) : ℂ) ∂(torusHaar ι)) = 0 := hzero
    exact_mod_cast hcast
  have hpos : 0 < ∫ x, f x ∂(torusHaar ι) := by
    refine integral_pos_of_torusHaar (fun x => (hfIcc x).1) (x₀ := x₀) ?_
    rw [hf1 rfl]
    norm_num
  linarith

/-- Every tail of a forward orbit is dense: the flow is additive, so a tail is a translate. -/
theorem dense_forwardOrbit [Countable ι] [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) (T₀ : ℝ) :
    Dense {x : UnitAddTorus ι | ∃ t : ℝ, T₀ ≤ t ∧ clockPhasePoint omega t = x} := by
  classical
  have hbase := dense_forwardOrbit_zero h
  have himage : (fun x => clockPhasePoint omega T₀ + x) ''
      {x : UnitAddTorus ι | ∃ t : ℝ, 0 ≤ t ∧ clockPhasePoint omega t = x}
      ⊆ {x : UnitAddTorus ι | ∃ t : ℝ, T₀ ≤ t ∧ clockPhasePoint omega t = x} := by
    rintro - ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨T₀ + s, by linarith, ?_⟩
    rw [clockPhasePoint_add]
  refine Dense.mono himage ?_
  exact (Homeomorph.addLeft (clockPhasePoint omega T₀)).surjective.denseRange.dense_image
    (Homeomorph.addLeft (clockPhasePoint omega T₀)).continuous hbase

end

end GaloisForLFunctions.HTGeometry
