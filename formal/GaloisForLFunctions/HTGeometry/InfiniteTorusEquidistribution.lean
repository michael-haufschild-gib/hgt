import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter
import GaloisForLFunctions.HTGeometry.SymmetricTimeAverageCharacterLaw

/-!
# Time averages along an infinite Kronecker flow

The symmetric time average of a continuous function along the phase flow of a frequency family is a
linear functional bounded by the supremum norm.  On a character it is the elementary phase average
of the character's detuning, which converges to one at zero detuning and to zero otherwise.

Under rational independence the detuning vanishes only for the trivial character, so on every
character the time average converges to the character's Haar mean -- the first half of unique
ergodicity of the flow on the product torus.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- Symmetric time average of a continuous torus function along a phase flow. -/
def flowAverage (omega : ι → ℝ) (T : ℝ) (f : C(UnitAddTorus ι, ℂ)) : ℂ :=
  (2 * T : ℂ)⁻¹ * ∫ t in -T..T, f (clockPhasePoint omega t)

theorem flowAverage_torusCharacter (omega : ι → ℝ) (n : ι →₀ ℤ) (T : ℝ) :
    flowAverage omega T (torusCharacter n)
      = symmetricPhaseAverage T (characterDetuning n omega) := by
  rw [flowAverage, symmetricPhaseAverage]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact torusCharacter_clockPhasePoint n omega t

theorem characterDetuning_zero (omega : ι → ℝ) :
    characterDetuning (0 : ι →₀ ℤ) omega = 0 := by
  rw [characterDetuning]
  simp

/-- Under rational independence only the trivial character is resonant. -/
theorem characterDetuning_eq_zero_iff {omega : ι → ℝ} (h : RationallyIndependentSequence omega)
    (n : ι →₀ ℤ) : characterDetuning n omega = 0 ↔ n = 0 := by
  classical
  constructor
  · intro hzero
    have hsum : (∑ i : (n.support : Set ι), ((fun j : (n.support : Set ι) => (n j : ℤ)) i : ℝ) *
        omega i) = 0 := by
      rw [← Finset.sum_subtype n.support (fun x => Finset.mem_coe.symm)
        (fun i => (n i : ℝ) * omega i)]
      exact hzero
    have hvec := h n.support (fun i : (n.support : Set ι) => n i) hsum
    refine Finsupp.ext fun i => ?_
    by_cases hi : i ∈ n.support
    · have := congrFun hvec ⟨i, hi⟩
      simpa using this
    · simpa using Finsupp.notMem_support_iff.mp hi
  · intro hn
    subst hn
    exact characterDetuning_zero omega

/-- **The time average of a character converges to its Haar mean.** -/
theorem tendsto_flowAverage_torusCharacter [Countable ι] [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) (n : ι →₀ ℤ) :
    Tendsto (fun T => flowAverage omega T (torusCharacter n)) atTop
      (𝓝 (∫ x, torusCharacter n x ∂(torusHaar ι))) := by
  classical
  have hfun : (fun T => flowAverage omega T (torusCharacter n))
      = fun T => symmetricPhaseAverage T (characterDetuning n omega) :=
    funext fun T => flowAverage_torusCharacter omega n T
  rw [hfun, integral_torusCharacter]
  have hlim := symmetricPhaseAverage_tendsto_resonanceIndicator (characterDetuning n omega)
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    rwa [if_pos (characterDetuning_zero omega)] at hlim
  · rw [if_neg hn]
    rwa [if_neg (fun hcon => hn ((characterDetuning_eq_zero_iff h n).mp hcon))] at hlim


/-! ## From characters to all continuous functions -/

theorem continuous_clockPhasePoint (omega : ι → ℝ) :
    Continuous (clockPhasePoint omega) := by
  refine continuous_pi fun i => ?_
  exact (AddCircle.continuous_mk' 1).comp (by fun_prop)

theorem intervalIntegrable_flow (omega : ι → ℝ) (f : C(UnitAddTorus ι, ℂ)) (a b : ℝ) :
    IntervalIntegrable (fun t => f (clockPhasePoint omega t)) MeasureTheory.volume a b :=
  (f.continuous.comp (continuous_clockPhasePoint omega)).intervalIntegrable a b

theorem flowAverage_add (omega : ι → ℝ) (T : ℝ) (f g : C(UnitAddTorus ι, ℂ)) :
    flowAverage omega T (f + g) = flowAverage omega T f + flowAverage omega T g := by
  rw [flowAverage, flowAverage, flowAverage, ← mul_add]
  congr 1
  rw [← intervalIntegral.integral_add (intervalIntegrable_flow omega f (-T) T)
    (intervalIntegrable_flow omega g (-T) T)]
  rfl

theorem flowAverage_smul (omega : ι → ℝ) (T : ℝ) (c : ℂ) (f : C(UnitAddTorus ι, ℂ)) :
    flowAverage omega T (c • f) = c * flowAverage omega T f := by
  rw [flowAverage, flowAverage]
  rw [show (fun t => (c • f) (clockPhasePoint omega t))
      = fun t => c • f (clockPhasePoint omega t) from rfl]
  rw [intervalIntegral.integral_smul]
  ring

theorem flowAverage_sub (omega : ι → ℝ) (T : ℝ) (f g : C(UnitAddTorus ι, ℂ)) :
    flowAverage omega T (f - g) = flowAverage omega T f - flowAverage omega T g := by
  have hsub : f - g = f + (-1 : ℂ) • g := by
    ext x
    simp [sub_eq_add_neg]
  rw [hsub, flowAverage_add, flowAverage_smul]
  ring

theorem norm_flowAverage_le (omega : ι → ℝ) {T : ℝ} (hT : 0 < T) (f : C(UnitAddTorus ι, ℂ)) :
    ‖flowAverage omega T f‖ ≤ ‖f‖ := by
  have hbound : ‖∫ t in -T..T, f (clockPhasePoint omega t)‖ ≤ ‖f‖ * (2 * T) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
      (C := ‖f‖) (f := fun t => f (clockPhasePoint omega t))
      (fun t _ => f.norm_coe_le_norm _)
    have habs : |T - -T| = 2 * T := by
      rw [show T - -T = 2 * T by ring, abs_of_pos (by linarith)]
    rwa [habs] at h
  have hnorm : ‖(2 * T : ℂ)‖ = 2 * T := by
    rw [show ((2 : ℂ) * (T : ℂ)) = ((2 * T : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * T)]
  rw [flowAverage, norm_mul, norm_inv, hnorm,
    inv_mul_le_iff₀ (by linarith : (0 : ℝ) < 2 * T)]
  calc ‖∫ t in -T..T, f (clockPhasePoint omega t)‖ ≤ ‖f‖ * (2 * T) := hbound
    _ = 2 * T * ‖f‖ := by ring

/-- Functions whose symmetric time average along the flow converges to their Haar mean. -/
def HasHaarTimeAverage [Countable ι] (omega : ι → ℝ) (f : C(UnitAddTorus ι, ℂ)) : Prop :=
  Tendsto (fun T => flowAverage omega T f) atTop (𝓝 (∫ x, f x ∂(torusHaar ι)))

theorem integrable_continuousMap [Countable ι] (f : C(UnitAddTorus ι, ℂ)) :
    MeasureTheory.Integrable (fun x => f x) (torusHaar ι) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem hasHaarTimeAverage_add [Countable ι] {omega : ι → ℝ} {f g : C(UnitAddTorus ι, ℂ)}
    (hf : HasHaarTimeAverage omega f) (hg : HasHaarTimeAverage omega g) :
    HasHaarTimeAverage omega (f + g) := by
  have hint : (∫ x, (f + g) x ∂(torusHaar ι))
      = (∫ x, f x ∂(torusHaar ι)) + ∫ x, g x ∂(torusHaar ι) := by
    rw [← MeasureTheory.integral_add (integrable_continuousMap f) (integrable_continuousMap g)]
    rfl
  unfold HasHaarTimeAverage
  rw [hint]
  refine (hf.add hg).congr fun T => ?_
  exact (flowAverage_add omega T f g).symm

theorem hasHaarTimeAverage_smul [Countable ι] {omega : ι → ℝ} (c : ℂ)
    {f : C(UnitAddTorus ι, ℂ)} (hf : HasHaarTimeAverage omega f) :
    HasHaarTimeAverage omega (c • f) := by
  have hint : (∫ x, (c • f) x ∂(torusHaar ι)) = c * ∫ x, f x ∂(torusHaar ι) := by
    rw [← MeasureTheory.integral_const_mul]
    rfl
  unfold HasHaarTimeAverage
  rw [hint]
  refine (hf.const_mul c).congr fun T => ?_
  exact (flowAverage_smul omega T c f).symm

theorem hasHaarTimeAverage_zero [Countable ι] (omega : ι → ℝ) :
    HasHaarTimeAverage omega (0 : C(UnitAddTorus ι, ℂ)) := by
  unfold HasHaarTimeAverage
  have hint : (∫ x, (0 : C(UnitAddTorus ι, ℂ)) x ∂(torusHaar ι)) = 0 := by
    simp
  rw [hint]
  refine tendsto_const_nhds.congr fun T => ?_
  rw [flowAverage]
  simp

/-- Convergence on the whole character span. -/
theorem hasHaarTimeAverage_of_mem_span [Countable ι] [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) {f : C(UnitAddTorus ι, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (torusCharacter (ι := ι)))) :
    HasHaarTimeAverage omega f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      exact tendsto_flowAverage_torusCharacter h n
  | zero => exact hasHaarTimeAverage_zero omega
  | add x y _ _ hx hy => exact hasHaarTimeAverage_add hx hy
  | smul c x _ hx => exact hasHaarTimeAverage_smul c hx

/-- **Unique ergodicity of an infinite Kronecker flow.**  For a rationally independent frequency
family the symmetric time average of every continuous function along the phase flow converges to its
Haar mean on the product torus. -/
theorem hasHaarTimeAverage_of_continuous [Countable ι] [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) (f : C(UnitAddTorus ι, ℂ)) :
    HasHaarTimeAverage omega f := by
  classical
  rw [HasHaarTimeAverage, Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  have hmem : f ∈ (Submodule.span ℂ (Set.range (torusCharacter (ι := ι)))).topologicalClosure := by
    rw [span_torusCharacter_closure_eq_top ι]
    exact Submodule.mem_top
  obtain ⟨g, hgspan, hgclose⟩ : ∃ g ∈ Submodule.span ℂ (Set.range (torusCharacter (ι := ι))),
      dist f g < ε / 3 := by
    have hclosure : f ∈ closure
        ((Submodule.span ℂ (Set.range (torusCharacter (ι := ι)))) : Set C(UnitAddTorus ι, ℂ)) :=
      hmem
    obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hclosure (ε / 3) hε3
    exact ⟨g, hg, hdist⟩
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp
    (hasHaarTimeAverage_of_mem_span h hgspan) (ε / 3) hε3
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right T₀ 1) hT)
  have hT₀le : T₀ ≤ T := le_trans (le_max_left T₀ 1) hT
  have hdiff : dist (flowAverage omega T f) (flowAverage omega T g) < ε / 3 := by
    rw [dist_eq_norm, ← flowAverage_sub]
    calc ‖flowAverage omega T (f - g)‖ ≤ ‖f - g‖ := norm_flowAverage_le omega hTpos _
      _ = dist f g := (dist_eq_norm f g).symm
      _ < ε / 3 := hgclose
  have hint : dist (∫ x, g x ∂(torusHaar ι)) (∫ x, f x ∂(torusHaar ι)) < ε / 3 := by
    rw [dist_eq_norm, ← MeasureTheory.integral_sub (integrable_continuousMap g)
      (integrable_continuousMap f)]
    have hbound : ‖∫ x, (g x - f x) ∂(torusHaar ι)‖ ≤ ‖g - f‖ * (torusHaar ι).real Set.univ := by
      refine MeasureTheory.norm_integral_le_of_norm_le_const ?_
      refine Filter.Eventually.of_forall fun x => ?_
      exact (g - f).norm_coe_le_norm x
    rw [MeasureTheory.probReal_univ, mul_one] at hbound
    calc ‖∫ x, (g x - f x) ∂(torusHaar ι)‖ ≤ ‖g - f‖ := hbound
      _ = dist g f := (dist_eq_norm g f).symm
      _ = dist f g := dist_comm g f
      _ < ε / 3 := hgclose
  calc dist (flowAverage omega T f) (∫ x, f x ∂(torusHaar ι))
      ≤ dist (flowAverage omega T f) (flowAverage omega T g)
        + dist (flowAverage omega T g) (∫ x, f x ∂(torusHaar ι)) := dist_triangle _ _ _
    _ ≤ dist (flowAverage omega T f) (flowAverage omega T g)
        + (dist (flowAverage omega T g) (∫ x, g x ∂(torusHaar ι))
          + dist (∫ x, g x ∂(torusHaar ι)) (∫ x, f x ∂(torusHaar ι))) := by
        gcongr
        exact dist_triangle _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by
        gcongr
        exact hT₀ T hT₀le
    _ = ε := by ring

end

end GaloisForLFunctions.HTGeometry
