import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic

/-!
# Smooth integration with an integrable weight and compact parameter range

The integration domain may have infinite measure. Compactness bounds the smooth
family and its derivatives; the fixed integrable weight supplies every majorant.
This is the spatial regularity bridge for the projective Poisson kernel.
-/

noncomputable section

open Complex Set Filter MeasureTheory Topology Metric
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

variable {U V K : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K)
  (hKV : K ⊆ V) {γ : ℝ → ℂ} (hγ : Continuous γ) (hγK : ∀ t, γ t ∈ K)
  {w : ℝ → ℝ} (hw : Integrable w)

include hU hV hKV hγ hγK in
private lemma parameter_fiber_continuous {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℂ × ℂ → G} (hf : ContinuousOn F (U ×ˢ V)) {x : ℂ} (hx : x ∈ U) :
    Continuous (fun t : ℝ => F (x, γ t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hf.continuousAt ((hU.prod hV).mem_nhds ⟨hx, hKV (hγK t)⟩)).comp
    (continuous_const.prodMk hγ).continuousAt

include hU hK hKV hγK in
private lemma parameter_local_bound {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℂ × ℂ → G} (hf : ContinuousOn F (U ×ˢ V)) {x : ℂ} (hx : x ∈ U) :
    ∃ S ∈ 𝓝 x, S ⊆ U ∧ ∃ C : ℝ, ∀ y ∈ S, ∀ t : ℝ, ‖F (y, γ t)‖ ≤ C := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hSU : closedBall x (r / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans hrU
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x (r / 2)).prod hK).exists_bound_of_continuousOn
    (hf.mono fun p hp => ⟨hSU hp.1, hKV hp.2⟩)
  exact ⟨closedBall x (r / 2), closedBall_mem_nhds x (by linarith), hSU, C,
    fun y hy t => hC (y, γ t) ⟨hy, hγK t⟩⟩

include hU hV hK hKV hγ hγK hw in
/-- A fixed integrable weight absorbs every continuous compact-parameter fiber. -/
theorem weighted_parameter_integrable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℂ × ℂ → G} (hf : ContinuousOn F (U ×ˢ V)) {x : ℂ} (hx : x ∈ U) :
    Integrable (fun t : ℝ => w t • F (x, γ t)) := by
  obtain ⟨S, hS, _, C, hC⟩ := parameter_local_bound hU hK hKV hγK hf hx
  apply (hw.norm.mul_const C).mono'
    (hw.aestronglyMeasurable.smul
      (parameter_fiber_continuous hU hV hKV hγ hγK hf hx).aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖w t • F (x, γ t)‖ ≤ ‖w t‖ * C
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x (mem_of_mem_nhds hS) t) (norm_nonneg _)

include hU hV hK hKV hγ hγK hw in
private lemma continuousOn_weighted_parameter {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℂ × ℂ → G} (hf : ContinuousOn F (U ×ˢ V)) :
    ContinuousOn (fun x => ∫ t : ℝ, w t • F (x, γ t)) U := by
  intro x hx
  obtain ⟨S, hS, _, C, hC⟩ := parameter_local_bound hU hK hKV hγK hf hx
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated (bound := fun t : ℝ => ‖w t‖ * C)
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact hw.aestronglyMeasurable.smul
      (parameter_fiber_continuous hU hV hKV hγ hγK hf hy).aestronglyMeasurable
  · filter_upwards [hS] with y hy
    exact Eventually.of_forall fun t => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC y hy t) (norm_nonneg _)
  · exact hw.norm.mul_const C
  · exact Eventually.of_forall fun t =>
      ((hf.continuousAt ((hU.prod hV).mem_nhds ⟨hx, hKV (hγK t)⟩)).comp
        (continuous_id.prodMk continuous_const).continuousAt).const_smul (w t)

/-- Derivative in the spatial coordinate of a two-variable smooth family. -/
def compactParameterPartial {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : ℂ × ℂ → G) (p : ℂ × ℂ) : ℂ →L[ℝ] G :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)

include hU hV in
private lemma compactParameterPartial_smooth {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℂ × ℂ → G} {n : ℕ} (hf : ContDiffOn ℝ (n + 1) F (U ×ˢ V)) :
    ContDiffOn ℝ n (compactParameterPartial F) (U ×ˢ V) := by
  have hh : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) F (U ×ˢ V) := by exact_mod_cast hf
  exact (hh.fderiv_of_isOpen (hU.prod hV) le_rfl).clm_comp contDiffOn_const

include hU hV in
private lemma compactParameterPartial_derivative {G : Type} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : ℂ × ℂ → G} (hf : ContDiffOn ℝ 1 F (U ×ˢ V))
    {x p : ℂ} (hx : x ∈ U) (hp : p ∈ V) :
    HasFDerivAt (fun y => F (y, p)) (compactParameterPartial F (x, p)) x := by
  have hd : DifferentiableAt ℝ F (x, p) := (hf.differentiableOn (by norm_num)).differentiableAt
    ((hU.prod hV).mem_nhds ⟨hx, hp⟩)
  exact hd.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const p x))

include hU hV hK hKV hγ hγK hw in
/-- Dominated differentiation with the exact integral of the spatial derivative. -/
theorem hasFDerivAt_weighted_compact_parameter {G : Type} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {F : ℂ × ℂ → G}
    (hf : ContDiffOn ℝ 1 F (U ×ˢ V)) {x : ℂ} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t : ℝ, w t • F (y, γ t))
      (∫ t : ℝ, w t • compactParameterPartial F (x, γ t)) x := by
  have hfd : ContinuousOn (compactParameterPartial F) (U ×ˢ V) :=
    (compactParameterPartial_smooth hU hV (n := 0) hf).continuousOn
  obtain ⟨S, hS, hSU, C, hC⟩ := parameter_local_bound hU hK hKV hγK hfd hx
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y t => w t • compactParameterPartial F (y, γ t))
    (bound := fun t => ‖w t‖ * C) hS
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact hw.aestronglyMeasurable.smul
      (parameter_fiber_continuous hU hV hKV hγ hγK hf.continuousOn hy).aestronglyMeasurable
  · exact weighted_parameter_integrable hU hV hK hKV hγ hγK hw hf.continuousOn hx
  · exact hw.aestronglyMeasurable.smul
      (parameter_fiber_continuous hU hV hKV hγ hγK hfd hx).aestronglyMeasurable
  · exact Eventually.of_forall fun t y hy => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC y hy t) (norm_nonneg _)
  · exact hw.norm.mul_const C
  · exact Eventually.of_forall fun t y hy =>
      (compactParameterPartial_derivative hU hV hf (hSU hy) (hKV (hγK t))).const_smul (w t)

include hU hV hK hKV hγ hγK hw in
/-- Every finite smoothness order is preserved, despite the noncompact integration domain. -/
theorem contDiffOn_weighted_compact_parameter (n : ℕ) :
    ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {F : ℂ × ℂ → G}, ContDiffOn ℝ n F (U ×ˢ V) →
      ContDiffOn ℝ n (fun y => ∫ t : ℝ, w t • F (y, γ t)) U := by
  induction n with
  | zero =>
    intro G _ _ _ F hf
    exact contDiffOn_zero.mpr
      (continuousOn_weighted_parameter hU hV hK hKV hγ hγK hw hf.continuousOn)
  | succ n ih =>
    intro G _ _ _ F hf
    have hf1 : ContDiffOn ℝ 1 F (U ×ˢ V) :=
      hf.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    have hh : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
        (fun y => ∫ t : ℝ, w t • F (y, γ t)) U := by
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
      refine ⟨by simp, (fun x => ∫ t : ℝ, w t • compactParameterPartial F (x, γ t)), ?_, ?_⟩
      · exact ih (compactParameterPartial_smooth hU hV hf)
      · intro x hx
        exact (hasFDerivAt_weighted_compact_parameter hU hV hK hKV hγ hγK hw hf1 hx).hasFDerivWithinAt
    exact_mod_cast hh

include hU hV hK hKV hγ hγK hw in
/-- The compactified Poisson parameter therefore preserves C∞ regularity. -/
theorem contDiffOn_weighted_compact_parameter_infty {G : Type} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {F : ℂ × ℂ → G}
    (hf : ContDiffOn ℝ ∞ F (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun y => ∫ t : ℝ, w t • F (y, γ t)) U :=
  contDiffOn_infty.mpr fun n => contDiffOn_weighted_compact_parameter hU hV hK hKV hγ hγK hw n
    (contDiffOn_infty.mp hf n)

include hU hV hK hKV hγ hγK hw in
/-- Complex differentiation uses the same compact-parameter majorant as real differentiation. -/
theorem hasDerivAt_weighted_compact_parameter {F F' : ℂ × ℂ → ℂ}
    (hF : ContinuousOn F (U ×ˢ V)) (hF' : ContinuousOn F' (U ×ˢ V))
    (hd : ∀ x ∈ U, ∀ c ∈ V, HasDerivAt (fun y => F (y, c)) (F' (x, c)) x)
    {x : ℂ} (hx : x ∈ U) :
    HasDerivAt (fun y => ∫ t : ℝ, w t • F (y, γ t))
      (∫ t : ℝ, w t • F' (x, γ t)) x := by
  obtain ⟨S, hS, hSU, C, hC⟩ := parameter_local_bound hU hK hKV hγK hF' hx
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun y t => w t • F' (y, γ t)) (bound := fun t => ‖w t‖ * C)
    hS ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact hw.aestronglyMeasurable.smul
      (parameter_fiber_continuous hU hV hKV hγ hγK hF hy).aestronglyMeasurable
  · exact weighted_parameter_integrable hU hV hK hKV hγ hγK hw hF hx
  · exact hw.aestronglyMeasurable.smul
      (parameter_fiber_continuous hU hV hKV hγ hγK hF' hx).aestronglyMeasurable
  · exact Eventually.of_forall fun t y hy => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC y hy t) (norm_nonneg _)
  · exact hw.norm.mul_const C
  · exact Eventually.of_forall fun t y hy => (hd y (hSU hy) (γ t) (hKV (hγK t))).const_smul (w t)

end RHTower.WeilHigherDenominator
