import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearSpaceCompleted
import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearProduct

/-!
# The completed map induced by a bounded linear map

A linear map carrying one seminorm into a multiple of another induces a bounded map of the normed
quotients, and that map extends uniquely to the completions.  The extension has the same bound, so
the coordinate projections and inclusions of a direct sum remain bounded after completion — which is
what the nuclearity of a direct sum needs, since nuclearity is stated on the completed quotients.

* `deningerSeminormInduced_norm_le` : the bound on the uncompleted induced map.
* `deningerSeminormInducedC` : **the completed induced map.**
* `deningerSeminormInducedC_mkC` : its value on a class.
* `deningerSeminormInducedC_norm_le` : it keeps the bound.
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

variable {𝕜 E E' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup E'] [Module 𝕜 E']

omit [CompleteSpace 𝕜] in
theorem deningerSeminormInduced_norm_le {p : Seminorm 𝕜 E'} {q : Seminorm 𝕜 E} {C : ℝ}
    (hC : 0 ≤ C) (f : E →ₗ[𝕜] E') (h : ∀ x, p (f x) ≤ C * q x) :
    ‖deningerSeminormInduced f h‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-- **The completed map of Banach spaces induced by a bounded linear map.** -/
noncomputable def deningerSeminormInducedC {p : Seminorm 𝕜 E'} {q : Seminorm 𝕜 E} {C : ℝ}
    (f : E →ₗ[𝕜] E') (h : ∀ x, p (f x) ≤ C * q x) :
    DeningerSeminormCompletion q →L[𝕜] DeningerSeminormCompletion p :=
  ((Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)).comp
    (deningerSeminormInduced f h)).extend
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q))

omit [CompleteSpace 𝕜] in
theorem deningerSeminormInducedC_coe {p : Seminorm 𝕜 E'} {q : Seminorm 𝕜 E} {C : ℝ}
    (f : E →ₗ[𝕜] E') (h : ∀ x, p (f x) ≤ C * q x) (z : DeningerSeminormSpace q) :
    deningerSeminormInducedC f h
        (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q) z)
      = Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)
        (deningerSeminormInduced f h z) :=
  ContinuousLinearMap.extend_eq
    (f := (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)).comp
      (deningerSeminormInduced f h))
    (e := Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q))
    (deningerDenseRange_toComplL q) (deningerIsUniformInducing_toComplL q) z

omit [CompleteSpace 𝕜] in
theorem deningerSeminormInducedC_mkC {p : Seminorm 𝕜 E'} {q : Seminorm 𝕜 E} {C : ℝ}
    (f : E →ₗ[𝕜] E') (h : ∀ x, p (f x) ≤ C * q x) (x : E) :
    deningerSeminormInducedC f h (deningerSeminormMkC q x) = deningerSeminormMkC p (f x) := by
  show deningerSeminormInducedC f h
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q) (deningerSeminormMk q x))
    = _
  rw [deningerSeminormInducedC_coe, deningerSeminormInduced_mk]
  rfl

omit [CompleteSpace 𝕜] in
theorem deningerSeminormInducedC_norm_le {p : Seminorm 𝕜 E'} {q : Seminorm 𝕜 E} {C : ℝ}
    (hC : 0 ≤ C) (f : E →ₗ[𝕜] E') (h : ∀ x, p (f x) ≤ C * q x) :
    ‖deningerSeminormInducedC f h‖ ≤ C := by
  have hcomp : ‖(Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)).comp
      (deningerSeminormInduced f h)‖ ≤ C := by
    refine ContinuousLinearMap.opNorm_le_bound _ hC fun z => ?_
    show ‖Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)
      (deningerSeminormInduced f h z)‖ ≤ C * ‖z‖
    rw [Completion.coe_toComplL, Completion.norm_coe]
    exact ContinuousLinearMap.le_of_opNorm_le _ (deningerSeminormInduced_norm_le hC f h) z
  have hnorm : ∀ z : DeningerSeminormSpace q,
      ‖z‖ ≤ 1 * ‖Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q) z‖ := by
    intro z
    rw [one_mul, Completion.coe_toComplL, Completion.norm_coe]
  have hext := ContinuousLinearMap.opNorm_extend_le
    (f := (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)).comp
      (deningerSeminormInduced f h))
    (e := Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q)) (N := 1)
    (deningerDenseRange_toComplL q) hnorm
  rw [deningerSeminormInducedC]
  refine hext.trans ?_
  simpa using hcomp

omit [CompleteSpace 𝕜] in
/-- The completed comparison map on a class. -/
theorem deningerSeminormComparisonC_mkC {p q : Seminorm 𝕜 E} {C : ℝ}
    (h : ∀ x, p x ≤ C * q x) (x : E) :
    deningerSeminormComparisonC h (deningerSeminormMkC q x) = deningerSeminormMkC p x := by
  show deningerSeminormComparisonC h
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q) (deningerSeminormMk q x))
    = _
  rw [deningerSeminormComparisonC_coe, deningerSeminormComparison_mk]
  rfl

end RHTower
