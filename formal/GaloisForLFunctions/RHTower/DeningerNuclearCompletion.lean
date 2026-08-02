import GaloisForLFunctions.RHTower.DeningerNuclearFiniteRank
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# A nuclear map extends to a nuclear map of completions

The functionals of a nuclear representation extend to the completion of the source without
increasing their norms, and the vectors sit inside the completion of the target.  The resulting
family of rank-one maps still has summable norms, so it sums in the operator norm to a map of the
completions, which is nuclear by construction and agrees with the original map on the image of the
source.

This is what makes nuclearity of a locally convex space a statement about the completed seminorm
quotients, as in the classical definition.

* `deningerCompletionFunctional` : the extension of a functional to the completion.
* `DeningerIsNuclear.exists_completion` : a nuclear map extends to a nuclear map of completions.
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section CompletionExtension

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **The extension of a continuous functional to the completion.** -/
noncomputable def deningerCompletionFunctional (φ : X →L[𝕜] 𝕜) :
    Completion X →L[𝕜] 𝕜 :=
  φ.extend (Completion.toComplL (𝕜 := 𝕜) (E := X))

theorem deningerCompletionFunctional_coe (φ : X →L[𝕜] 𝕜) (x : X) :
    deningerCompletionFunctional φ (Completion.toComplL (𝕜 := 𝕜) (E := X) x) = φ x := by
  refine ContinuousLinearMap.extend_eq (f := φ)
    (e := Completion.toComplL (𝕜 := 𝕜) (E := X)) ?_ ?_ x
  · rw [Completion.coe_toComplL]
    exact Completion.denseRange_coe
  · rw [Completion.coe_toComplL]
    exact Completion.isUniformInducing_coe X

theorem deningerCompletionFunctional_norm_le (φ : X →L[𝕜] 𝕜) :
    ‖deningerCompletionFunctional φ‖ ≤ ‖φ‖ := by
  have hdense : DenseRange (Completion.toComplL (𝕜 := 𝕜) (E := X)) := by
    rw [Completion.coe_toComplL]
    exact Completion.denseRange_coe
  have hnorm : ∀ x : X, ‖x‖ ≤ 1 * ‖Completion.toComplL (𝕜 := 𝕜) (E := X) x‖ := by
    intro x
    rw [one_mul, Completion.coe_toComplL, Completion.norm_coe]
  have h := ContinuousLinearMap.opNorm_extend_le (f := φ)
    (e := Completion.toComplL (𝕜 := 𝕜) (E := X)) (N := 1) hdense hnorm
  rw [deningerCompletionFunctional]
  simpa using h

end CompletionExtension

section NuclearCompletion

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **A nuclear map extends to a nuclear map of the completions.** -/
theorem DeningerIsNuclear.exists_completion {T : X →L[𝕜] Y} (hT : DeningerIsNuclear T) :
    ∃ S : Completion X →L[𝕜] Completion Y, DeningerIsNuclear S ∧
      ∀ x : X, S (Completion.toComplL (𝕜 := 𝕜) (E := X) x)
        = Completion.toComplL (𝕜 := 𝕜) (E := Y) (T x) := by
  obtain ⟨ι, φ, y, hsum, happ⟩ := hT
  set ψ : ι → (Completion X →L[𝕜] 𝕜) :=
    fun a => deningerCompletionFunctional (φ a) with hψ
  set z : ι → Completion Y := fun a => Completion.toComplL (𝕜 := 𝕜) (E := Y) (y a) with hz
  have hznorm : ∀ a, ‖z a‖ = ‖y a‖ := by
    intro a
    rw [hz, Completion.coe_toComplL, Completion.norm_coe]
  have hsum' : Summable fun a => ‖ψ a‖ * ‖z a‖ := by
    refine Summable.of_nonneg_of_le (fun a => by positivity) (fun a => ?_) hsum
    rw [hznorm a]
    exact mul_le_mul_of_nonneg_right (deningerCompletionFunctional_norm_le (φ a)) (norm_nonneg _)
  have hnormeq : (fun a => ‖(ψ a).smulRight (z a)‖) = fun a => ‖ψ a‖ * ‖z a‖ := by
    funext a
    exact ContinuousLinearMap.norm_smulRight_apply (ψ a) (z a)
  have hsummable : Summable fun a => (ψ a).smulRight (z a) := by
    refine Summable.of_norm ?_
    rw [hnormeq]
    exact hsum'
  obtain ⟨S, hS⟩ := hsummable
  have hpoint : ∀ w : Completion X, HasSum (fun a => ψ a w • z a) (S w) := by
    intro w
    have h1 := (ContinuousLinearMap.apply 𝕜 (Completion Y) w).hasSum hS
    have heq : (fun a => (ContinuousLinearMap.apply 𝕜 (Completion Y) w) ((ψ a).smulRight (z a)))
        = fun a => ψ a w • z a := by
      funext a
      show ((ψ a).smulRight (z a)) w = ψ a w • z a
      exact ContinuousLinearMap.smulRight_apply
    rwa [heq] at h1
  refine ⟨S, ⟨ι, ψ, z, hsum', hpoint⟩, ?_⟩
  intro x
  have hcoe : HasSum (fun a => ψ a (Completion.toComplL (𝕜 := 𝕜) (E := X) x) • z a)
      (Completion.toComplL (𝕜 := 𝕜) (E := Y) (T x)) := by
    have h2 := (Completion.toComplL (𝕜 := 𝕜) (E := Y)).hasSum (happ x)
    have heq : (fun a => Completion.toComplL (𝕜 := 𝕜) (E := Y) (φ a x • y a))
        = fun a => ψ a (Completion.toComplL (𝕜 := 𝕜) (E := X) x) • z a := by
      funext a
      rw [map_smul, hψ, hz, deningerCompletionFunctional_coe]
    rwa [heq] at h2
  exact (hpoint (Completion.toComplL (𝕜 := 𝕜) (E := X) x)).unique hcoe

end NuclearCompletion

end RHTower

