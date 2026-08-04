import GaloisForLFunctions.HTGeometry.SimpleEigenvalueBranch
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Kato perturbation theory for a compact symmetric family

A simple nonzero eigenvalue of a compact symmetric operator moves differentiably under a differentiable
perturbation of the operator, together with a normalized eigenvector, and its derivative is the expectation of
the perturbation.  This is the perturbation-theoretic input that spectral applications import; here it is
proved outright.

Two ingredients meet.  The first is the bordered implicit function theorem of `SimpleEigenvalueBranch`, which
needs a pseudo-inverse `R` of `A - nu_0` modulo the eigendirection.  The second — supplied here — is the
existence of that pseudo-inverse for a *compact* symmetric operator: on the orthogonal complement

```text
W = {phi | ⟪psi_0, phi⟫ = 0}
```

the operator `A` restricts to a compact operator with no `nu_0`-eigenvector (an eigenvector there would be a
multiple of `psi_0` by simplicity, and `psi_0` is not in `W`), so the Fredholm alternative puts `nu_0` in the
resolvent set of the restriction.  The resolvent, precomposed with the projection `y ↦ y - ⟪psi_0, y⟫ psi_0`,
*is* the pseudo-inverse — with no gap estimate, no open mapping theorem and no contour integral.
-/

noncomputable section

open RealInnerProductSpace Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The pseudo-inverse of a compact symmetric operator at a simple nonzero eigenvalue.**  There is a bounded
operator `R` with

```text
A (R y) - nu_0 • R y = y - ⟪psi_0, y⟫ psi_0,      ⟪psi_0, R y⟫ = 0,
```

i.e. `R` inverts `A - nu_0` on the orthogonal complement of the eigendirection and vanishes in the
eigendirection.  It is the Fredholm resolvent of the restriction of `A` to that complement. -/
theorem exists_pseudoInverse_of_isCompactOperator [CompleteSpace E]
    {A : E →L[ℝ] E} {ν₀ : ℝ} {ψ₀ : E}
    (hcomp : IsCompactOperator A)
    (hsymm : ∀ u v : E, ⟪A u, v⟫ = ⟪u, A v⟫)
    (heig : A ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫ = 1) (hν₀ : ν₀ ≠ 0)
    (hker : ∀ φ : E, A φ = ν₀ • φ → ∃ s : ℝ, φ = s • ψ₀) :
    ∃ R : E →L[ℝ] E, (∀ y : E, A (R y) - ν₀ • R y = y - ⟪ψ₀, y⟫ • ψ₀) ∧
      ∀ y : E, ⟪ψ₀, R y⟫ = 0 := by
  classical
  -- the orthogonal complement of the eigendirection, as a closed subspace
  set W : Submodule ℝ E := LinearMap.ker ((innerSL ℝ ψ₀ : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ) with hWdef
  have hnψ₀ : ‖ψ₀‖ = 1 := by
    have h := real_inner_self_eq_norm_sq ψ₀
    rw [hnorm] at h
    nlinarith [norm_nonneg ψ₀]
  have hmemW : ∀ x : E, x ∈ W ↔ ⟪ψ₀, x⟫ = 0 := by
    intro x
    simp [hWdef, LinearMap.mem_ker]
  haveI hcompleteW : CompleteSpace W :=
    IsClosed.completeSpace_coe (hs := (innerSL ℝ ψ₀).isClosed_ker)
  -- `A` preserves the complement
  have hAW : ∀ x ∈ W, A x ∈ W := by
    intro x hx
    rw [hmemW] at hx ⊢
    rw [← hsymm ψ₀ x, heig, real_inner_smul_left, hx, mul_zero]
  -- the restriction, a compact operator on `W`
  set AW : W →L[ℝ] W := (A.comp W.subtypeL).codRestrict W (fun x => hAW x x.2) with hAWdef
  have hAWval : ∀ x : W, ((AW x : E)) = A (x : E) := fun _ => rfl
  have hcompW : IsCompactOperator (AW : W → W) := by
    have hcompL : IsCompactOperator ((A : E →ₗ[ℝ] E) : E → E) := hcomp
    have h := hcompL.restrict' (V := W) hAW
    have hfun : (AW : W → W) = ((A : E →ₗ[ℝ] E).restrict hAW : W → W) := by
      funext x
      exact Subtype.ext rfl
    rw [hfun]
    exact h
  -- `nu_0` is not an eigenvalue of the restriction: simplicity forces the eigendirection
  have hnoteig : ¬ Module.End.HasEigenvalue (AW : Module.End ℝ W) ν₀ := by
    intro hev
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hv1 : AW v = ν₀ • v := by
      have h := hv.1
      rwa [Module.End.mem_eigenspace_iff] at h
    have hvE : A (v : E) = ν₀ • (v : E) := by
      have h := congrArg (fun z : W => (z : E)) hv1
      simpa [hAWval] using h
    obtain ⟨s, hs⟩ := hker (v : E) hvE
    have hvW : ⟪ψ₀, (v : E)⟫ = 0 := (hmemW _).mp v.2
    rw [hs, real_inner_smul_right, hnorm, mul_one] at hvW
    have hzero : (v : E) = 0 := by rw [hs, hvW, zero_smul]
    exact hv.2 (Subtype.ext hzero)
  -- so it lies in the resolvent set of the restriction
  have hmem : ν₀ ∈ resolventSet ℝ AW :=
    (hcompW.hasEigenvalue_or_mem_resolventSet hν₀).resolve_left hnoteig
  have hunit : IsUnit (algebraMap ℝ (W →L[ℝ] W) ν₀ - AW) := hmem
  obtain ⟨u, hu⟩ := hunit
  have halg : ∀ z : W, (algebraMap ℝ (W →L[ℝ] W) ν₀) z = ν₀ • z := by
    intro z
    rw [Algebra.algebraMap_eq_smul_one]
    simp
  have hQ1 : ∀ z : W, ν₀ • ((↑u⁻¹ : W →L[ℝ] W) z) - AW ((↑u⁻¹ : W →L[ℝ] W) z) = z := by
    intro z
    have h := u.mul_inv
    rw [hu] at h
    have hz : ((algebraMap ℝ (W →L[ℝ] W) ν₀ - AW) * (↑u⁻¹ : W →L[ℝ] W)) z = z := by
      rw [h]
      rfl
    rw [mul_apply_eq_comp] at hz
    rw [← halg]
    simpa using hz
  -- the projection onto the complement
  have hPmem : ∀ y : E,
      (ContinuousLinearMap.id ℝ E - (innerSL ℝ ψ₀).smulRight ψ₀) y ∈ W := by
    intro y
    rw [hmemW]
    simp [inner_sub_right, real_inner_smul_right, hnψ₀]
  set P : E →L[ℝ] W :=
    (ContinuousLinearMap.id ℝ E - (innerSL ℝ ψ₀).smulRight ψ₀).codRestrict W hPmem with hPdef
  have hPval : ∀ y : E, ((P y : E)) = y - ⟪ψ₀, y⟫ • ψ₀ := by
    intro y
    simp [hPdef]
  refine ⟨W.subtypeL.comp ((-(↑u⁻¹ : W →L[ℝ] W)).comp P), ?_, ?_⟩
  · intro y
    have hRval : (W.subtypeL.comp ((-(↑u⁻¹ : W →L[ℝ] W)).comp P)) y
        = (((-(↑u⁻¹ : W →L[ℝ] W)) (P y) : W) : E) := rfl
    have hkey := hQ1 (P y)
    have hkeyE : ν₀ • (((↑u⁻¹ : W →L[ℝ] W) (P y) : W) : E)
        - A ((((↑u⁻¹ : W →L[ℝ] W) (P y) : W)) : E) = y - ⟪ψ₀, y⟫ • ψ₀ := by
      have h := congrArg (fun z : W => (z : E)) hkey
      simpa [hAWval, hPval] using h
    rw [hRval]
    simp only [neg_apply, Submodule.coe_neg, map_neg, smul_neg]
    rw [sub_neg_eq_add, ← sub_eq_neg_add]
    exact hkeyE
  · intro y
    have hmemR : ((-(↑u⁻¹ : W →L[ℝ] W)) (P y) : W).val ∈ W :=
      ((-(↑u⁻¹ : W →L[ℝ] W)) (P y) : W).2
    exact (hmemW _).mp hmemR

/-- **Kato perturbation theory for a compact symmetric family.**  A simple nonzero eigenvalue of a compact
symmetric operator, perturbed differentiably, has a differentiable branch with a normalized eigenvector, and
the eigenvalue derivative is the expectation of the perturbation:

```text
nu'(c_0) = ⟪psi_0, w⟫.
```

Every input is structural: compactness and symmetry of the operator at the base point, simplicity of the
eigenvalue, and strict differentiability of the family with motion `w`. -/
theorem exists_normalized_branch_of_isCompactOperator [CompleteSpace E]
    {A : ℝ → E →L[ℝ] E} {c₀ ν₀ : ℝ} {ψ₀ w : E}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDeriv (A c₀) w) (c₀, ψ₀))
    (hcomp : IsCompactOperator (A c₀))
    (hsymm : ∀ u v : E, ⟪A c₀ u, v⟫ = ⟪u, A c₀ v⟫)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫ = 1) (hν₀ : ν₀ ≠ 0)
    (hker : ∀ φ : E, A c₀ φ = ν₀ • φ → ∃ s : ℝ, φ = s • ψ₀) :
    ∃ (ψ : ℝ → E) (ν : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫ = 1) ∧
      HasDerivAt ν ⟪ψ₀, w⟫ c₀ := by
  obtain ⟨R, hR, hRψ⟩ :=
    exists_pseudoInverse_of_isCompactOperator hcomp hsymm heig hnorm hν₀ hker
  exact exists_normalized_branch_deriv_eq_expectation hA hsymm heig hnorm hker hR hRψ

end GaloisForLFunctions.HTGeometry

end
