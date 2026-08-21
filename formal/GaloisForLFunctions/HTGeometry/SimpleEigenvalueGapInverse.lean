import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The pseudo-inverse at a gapped simple eigenvalue

Perturbation theory for a simple eigenvalue needs a *pseudo-inverse* of `T = A - nu_0`: a bounded operator `R`
with

```text
T (R y) = y - ⟪psi_0, y⟫ psi_0,      ⟪psi_0, R y⟫ = 0,
```

i.e. an inverse of `T` on the orthogonal complement of the eigendirection.  The corpus already builds `R` for a
*compact* symmetric operator at a *nonzero* eigenvalue, through the Fredholm alternative
(`SimpleEigenvalueCompactBranch`).  Neither restriction is intrinsic: what perturbation theory really needs is
that the eigenvalue be **isolated**, and for a bounded symmetric operator that is exactly a transverse
coercivity bound

```text
⟪psi_0, phi⟫ = 0  →  gamma ‖phi‖ ≤ ‖T phi‖,      gamma > 0.
```

This file constructs `R` from that bound alone — no compactness, no Fredholm theory, and `nu_0 = 0` allowed.
The mechanism is elementary: on `W = psi_0^perp` the restriction of `T` is injective (simplicity), bounded
below (the gap), hence has closed range; and its range has trivial orthogonal complement inside `W`, because a
vector of `W` orthogonal to `T W` is killed by `T` and therefore lies in the eigendirection.  Closed plus dense
is everything, so the restriction is bijective, and the Banach inverse composed with the transverse projector
`y ↦ y - ⟪psi_0, y⟫ psi_0` is `R`.

A second theorem records that in finite dimensions the gap is *free*: simplicity alone already forces one,
since an injective endomorphism of a finite-dimensional space is invertible and its inverse is bounded.

Everything is over an arbitrary `RCLike` field, so the real and complex cases are both covered.
-/

noncomputable section

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A symmetric operator killing `ψ₀` restricts to the orthogonal complement of `ψ₀`. -/
private theorem gapRestrict {T : E →L[𝕜] E} {ψ₀ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜) (hTψ : T ψ₀ = 0) :
    ∃ f : ((𝕜 ∙ ψ₀)ᗮ : Submodule 𝕜 E) →L[𝕜] ((𝕜 ∙ ψ₀)ᗮ : Submodule 𝕜 E),
      ∀ x : ((𝕜 ∙ ψ₀)ᗮ : Submodule 𝕜 E), ((f x : E)) = T (x : E) := by
  have hperp : ∀ z : E, ⟪ψ₀, T z⟫_𝕜 = 0 := by
    intro z
    have h := hsymm ψ₀ z
    rw [hTψ, inner_zero_left] at h
    exact h.symm
  exact ⟨(T.comp (Submodule.subtypeL _)).codRestrict _
    (fun x => Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hperp _)), fun _ => rfl⟩

/-- **The pseudo-inverse of a gapped simple eigenvalue.**  For a bounded symmetric `T` with `T psi_0 = 0`,
kernel spanned by `psi_0`, and a transverse coercivity bound `gamma ‖phi‖ ≤ ‖T phi‖` on `psi_0^perp`, there is a
bounded `R` inverting `T` modulo the eigendirection:

```text
T (R y) = y - ⟪psi_0, y⟫ psi_0,      ⟪psi_0, R y⟫ = 0.
```

No compactness and no restriction on the eigenvalue are used. -/
theorem exists_pseudoInverse_of_gap [CompleteSpace E]
    {T : E →L[𝕜] E} {ψ₀ : E} {γ : ℝ}
    (hsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜)
    (hTψ : T ψ₀ = 0) (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ₀)
    (hγ : 0 < γ)
    (hgap : ∀ φ : E, ⟪ψ₀, φ⟫_𝕜 = 0 → γ * ‖φ‖ ≤ ‖T φ‖) :
    ∃ R : E →L[𝕜] E, (∀ y : E, T (R y) = y - ⟪ψ₀, y⟫_𝕜 • ψ₀) ∧ (∀ y : E, ⟪ψ₀, R y⟫_𝕜 = 0) := by
  classical
  set W : Submodule 𝕜 E := (𝕜 ∙ ψ₀)ᗮ with hWdef
  have hmemW : ∀ x : E, x ∈ W ↔ ⟪ψ₀, x⟫_𝕜 = 0 := fun x =>
    Submodule.mem_orthogonal_singleton_iff_inner_right
  haveI hWc : CompleteSpace W := (Submodule.isClosed_orthogonal _).completeSpace_coe
  have hperpRange : ∀ z : E, ⟪ψ₀, T z⟫_𝕜 = 0 := by
    intro z
    have h := hsymm ψ₀ z
    rw [hTψ, inner_zero_left] at h
    exact h.symm
  obtain ⟨TW, hTWcoe⟩ := gapRestrict hsymm hTψ
  -- a transverse vector in the kernel is zero
  have hWzero : ∀ x : W, T (x : E) = 0 → x = 0 := by
    intro x hx
    obtain ⟨s, hs⟩ := hker _ hx
    have hxW : ⟪ψ₀, (x : E)⟫_𝕜 = 0 := (hmemW _).1 x.2
    rw [hs, inner_smul_right, hnorm, mul_one] at hxW
    refine Subtype.ext ?_
    rw [hs, hxW, zero_smul]
    rfl
  have hinj : LinearMap.ker (TW : W →ₗ[𝕜] W) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    refine hWzero x ?_
    rw [← hTWcoe x]
    have h : TW x = 0 := hx
    rw [h]
    rfl
  -- the gap makes the restriction bounded below, so its range is closed
  have hbound : ∀ x : W, ‖x‖ ≤ γ⁻¹ * ‖TW x‖ := by
    intro x
    have h := hgap (x : E) ((hmemW _).1 x.2)
    have hn : ‖TW x‖ = ‖T (x : E)‖ := by rw [← hTWcoe x]; rfl
    have hnx : ‖x‖ = ‖(x : E)‖ := rfl
    rw [hn, hnx, inv_mul_eq_div, le_div_iff₀ hγ, mul_comm]
    exact h
  have hclosedRange : IsClosed (Set.range TW) := by
    have hanti : AntilipschitzWith ⟨γ⁻¹, (inv_pos.mpr hγ).le⟩ (TW) :=
      TW.antilipschitz_of_bound hbound
    exact hanti.isClosed_range TW.lipschitz.uniformContinuous
  have hKclosed : IsClosed ((LinearMap.range (TW : W →ₗ[𝕜] W) : Submodule 𝕜 W) : Set W) := by
    convert hclosedRange using 1
    ext z
    simp [LinearMap.mem_range]
  haveI : CompleteSpace (LinearMap.range (TW : W →ₗ[𝕜] W)) := hKclosed.completeSpace_coe
  haveI : (LinearMap.range (TW : W →ₗ[𝕜] W)).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  -- and dense: a transverse vector orthogonal to the range is killed by `T`
  have hKperp : (LinearMap.range (TW : W →ₗ[𝕜] W))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hy' : ∀ x : W, ⟪T (x : E), (y : E)⟫_𝕜 = 0 := by
      intro x
      have h := hy (TW x) (LinearMap.mem_range_self _ x)
      rw [Submodule.coe_inner, hTWcoe] at h
      exact h
    have hTy : ∀ z : E, ⟪z, T (y : E)⟫_𝕜 = 0 := by
      intro z
      have hz : z - ⟪ψ₀, z⟫_𝕜 • ψ₀ ∈ W := by
        rw [hmemW, inner_sub_right, inner_smul_right, hnorm, mul_one, sub_self]
      have h1 : ⟪z - ⟪ψ₀, z⟫_𝕜 • ψ₀, T (y : E)⟫_𝕜 = 0 := by
        have h := hy' ⟨z - ⟪ψ₀, z⟫_𝕜 • ψ₀, hz⟩
        rw [hsymm] at h
        exact h
      have h2 : ⟪(⟪ψ₀, z⟫_𝕜 : 𝕜) • ψ₀, T (y : E)⟫_𝕜 = 0 := by
        rw [inner_smul_left, hperpRange, mul_zero]
      have hsplit : ⟪z, T (y : E)⟫_𝕜
          = ⟪z - ⟪ψ₀, z⟫_𝕜 • ψ₀, T (y : E)⟫_𝕜 + ⟪(⟪ψ₀, z⟫_𝕜 : 𝕜) • ψ₀, T (y : E)⟫_𝕜 := by
        rw [inner_sub_left]; ring
      rw [hsplit, h1, h2, add_zero]
    exact hWzero y (inner_self_eq_zero.mp (hTy (T (y : E))))
  have hsurj : LinearMap.range (TW : W →ₗ[𝕜] W) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    exact hKperp
  obtain ⟨S, hS⟩ : ∃ S : W →L[𝕜] W, ∀ x : W, TW (S x) = x := by
    refine ⟨((ContinuousLinearEquiv.ofBijective TW hinj hsurj).symm : W →L[𝕜] W), fun x => ?_⟩
    have h1 : ((ContinuousLinearEquiv.ofBijective TW hinj hsurj : W ≃L[𝕜] W) : W →L[𝕜] W) = TW :=
      ContinuousLinearEquiv.coe_ofBijective _ _ _
    have h3 : ∀ z : W, (ContinuousLinearEquiv.ofBijective TW hinj hsurj) z = TW z :=
      fun z => congrArg (fun g : W →L[𝕜] W => g z) h1
    exact (h3 _).symm.trans (ContinuousLinearEquiv.apply_symm_apply _ _)
  obtain ⟨Pw, hPw⟩ : ∃ f : E →L[𝕜] W, ∀ y : E, ((f y : E)) = y - ⟪ψ₀, y⟫_𝕜 • ψ₀ := by
    refine ⟨(ContinuousLinearMap.id 𝕜 E - (innerSL 𝕜 ψ₀).smulRight ψ₀).codRestrict W ?_,
      fun _ => rfl⟩
    intro y
    rw [hmemW]
    show ⟪ψ₀, y - ⟪ψ₀, y⟫_𝕜 • ψ₀⟫_𝕜 = 0
    rw [inner_sub_right, inner_smul_right, hnorm, mul_one, sub_self]
  refine ⟨(Submodule.subtypeL W).comp (S.comp Pw), ?_, ?_⟩
  · intro y
    show T ((S (Pw y) : E)) = y - ⟪ψ₀, y⟫_𝕜 • ψ₀
    rw [← hTWcoe (S (Pw y)), hS, hPw]
  · intro y
    exact (hmemW _).1 (S (Pw y)).2

/-- **In finite dimensions simplicity already forces a gap.**  An injective endomorphism of a
finite-dimensional space is invertible and its inverse is bounded, so the transverse coercivity bound is
automatic. -/
theorem exists_gap_of_finiteDimensional [FiniteDimensional 𝕜 E]
    {T : E →L[𝕜] E} {ψ₀ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜)
    (hTψ : T ψ₀ = 0) (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ₀) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ φ : E, ⟪ψ₀, φ⟫_𝕜 = 0 → γ * ‖φ‖ ≤ ‖T φ‖ := by
  classical
  set W : Submodule 𝕜 E := (𝕜 ∙ ψ₀)ᗮ with hWdef
  have hmemW : ∀ x : E, x ∈ W ↔ ⟪ψ₀, x⟫_𝕜 = 0 := fun x =>
    Submodule.mem_orthogonal_singleton_iff_inner_right
  obtain ⟨TW, hTWcoe⟩ := gapRestrict hsymm hTψ
  have hWzero : ∀ x : W, T (x : E) = 0 → x = 0 := by
    intro x hx
    obtain ⟨s, hs⟩ := hker _ hx
    have hxW : ⟪ψ₀, (x : E)⟫_𝕜 = 0 := (hmemW _).1 x.2
    rw [hs, inner_smul_right, hnorm, mul_one] at hxW
    refine Subtype.ext ?_
    rw [hs, hxW, zero_smul]
    rfl
  have hinjfun : Function.Injective (TW : W →ₗ[𝕜] W) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine hWzero x ?_
    rw [← hTWcoe x]
    have h : TW x = 0 := hx
    rw [h]
    rfl
  have hbij : Function.Bijective (TW : W →ₗ[𝕜] W) :=
    ⟨hinjfun, LinearMap.surjective_of_injective hinjfun⟩
  set e : W ≃ₗ[𝕜] W := LinearEquiv.ofBijective (TW : W →ₗ[𝕜] W) hbij with hedef
  set ec : W ≃L[𝕜] W := e.toContinuousLinearEquiv with hecdef
  have hec : ∀ x : W, ec x = TW x := fun _ => rfl
  set M : ℝ := max ‖(ec.symm : W →L[𝕜] W)‖ 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨M⁻¹, inv_pos.mpr hM, ?_⟩
  intro φ hφ
  have hxmem : φ ∈ W := (hmemW φ).2 hφ
  have hkey : ‖(⟨φ, hxmem⟩ : W)‖ ≤ M * ‖TW (⟨φ, hxmem⟩ : W)‖ := by
    have h1 : ((ec.symm : W →L[𝕜] W)) (ec (⟨φ, hxmem⟩ : W)) = (⟨φ, hxmem⟩ : W) :=
      ec.symm_apply_apply _
    have h2 := (ec.symm : W →L[𝕜] W).le_opNorm (ec (⟨φ, hxmem⟩ : W))
    rw [h1, hec] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hn1 : ‖(⟨φ, hxmem⟩ : W)‖ = ‖φ‖ := rfl
  have hn2 : ‖TW (⟨φ, hxmem⟩ : W)‖ = ‖T φ‖ :=
    congrArg norm (hTWcoe (⟨φ, hxmem⟩ : W))
  rw [hn1, hn2] at hkey
  rw [inv_mul_eq_div, div_le_iff₀ hM, mul_comm]
  exact hkey

end GaloisForLFunctions.HTGeometry

end
