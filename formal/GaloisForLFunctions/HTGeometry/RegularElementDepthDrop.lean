import GaloisForLFunctions.HTGeometry.ExtMiddleProduct

/-!
# Depth drops by exactly one across a regular element

The third end of the depth transfer, and the short exact sequence that a nonzerodivisor defines:

```text
subsingleton_ext_quotient_of_shortExact
    ** Ext^n(X,B) and Ext^{n+1}(X,A) vanishing forces Ext^n(X,C) to vanish **
smulShortComplex, smulShortComplex_shortExact
    the sequence 0 → M → M → M ⧸ uM → 0 of a nonzerodivisor
subsingleton_ext_quotSMul
    ** Ext-vanishing below n+1 on M gives Ext-vanishing below n on M ⧸ uM **
```

Read through Rees, the last statement is that quotienting by a regular element drops the depth by at
most one — the step that lets a regular sequence be built one element at a time while keeping
control of what remains.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Abelian Limits ShortComplex
open scoped Pointwise

universe w v u

/-- **The quotient end of the depth transfer.**  If `Ext^n(X, B)` and `Ext^{n+1}(X, A)` vanish then
so does `Ext^n(X, C)`. -/
theorem subsingleton_ext_quotient_of_shortExact {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (X : C) {S : ShortComplex C} (hS : S.ShortExact) {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁)
    [Subsingleton (Ext.{w} X S.X₂ n₀)] [Subsingleton (Ext.{w} X S.X₁ n₁)] :
    Subsingleton (Ext.{w} X S.X₃ n₀) := by
  constructor
  intro a b
  suffices h : ∀ x₃ : Ext.{w} X S.X₃ n₀, x₃ = 0 by rw [h a, h b]
  intro x₃
  have hzero : x₃.comp hS.extClass hn = 0 := Subsingleton.elim _ _
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ X hS x₃ hn hzero
  rw [← hx₂, Subsingleton.elim x₂ 0]
  simp

section Regular

variable {R : Type u} [CommRing R] [CategoryTheory.HasExt.{w} (ModuleCat.{u} R)]

/-- The short complex `M → M → M ⧸ uM` of multiplication by `u` and the projection. -/
noncomputable def smulShortComplex (u : R) (M : ModuleCat.{u} R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.lsmul R M u))
    (ModuleCat.ofHom (Submodule.mkQ (u • (⊤ : Submodule R M))))
    (by
      apply ModuleCat.hom_ext
      ext m
      show Submodule.mkQ _ (u • m) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨m, Submodule.mem_top, rfl⟩)

omit [CategoryTheory.HasExt.{w} (ModuleCat.{u} R)] in
theorem smulShortComplex_shortExact {u : R} {M : ModuleCat.{u} R} (hu : IsSMulRegular M u) :
    (smulShortComplex u M).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro m hm
    obtain ⟨y, hy⟩ : ∃ y : (M : Type u), u • y = m := by
      have h0 : (Submodule.Quotient.mk (p := u • (⊤ : Submodule R M)) m) = 0 := hm
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h0
      obtain ⟨y, -, hy⟩ := h0
      exact ⟨y, hy⟩
    exact ⟨y, hy⟩
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    exact hu
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    exact Submodule.mkQ_surjective _

/-- **Depth drops by exactly one across a regular element.** -/
theorem subsingleton_ext_quotSMul {X : ModuleCat.{u} R} {u : R} {M : ModuleCat.{u} R}
    (hu : IsSMulRegular M u) {n : ℕ}
    (hM : ∀ i < n + 1, Subsingleton (Abelian.Ext.{w} X M i)) :
    ∀ i < n, Subsingleton (Abelian.Ext.{w} X (smulShortComplex u M).X₃ i) := by
  intro i hi
  haveI h1 : Subsingleton (Abelian.Ext.{w} X (smulShortComplex u M).X₂ i) := hM i (by omega)
  haveI h2 : Subsingleton (Abelian.Ext.{w} X (smulShortComplex u M).X₁ (i + 1)) :=
    hM (i + 1) (by omega)
  exact subsingleton_ext_quotient_of_shortExact X (smulShortComplex_shortExact hu) rfl

end Regular

end GaloisForLFunctions.HTGeometry
