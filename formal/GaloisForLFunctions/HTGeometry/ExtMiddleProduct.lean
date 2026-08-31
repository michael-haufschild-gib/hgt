import GaloisForLFunctions.HTGeometry.DepthTransfer

/-!
# `Ext`-vanishing at the middle of a short exact sequence, and for products

```text
subsingleton_ext_middle_of_shortExact       both outer terms vanish ⟹ the middle vanishes
subsingleton_ext_middle_lt_of_shortExact    the same over a range of degrees
prodShortComplex, prodShortComplex_shortExact   0 → A → A × B → B → 0
subsingleton_ext_prod                       ** Ext-vanishing passes to a binary product **
```

The middle lemma is `Ext.covariant_sequence_exact₂`: a class in `Ext^n(X, B)` that dies in
`Ext^n(X, C)` comes from `Ext^n(X, A)`, and that group is zero.

The product case is what the Cohen–Macaulay induction needs for its middle term
`K[del(v)] ⊕ K[st(v)]`: depth for a direct sum is the minimum of the depths, and the direction
needed here — both summands deep ⟹ the sum is deep — is exactly `subsingleton_ext_prod`.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory CategoryTheory.Abelian

universe v u w

/-- **`Ext`-vanishing at the middle of a short exact sequence.**  If the two outer terms have
vanishing `Ext` in a degree, so does the middle. -/
theorem subsingleton_ext_middle_of_shortExact {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (X : C) {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ}
    [Subsingleton (Ext.{w} X S.X₁ n)] [Subsingleton (Ext.{w} X S.X₃ n)] :
    Subsingleton (Ext.{w} X S.X₂ n) := by
  constructor
  intro a b
  suffices h : ∀ x₂ : Ext.{w} X S.X₂ n, x₂ = 0 by rw [h a, h b]
  intro x₂
  have hzero : x₂.comp (Ext.mk₀ S.g) (add_zero n) = 0 := Subsingleton.elim _ _
  obtain ⟨x₁, hx₁⟩ := Ext.covariant_sequence_exact₂ X hS x₂ hzero
  rw [← hx₁, Subsingleton.elim x₁ 0]
  simp

theorem subsingleton_ext_middle_lt_of_shortExact {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (X : C) {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ}
    (h1 : ∀ i < n, Subsingleton (Ext.{w} X S.X₁ i))
    (h3 : ∀ i < n, Subsingleton (Ext.{w} X S.X₃ i)) :
    ∀ i < n, Subsingleton (Ext.{w} X S.X₂ i) := by
  intro i hi
  haveI := h1 i hi
  haveI := h3 i hi
  exact subsingleton_ext_middle_of_shortExact X hS

section Product

variable {R : Type u} [Ring R]

/-- The split short exact sequence of a binary product of modules. -/
noncomputable def prodShortComplex (A B : ModuleCat.{u} R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.inl R A B))
    (ModuleCat.ofHom (LinearMap.snd R A B))
    (by
      apply ModuleCat.hom_ext
      ext a
      simp)

theorem prodShortComplex_shortExact (A B : ModuleCat.{u} R) :
    (prodShortComplex A B).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    rintro ⟨a, b⟩ hab
    have hb : b = 0 := hab
    refine ⟨a, ?_⟩
    show (a, (0 : B)) = (a, b)
    rw [hb]
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    intro a b hab
    exact congrArg Prod.fst hab
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    intro b
    exact ⟨(0, b), rfl⟩

variable [CategoryTheory.HasExt.{w} (ModuleCat.{u} R)]

/-- **`Ext`-vanishing passes to a binary product.** -/
theorem subsingleton_ext_prod (X : ModuleCat.{u} R) (A B : ModuleCat.{u} R) {n : ℕ}
    (hA : Subsingleton (Ext.{w} X A n)) (hB : Subsingleton (Ext.{w} X B n)) :
    Subsingleton (Ext.{w} X (prodShortComplex A B).X₂ n) := by
  haveI : Subsingleton (Ext.{w} X (prodShortComplex A B).X₁ n) := hA
  haveI : Subsingleton (Ext.{w} X (prodShortComplex A B).X₃ n) := hB
  exact subsingleton_ext_middle_of_shortExact X (prodShortComplex_shortExact A B)

end Product


end GaloisForLFunctions.HTGeometry
