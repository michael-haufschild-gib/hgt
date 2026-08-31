import GaloisForLFunctions.HTGeometry.MayerVietorisShortExact

/-!
# The depth lemma

For a short exact sequence `0 → A → B → C → 0` in an abelian category, exactness of the long `Ext`
sequence at `Ext^{n₁}(X, A)` gives

```text
Ext^{n₀}(X, C) = 0  and  Ext^{n₁}(X, B) = 0   ⟹   Ext^{n₁}(X, A) = 0        (n₀ + 1 = n₁)
```

which, once depth is read off from `Ext`-vanishing, is `depth A ≥ min (depth B, depth C + 1)`.

```text
subsingleton_ext_of_shortExact   ** the depth lemma **
subsingleton_ext_mv              its instance along the Mayer–Vietoris sequence of two ideals
```

The proof is `Ext.covariant_sequence_exact₁`: a class in `Ext^{n₁}(X, A)` that dies in
`Ext^{n₁}(X, B)` comes from `Ext^{n₀}(X, C)`, and that group is zero.

With `I = I_{del(v)}` and `J = I_{st(v)}` — so that `I ⊓ J = I_Δ` and `I ⊔ J = I_{lk(v)}` by
`faceFamilyIdeal_deletion_inf_star` and `faceFamilyIdeal_link_eq_sup` — `subsingleton_ext_mv` is
exactly the inductive step of the Cohen–Macaulay argument for a simplicial complex at a non-cone
vertex.  This is step 3 of the route recorded on the Hankel card; what remains is step 2, the
translation between `Ext`-vanishing and regular sequences, for which mathlib's Rees theorem and the
bridge `isRingRegularSeq_iff_isRegular` are in place.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory CategoryTheory.Abelian

universe v u w

/-- **The depth lemma, in `Ext` form.**  For a short exact sequence `0 → A → B → C → 0`, if
`Ext^{n₀}(X, C)` and `Ext^{n₁}(X, B)` vanish with `n₀ + 1 = n₁`, then `Ext^{n₁}(X, A)` vanishes.

This is exactness of the long `Ext` sequence at `Ext^{n₁}(X, A)`, and it is the statement
`depth A ≥ min (depth B, depth C + 1)` once depth is read off from `Ext`-vanishing. -/
theorem subsingleton_ext_of_shortExact {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (X : C) {S : ShortComplex C} (hS : S.ShortExact) {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁)
    [Subsingleton (Ext.{w} X S.X₃ n₀)] [Subsingleton (Ext.{w} X S.X₂ n₁)] :
    Subsingleton (Ext.{w} X S.X₁ n₁) := by
  constructor
  intro a b
  suffices h : ∀ x₁ : Ext.{w} X S.X₁ n₁, x₁ = 0 by rw [h a, h b]
  intro x₁
  have hzero : x₁.comp (Ext.mk₀ S.f) (add_zero n₁) = 0 := Subsingleton.elim _ _
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ X hS x₁ hzero hn
  rw [← hx₃, Subsingleton.elim x₃ 0]
  simp

section MayerVietoris

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

/-- **The depth lemma along the Mayer–Vietoris sequence of two ideals.**  With
`I = I_{del(v)}` and `J = I_{st(v)}` — where `I ⊓ J = I_Δ` and `I ⊔ J = I_{lk(v)}` — this says
`depth K[Δ] ≥ min (depth (K[del(v)] ⊕ K[st(v)]), depth K[lk(v)] + 1)`. -/
theorem subsingleton_ext_mv (I J : Ideal R) (X : ModuleCat.{u} R) {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁)
    [Subsingleton (Ext.{w} X (mvShortComplex I J).X₃ n₀)]
    [Subsingleton (Ext.{w} X (mvShortComplex I J).X₂ n₁)] :
    Subsingleton (Ext.{w} X (mvShortComplex I J).X₁ n₁) :=
  subsingleton_ext_of_shortExact X (mvShortComplex_shortExact I J) hn

end MayerVietoris


end GaloisForLFunctions.HTGeometry
