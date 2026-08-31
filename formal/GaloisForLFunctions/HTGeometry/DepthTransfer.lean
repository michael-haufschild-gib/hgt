import GaloisForLFunctions.HTGeometry.ReesDepth

/-!
# Depth transfer along a short exact sequence, over a whole range

The depth lemma applies degree by degree; assembling it over `i < n₁` needs one extra case, `i = 0`,
where there is no preceding term of the long exact sequence.  There the transfer is immediate:
`Ext⁰(X, -)` is the hom functor and `A ⟶ B` is a monomorphism.

```text
subsingleton_ext_zero_of_mono      degree-zero vanishing passes to a subobject
subsingleton_ext_lt_of_shortExact
    ** Ext^i(X,B) = 0 for i < n₁ and Ext^i(X,C) = 0 for i < n₀ ⟹ Ext^i(X,A) = 0 for i < n₁ **
```

Read through `ReesDepth.lean`, this is `depth A ≥ min (depth B, depth C + 1)` in the form the
Cohen–Macaulay induction consumes: with the Mayer–Vietoris sequence
`0 → K[Δ] → K[del(v)] ⊕ K[st(v)] → K[lk(v)] → 0`, depth `d` for the middle term and `d-1` for the
right gives depth `d` for `K[Δ]`.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory CategoryTheory.Abelian

universe v u w

/-- Degree-zero `Ext` vanishing transfers along a monomorphism. -/
theorem subsingleton_ext_zero_of_mono {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (X : C) {A B : C} (f : A ⟶ B) [Mono f] [Subsingleton (Ext.{w} X B 0)] :
    Subsingleton (Ext.{w} X A 0) := by
  constructor
  intro a b
  apply Ext.homEquiv₀.injective
  apply (cancel_mono f).mp
  refine Ext.homEquiv₀.symm.injective ?_
  exact Subsingleton.elim _ _

/-- **The depth transfer along a short exact sequence.**  If `Ext^i(X, B)` vanishes for `i < n₁` and
`Ext^i(X, C)` vanishes for `i < n₀` with `n₀ + 1 = n₁`, then `Ext^i(X, A)` vanishes for `i < n₁`. -/
theorem subsingleton_ext_lt_of_shortExact {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (X : C) {S : ShortComplex C} (hS : S.ShortExact) {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁)
    (hB : ∀ i < n₁, Subsingleton (Ext.{w} X S.X₂ i))
    (hC : ∀ i < n₀, Subsingleton (Ext.{w} X S.X₃ i)) :
    ∀ i < n₁, Subsingleton (Ext.{w} X S.X₁ i) := by
  intro i hi
  match i with
  | 0 =>
    haveI := hB 0 hi
    haveI : Mono S.f := hS.mono_f
    exact subsingleton_ext_zero_of_mono X S.f
  | (j + 1) =>
    haveI := hC j (by omega)
    haveI := hB (j + 1) hi
    exact subsingleton_ext_of_shortExact X hS (n₀ := j) (n₁ := j + 1) rfl

end GaloisForLFunctions.HTGeometry
