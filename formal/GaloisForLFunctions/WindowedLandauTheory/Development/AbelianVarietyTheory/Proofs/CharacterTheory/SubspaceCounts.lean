import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.RingTheory.Finiteness.Cardinality

/-! Count subspaces of prescribed dimension by the independent tuples that span them. -/

namespace GlobalTheory.SubspaceNumber

private theorem card_fibre {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (a : ℕ) (W : Submodule F V) (hW : Module.finrank F W = a) :
    Nat.card {s : {s : Fin a → V // LinearIndependent F s} //
      Submodule.span F (Set.range s.1) = W} = Nat.card {t : Fin a → W // LinearIndependent F t} := by
  symm
  have hspan (t : Fin a → W) (ht : LinearIndependent F t) :
      Submodule.span F (Set.range (W.subtype ∘ t)) = W := by
    have htop : Submodule.span F (Set.range t) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card ht, Fintype.card_fin, hW]
    rw [Set.range_comp, ← Submodule.map_span, htop, Submodule.map_top, Submodule.range_subtype]
  refine Nat.card_congr (Equiv.ofBijective
    (fun t => ⟨⟨W.subtype ∘ t.1, t.2.map' _ W.ker_subtype⟩, hspan t.1 t.2⟩) ⟨?_, ?_⟩)
  · intro t u h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun (congrArg (fun x => x.1.1) h) i
  · rintro ⟨⟨s, hs⟩, h⟩
    have hm (i : Fin a) : s i ∈ W := by
      rw [← h]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨⟨fun i => ⟨s i, hm i⟩, LinearIndependent.of_comp W.subtype hs⟩, rfl⟩

/-- Each subspace of dimension `a` has the same number of ordered bases. -/
theorem card_subspaces_mul (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (a : ℕ) (ha : a ≤ Module.finrank F V) :
    Nat.card {W : Submodule F V // Module.finrank F W = a} *
      ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) =
    ∏ i ∈ Finset.range a, (Nat.card F ^ Module.finrank F V - Nat.card F ^ i) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : Finite V := Module.finite_of_finite F
  letI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective
  letI : Fintype {W : Submodule F V // Module.finrank F W = a} := Fintype.ofFinite _
  let span : {s : Fin a → V // LinearIndependent F s} →
      {W : Submodule F V // Module.finrank F W = a} := fun s =>
    ⟨Submodule.span F (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩
  have hfib (W : {W : Submodule F V // Module.finrank F W = a}) : Nat.card {s // span s = W} =
      ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) := by
    obtain ⟨W, hW⟩ := W
    have e : {s // span s = ⟨W, hW⟩} ≃ {s : {s : Fin a → V // LinearIndependent F s} //
        Submodule.span F (Set.range s.1) = W} :=
      Equiv.subtypeEquivRight (fun s => Subtype.ext_iff)
    rw [Nat.card_congr e, card_fibre a W hW, card_linearIndependent hW.ge, hW,
      Finset.prod_range, Nat.card_eq_fintype_card]
  have h := card_linearIndependent (K := F) (V := V) ha
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv span), Nat.card_sigma] at h
  simp_rw [hfib] at h
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  rw [h, Finset.prod_range]

end GlobalTheory.SubspaceNumber
