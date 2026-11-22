import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ImprimitiveRepresentations
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.RepresentationTheory.Maschke

/-! Monomial bases for representations of finite nilpotent groups in nonmodular characteristic. -/

open Module

namespace GlobalTheory.CuspGL

private theorem exists_monomial_basis_of_imprimitive (k : Type) [Field k] (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (T : Subgroup G) (W : Submodule k V)
    (hind : iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)))
    (hsup : ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤)
    (hW : ∃ (n : ℕ) (b : Module.Basis (Fin n) k W), ∀ t ∈ T, ∀ i : Fin n,
      ∃ (j : Fin n) (c : k), ρ t (b i : V) = c • (b j : V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  classical
  obtain ⟨n, b, hb⟩ := hW
  have hinj : ∀ g : G, Function.Injective (ρ g) := by
    intro g x y h
    have h2 := congrArg (ρ g⁻¹) h
    simpa [← Module.End.mul_apply, ← map_mul] using h2
  have hint : DirectSum.IsInternal (fun q : G ⧸ T => W.map (ρ q.out)) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  let bq : ∀ q : G ⧸ T, Module.Basis (Fin n) k (W.map (ρ q.out)) := fun q =>
    b.map (Submodule.equivMapOfInjective (ρ q.out) (hinj _) W)
  let B := hint.collectedBasis bq
  have hB : ∀ (q : G ⧸ T) (i : Fin n), B ⟨q, i⟩ = ρ q.out (b i : V) := by
    intro q i
    simp [B, bq]
  haveI : Fintype (G ⧸ T) := Fintype.ofFinite _
  let e := Fintype.equivFin (Σ _ : G ⧸ T, Fin n)
  refine ⟨_, B.reindex e, fun g i => ?_⟩
  obtain ⟨⟨q, i⟩, rfl⟩ := e.surjective i
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T (g * q.out)
  obtain ⟨j, c, hj⟩ := hb (t⁻¹ : T) (t⁻¹).2 i
  refine ⟨e ⟨(QuotientGroup.mk (g * q.out) : G ⧸ T), j⟩, c, ?_⟩
  simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
  rw [← map_smul, ← hj, ht, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp

private theorem exists_monomial_basis_of_isCompl {k : Type} [Field k] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (U U' : Submodule k V) (h : IsCompl U U')
    (hU : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V))
    (hU' : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U'), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  obtain ⟨n, b, hb⟩ := hU
  obtain ⟨n', b', hb'⟩ := hU'
  let B := (b.prod b').map (Submodule.prodEquivOfIsCompl U U' h)
  have h1 : ∀ i, B (Sum.inl i) = (b i : V) := by
    intro i
    simp [B, Module.Basis.prod_apply]
  have h2 : ∀ i, B (Sum.inr i) = (b' i : V) := by
    intro i
    simp [B, Module.Basis.prod_apply]
  refine ⟨n + n', B.reindex finSumFinEquiv, fun g i => ?_⟩
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · obtain ⟨j, c, hj⟩ := hb g i
    refine ⟨finSumFinEquiv (Sum.inl j), c, ?_⟩
    simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, h1, hj]
  · obtain ⟨j, c, hj⟩ := hb' g i
    refine ⟨finSumFinEquiv (Sum.inr j), c, ?_⟩
    simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, h2, hj]

/-- Over an algebraically closed field of characteristic prime to the group order,
a nilpotent group representation admits a basis of lines permuted by the group. -/
theorem exists_monomial_basis_of_nilpotent (k : Type) [Field k] (G : Type) [Group G]
    [Finite G] [Group.IsNilpotent G] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k]
    (hcard : (Nat.card G : k) ≠ 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  have key : ∀ (m : ℕ) (G : Type) [Group G] [Finite G] [Group.IsNilpotent G]
      (V : Type) [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k],
      Nat.card G + Module.finrank k V = m → (Nat.card G : k) ≠ 0 →
      ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
        ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro G _ _ _ V _ _ _ ρ _ hm hcard
      by_cases h0 : Module.finrank k V = 0
      · exact ⟨0, Module.finBasisOfFinrankEq k V h0, fun g i => i.elim0⟩
      by_cases hirr : ρ.IsIrreducible
      · rcases finrank_eq_one_or_imprimitive k G V ρ hirr with h1 | ⟨T, W, hT, hW, hind, hsup⟩
        · let b := Module.finBasisOfFinrankEq k V h1
          refine ⟨1, b, fun g i => ⟨0, b.repr (ρ g (b i)) 0, ?_⟩⟩
          have := b.sum_repr (ρ g (b i))
          rw [Fin.sum_univ_one] at this
          exact this.symm
        · refine exists_monomial_basis_of_imprimitive k G V ρ T W hind hsup ?_
          let σ : Subrepresentation (ρ.comp T.subtype : Representation k T V) :=
            ⟨W, fun t w hw => hW t t.2 w hw⟩
          have hlt : Nat.card T < Nat.card G := by
            have := T.card_le_card_group
            have h2 : Nat.card T ≠ Nat.card G := fun H => hT (Subgroup.eq_top_of_card_eq T H)
            omega
          have hle : Module.finrank k W ≤ Module.finrank k V := Submodule.finrank_le W
          have hc : (Nat.card T : k) ≠ 0 := by
            intro H
            obtain ⟨d, hd⟩ := T.card_subgroup_dvd_card
            apply hcard
            rw [hd, Nat.cast_mul, H, zero_mul]
          obtain ⟨n, b, hb⟩ := ih _ (by omega) T W σ.toRepresentation rfl hc
          refine ⟨n, b, fun t ht i => ?_⟩
          obtain ⟨j, c, hj⟩ := hb ⟨t, ht⟩ i
          exact ⟨j, c, congrArg Subtype.val hj⟩
      · haveI : NeZero (Nat.card G : k) := ⟨hcard⟩
        haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h0)
        haveI : Nontrivial (Subrepresentation ρ) :=
          ⟨⊥, ⊤, fun H => (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤)
            (congrArg Subrepresentation.toSubmodule H)⟩
        have hex : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
          by_contra H
          push Not at H
          exact hirr ⟨fun U => by
            by_cases hU : U = ⊥
            · exact Or.inl hU
            · exact Or.inr (H U hU)⟩
        obtain ⟨U, hU0, hU1⟩ := hex
        obtain ⟨U', hUU'⟩ := exists_isCompl U
        have hcompl : IsCompl U.toSubmodule U'.toSubmodule :=
          ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hUU'.inf_eq_bot),
            codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hUU'.sup_eq_top)⟩
        have hsub : ∀ S : Subrepresentation ρ, S ≠ ⊤ →
            ∃ (n : ℕ) (b : Module.Basis (Fin n) k S.toSubmodule), ∀ (g : G) (i : Fin n),
              ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V) := by
          intro S hS
          have hlt : Module.finrank k S.toSubmodule < Module.finrank k V :=
            Submodule.finrank_lt (fun H => hS (Subrepresentation.ext H))
          obtain ⟨n, b, hb⟩ := ih _ (by omega) G S.toSubmodule S.toRepresentation rfl hcard
          refine ⟨n, b, fun g i => ?_⟩
          obtain ⟨j, c, hj⟩ := hb g i
          exact ⟨j, c, congrArg Subtype.val hj⟩
        refine exists_monomial_basis_of_isCompl ρ _ _ hcompl (hsub U hU1) (hsub U' ?_)
        rintro rfl
        exact hU0 (by simpa using hUU'.inf_eq_bot)
  exact key _ G V ρ rfl hcard

end GlobalTheory.CuspGL
