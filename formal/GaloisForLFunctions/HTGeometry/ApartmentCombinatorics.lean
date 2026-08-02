import GaloisForLFunctions.HTGeometry.ApartmentChains

/-!
# The size and shape of an apartment

The apartment of a frame with `N` vectors has one vertex for every nonempty proper coordinate set
and one chamber for every ordering of the frame, and the `k`-th vertex of every chamber is a
coordinate set with `k` elements.  So it has `2 ^ N - 2` vertices, `N !` chambers, and its chambers
alternate between coordinate sets of consecutive sizes.

For `N = 3` this is the hexagon: six vertices, six chambers, each chamber a single coordinate line
inside a coordinate plane.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

section Vertices

variable {ι : Type u} [Finite ι] [Nonempty ι]

/-- **The vertices of an apartment are the nonempty proper coordinate sets**, so there are
`2 ^ N - 2` of them. -/
theorem card_properPart_set : Nat.card (properPart (Set ι)) = 2 ^ Nat.card ι - 2 := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hpair : Nat.card {S : Set ι // S = ∅ ∨ S = Set.univ} = 2 := by
    have hne : (∅ : Set ι) ≠ Set.univ := Set.empty_ne_univ
    have h := Set.ncard_pair hne
    show Nat.card ↥({∅, Set.univ} : Set (Set ι)) = 2
    rw [Nat.card_coe_set_eq, h]
  have hequiv : properPart (Set ι) ≃ {S : Set ι // ¬ (S = ∅ ∨ S = Set.univ)} :=
    Equiv.subtypeEquivRight fun S => by
      constructor
      · rintro ⟨h1, h2⟩ (rfl | rfl)
        · exact absurd h1 (lt_irrefl _)
        · exact absurd h2 (lt_irrefl _)
      · intro h
        exact ⟨lt_of_le_of_ne bot_le fun hc => h (Or.inl hc.symm),
          lt_of_le_of_ne le_top fun hc => h (Or.inr hc)⟩
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at *
  rw [Fintype.card_subtype_compl, Fintype.card_set, hpair]

end Vertices

section Chambers

variable {ι : Type u} [Finite ι] {n : ℕ}

/-- **The chambers of an apartment are the orderings of its frame**, so there are `N !` of them. -/
theorem card_apartmentChambers (hN : Nat.card ι = n + 2) :
    Nat.card ((nerve (properPart (Set ι))).nonDegenerate n) = Nat.factorial (n + 2) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = n + 2 := by rw [← Nat.card_eq_fintype_card, hN]
  have h1 : Nat.card ((nerve (properPart (Set ι))).nonDegenerate n)
      = Nat.card (Fin (n + 2) ≃ ι) := Nat.card_congr (apartmentChamberEquiv hN).symm
  rw [h1, Nat.card_eq_fintype_card,
    Fintype.card_equiv (Fintype.equivFinOfCardEq hcard).symm, Fintype.card_fin]

/-- **The `k`-th vertex of every chamber is a coordinate set with `k + 1` elements.** -/
theorem ncard_chamber_vertex (hN : Nat.card ι = n + 2)
    (y : (nerve (properPart (Set ι))).nonDegenerate n) (i : Fin (n + 1)) :
    ((((y : (nerve (properPart (Set ι))) _⦋n⦌)).obj i : properPart (Set ι)) : Set ι).ncard
      = (i : ℕ) + 1 :=
  apartment_chain_ncard hN (by have h : ((unop (op ⦋n⦌)).len) = n := rfl; omega)
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono
      (y : (nerve (properPart (Set ι))) _⦋n⦌)).1 y.2) i

end Chambers

section Hexagon

variable {ι : Type u} [Finite ι] [Nonempty ι]

/-- **For a three-vector frame the apartment is a hexagon.**  It has six vertices and six chambers,
and every chamber is a coordinate line inside a coordinate plane: the alternation of single-observer
horizons with pairwise common-horizon fields. -/
theorem apartment_hexagon (hN : Nat.card ι = 3) :
    Nat.card (properPart (Set ι)) = 6
      ∧ Nat.card ((nerve (properPart (Set ι))).nonDegenerate 1) = 6
      ∧ ∀ (y : (nerve (properPart (Set ι))).nonDegenerate 1),
          ((((y : (nerve (properPart (Set ι))) _⦋1⦌)).obj 0 : properPart (Set ι)) : Set ι).ncard = 1
            ∧ ((((y : (nerve (properPart (Set ι))) _⦋1⦌)).obj 1 :
              properPart (Set ι)) : Set ι).ncard = 2 := by
  refine ⟨?_, ?_, fun y => ⟨?_, ?_⟩⟩
  · rw [card_properPart_set, hN]
    norm_num
  · rw [card_apartmentChambers (show Nat.card ι = 1 + 2 by omega)]
    norm_num [Nat.factorial]
  · exact ncard_chamber_vertex (show Nat.card ι = 1 + 2 by omega) y 0
  · exact ncard_chamber_vertex (show Nat.card ι = 1 + 2 by omega) y 1

end Hexagon

end GaloisForLFunctions.HTGeometry
