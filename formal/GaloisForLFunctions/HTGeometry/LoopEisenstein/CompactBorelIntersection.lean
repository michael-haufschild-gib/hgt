import GaloisForLFunctions.HTGeometry.LoopEisenstein.RealCompactSigns
import GaloisForLFunctions.HTGeometry.LoopEisenstein.SimpleMatrixWords
import GaloisForLFunctions.HTGeometry.LoopEisenstein.SubgroupAlternatingWords

/-!
# The exact compact–Borel intersection

An amalgamated-product normal form supplies alternating words in the two
enlarged simple rotation groups. Outside their common sign torus, every
source rotation has nonzero lower-left entry. Its projected word has a
nonzero negative Laurent boundary coefficient, hence cannot lie in Borel.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2

open GaloisForLFunctions.RHTower

noncomputable section

/-- Actual central-sign and rotation factors of an enlarged simple element. -/
def enlargedSimpleFactors (i : Bool) (g : enlargedSimpleCompact i) :
    realSignUnits × upperHalfPlaneStabilizer := Classical.choose g.property

theorem enlargedSimpleFactors_spec (i : Bool) (g : enlargedSimpleCompact i) :
    signRotationHom i (enlargedSimpleFactors i g) = (g : LoopSL2 ℝ) :=
  Classical.choose_spec g.property

/-- The matrix source of a letter, with its finite or affine index retained. -/
def enlargedSimpleSource (p : Σ i, enlargedSimpleCompact i) : Bool × SL2 ℝ :=
  (p.1, ((enlargedSimpleFactors p.1 p.2).2 : SL2 ℝ))

theorem enlargedSimpleSource_nontriangular (p : Σ i, enlargedSimpleCompact i)
    (hp : (p.2 : LoopSL2 ℝ) ∉ signTorus) : (enlargedSimpleSource p).2 1 0 ≠ 0 := by
  intro hc
  have h := signRotationHom_mem_signTorus_of_triangular p.1
    (enlargedSimpleFactors p.1 p.2).1 (enlargedSimpleFactors p.1 p.2).2 hc
  rw [enlargedSimpleFactors_spec] at h
  exact hp h

theorem projection_enlargedSimpleSource (p : Σ i, enlargedSimpleCompact i) :
    projection ℝ (p.2 : LoopSL2 ℝ) =
      simpleMatrixEmbedding ℝ (enlargedSimpleSource p).1 (enlargedSimpleSource p).2 := by
  rw [← enlargedSimpleFactors_spec p.1 p.2]
  change projection ℝ (centralEmbedding ℝ (enlargedSimpleFactors p.1 p.2).1 *
    simpleRotationHom p.1 (enlargedSimpleFactors p.1 p.2).2) = _
  rw [map_mul, projection_centralEmbedding, one_mul]
  rcases p with ⟨i, g⟩
  cases i <;> rfl

private theorem enlargedSimpleSource_chain (L : List (Σ i, enlargedSimpleCompact i)) :
    List.IsChain (fun p q : Σ i, enlargedSimpleCompact i => p.1 ≠ q.1) L →
      List.IsChain (fun p q : Bool × SL2 ℝ => p.1 ≠ q.1) (L.map enlargedSimpleSource) := by
  induction L with
  | nil => simp
  | cons p tail ih =>
    intro hl
    cases tail with
    | nil => simp
    | cons q rest =>
      have h := List.isChain_cons_cons.1 hl
      apply List.isChain_cons_cons.2
      exact ⟨h.1, ih h.2⟩

theorem projection_enlargedSimpleWord (L : List (Σ i, enlargedSimpleCompact i)) :
    projection ℝ (L.map (fun p => (p.2 : LoopSL2 ℝ))).prod =
      simpleMatrixWord ℝ (L.map enlargedSimpleSource) := by
  rw [map_list_prod, simpleMatrixWord, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  exact projection_enlargedSimpleSource p

/-- Every nonempty reduced alternating rotation word lies outside the positive Borel. -/
theorem alternating_enlargedSimpleWord_not_mem_borel
    (L : List (Σ i, enlargedSimpleCompact i)) (hne : L ≠ [])
    (hred : ∀ p ∈ L, (p.2 : LoopSL2 ℝ) ∉ signTorus)
    (halt : List.IsChain (fun p q : Σ i, enlargedSimpleCompact i => p.1 ≠ q.1) L) :
    (L.map (fun p => (p.2 : LoopSL2 ℝ))).prod ∉ positiveBorel ℝ := by
  intro hb
  have hi := projection_mem_laurentIwahori ℝ hb
  rw [projection_enlargedSimpleWord] at hi
  apply alternating_simpleMatrixWord_not_mem_iwahori ℝ (L.map enlargedSimpleSource) _ _
    (enlargedSimpleSource_chain L halt) hi
  · intro he
    exact hne (List.map_eq_nil_iff.1 he)
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact enlargedSimpleSource_nontriangular p (hred p hp)

/-- The actual generated rotation subgroup meets Borel in exactly its four sign elements. -/
theorem realCompact_inf_positiveBorel : realCompact ⊓ positiveBorel ℝ = signTorus := by
  apply le_antisymm
  · intro g hg
    have hk : g ∈ enlargedSimpleCompact false ⊔ enlargedSimpleCompact true := by
      rw [enlargedSimpleCompact_sup]
      exact hg.1
    rcases subgroup_join_base_or_alternating enlargedSimpleCompact signTorus
        signTorus_le_enlargedSimpleCompact hk with hm | hw
    · exact hm
    · obtain ⟨L, hne, hred, halt, he⟩ := hw
      exact False.elim (alternating_enlargedSimpleWord_not_mem_borel L hne hred halt (he.symm ▸ hg.2))
  · exact le_inf
      (le_trans (signTorus_le_enlargedSimpleCompact false) (enlargedSimpleCompact_le_realCompact false))
      signTorus_le_positiveBorel

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2
