import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite automorphism avoidance and prime-torsion polygons

This file isolates the exact combinatorial mechanism behind complete hard
recurrence polygons.  A finite bad set pulled back by a finite family of
automorphisms covers at most the sum of its pullback cardinalities.  Hence at
least `|X| - |S| |A|` points avoid the bad set under every automorphism in the
family.

For the anchored prime-torsion phase group `(Fin d → ZMod p)`, every nonzero
scalar is an automorphism.  Thus a bad set of cardinality `N` excludes at most
`(p - 1) N` starting phases from having a completely avoiding nonidentity
power orbit.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Points whose images under every selected automorphism avoid `bad`. -/
def automorphismAvoidanceSet {X I : Type*} [Fintype X] [Fintype I]
    [DecidableEq X] (bad : Finset X) (indices : Finset I)
    (action : I → X ≃ X) : Finset X :=
  Finset.univ.filter fun x => ∀ i ∈ indices, action i x ∉ bad

/-- An automorphism pulls a finite set back without changing its cardinality. -/
theorem automorphism_preimage_card {X : Type*} [Fintype X] [DecidableEq X]
    (bad : Finset X) (e : X ≃ X) :
    (Finset.univ.filter fun x => e x ∈ bad).card = bad.card := by
  classical
  have hset :
      (Finset.univ.filter fun x => e x ∈ bad) =
        bad.map e.symm.toEmbedding := by
    ext x
    simp
  rw [hset, Finset.card_map]

/-- Union bound for failure of simultaneous finite automorphism avoidance. -/
theorem automorphismAvoidance_bad_card_le
    {X I : Type*} [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    (bad : Finset X) (indices : Finset I) (action : I → X ≃ X) :
    (Finset.univ \ automorphismAvoidanceSet bad indices action).card ≤
      indices.card * bad.card := by
  classical
  let pullback : I → Finset X :=
    fun i => Finset.univ.filter fun x => action i x ∈ bad
  have hsub :
      Finset.univ \ automorphismAvoidanceSet bad indices action ⊆
        indices.biUnion pullback := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      automorphismAvoidanceSet, Finset.mem_filter, not_forall, not_not] at hx
    obtain ⟨i, hiIndices, hiBad⟩ := hx
    exact Finset.mem_biUnion.mpr
      ⟨i, hiIndices, by simp [pullback, hiBad]⟩
  calc
    (Finset.univ \ automorphismAvoidanceSet bad indices action).card ≤
        (indices.biUnion pullback).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ indices, (pullback i).card := Finset.card_biUnion_le
    _ = ∑ _i ∈ indices, bad.card := by
      apply Finset.sum_congr rfl
      intro i _
      exact automorphism_preimage_card bad (action i)
    _ = indices.card * bad.card := by simp

/-- Exact quantitative survivor bound after simultaneous avoidance. -/
theorem automorphismAvoidance_card_lower
    {X I : Type*} [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    (bad : Finset X) (indices : Finset I) (action : I → X ≃ X) :
    Fintype.card X - indices.card * bad.card ≤
      (automorphismAvoidanceSet bad indices action).card := by
  classical
  have hdecomp :
      (Finset.univ \ automorphismAvoidanceSet bad indices action).card +
          (automorphismAvoidanceSet bad indices action).card =
        Fintype.card X := by
    calc
      _ = ((Finset.univ : Finset X) ∪
          automorphismAvoidanceSet bad indices action).card :=
        Finset.card_sdiff_add_card _ _
      _ = Fintype.card X := by
        rw [Finset.union_eq_left.mpr (Finset.subset_univ _), Finset.card_univ]
  have hbad := automorphismAvoidance_bad_card_le bad indices action
  omega

/-- If the automorphism union budget is strictly below the ambient cardinality,
one point avoids the bad set under every selected automorphism. -/
theorem exists_automorphismAvoidance_of_card_lt
    {X I : Type*} [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    (bad : Finset X) (indices : Finset I) (action : I → X ≃ X)
    (hsmall : indices.card * bad.card < Fintype.card X) :
    ∃ x : X, ∀ i ∈ indices, action i x ∉ bad := by
  have hcount := automorphismAvoidance_card_lower bad indices action
  have hpos : 0 < (automorphismAvoidanceSet bad indices action).card := by
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact ⟨x, by simpa [automorphismAvoidanceSet] using hx⟩

/-- Coordinatewise multiplication by a nonzero residue modulo a prime is an
automorphism of the anchored torsion phase group. -/
def primeTorsionScalarEquiv {p d : ℕ} [Fact p.Prime]
    (a : {a : ZMod p // a ≠ 0}) :
    (Fin d → ZMod p) ≃ (Fin d → ZMod p) := by
  exact {
    toFun := fun q i => a.1 * q i
    invFun := fun q i => a.1⁻¹ * q i
    left_inv := by
      intro q
      funext i
      simp [a.2]
    right_inv := by
      intro q
      funext i
      simp [a.2]
  }

/-- A prime field has exactly `p - 1` nonzero scalars. -/
theorem card_nonzero_zmod (p : ℕ) [Fact p.Prime] :
    Fintype.card {a : ZMod p // a ≠ 0} = p - 1 := by
  rw [Fintype.card_subtype_compl (p := fun a : ZMod p => a = 0)]
  simp [ZMod.card]

/-- Anchored prime-torsion phases whose every nonzero scalar multiple avoids
the supplied bad set. -/
def primeTorsionAvoidanceSet (p d : ℕ) [Fact p.Prime]
    (bad : Finset (Fin d → ZMod p)) : Finset (Fin d → ZMod p) :=
  automorphismAvoidanceSet bad Finset.univ
    (fun a : {a : ZMod p // a ≠ 0} => primeTorsionScalarEquiv a)

/-- **Quantitative complete prime-torsion orbit avoidance.** At least
`p^d - (p-1)|bad|` anchored torsion phases have every nonidentity power outside
`bad`. -/
theorem primeTorsionAvoidanceSet_card_lower
    (p d : ℕ) [Fact p.Prime] (bad : Finset (Fin d → ZMod p)) :
    p ^ d - (p - 1) * bad.card ≤
      (primeTorsionAvoidanceSet p d bad).card := by
  simpa [primeTorsionAvoidanceSet, card_nonzero_zmod p, ZMod.card] using
    (automorphismAvoidance_card_lower bad
      (Finset.univ : Finset {a : ZMod p // a ≠ 0})
      (fun a => primeTorsionScalarEquiv (d := d) a))

/-- **Complete prime-torsion polygon theorem.** If the full nonidentity-power
union budget is smaller than the anchored phase group, one phase has every
nonzero scalar multiple outside the bad set. -/
theorem exists_primeTorsion_complete_avoidance
    (p d : ℕ) [Fact p.Prime] (bad : Finset (Fin d → ZMod p))
    (hsmall : (p - 1) * bad.card < p ^ d) :
    ∃ q : Fin d → ZMod p,
      ∀ a : ZMod p, a ≠ 0 → (fun i => a * q i) ∉ bad := by
  have hsmall' :
      (Finset.univ : Finset {a : ZMod p // a ≠ 0}).card * bad.card <
        Fintype.card (Fin d → ZMod p) := by
    simpa [card_nonzero_zmod p, ZMod.card] using hsmall
  obtain ⟨q, hq⟩ := exists_automorphismAvoidance_of_card_lt bad
    (Finset.univ : Finset {a : ZMod p // a ≠ 0})
    (fun a => primeTorsionScalarEquiv (d := d) a) hsmall'
  refine ⟨q, ?_⟩
  intro a ha
  simpa [primeTorsionScalarEquiv] using
    hq ⟨a, ha⟩ (Finset.mem_univ _)

end GaloisForLFunctions.HTGeometry
