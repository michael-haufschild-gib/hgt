import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupMovesFinitelyManyZerosInDistinctPairsAtWill

/-!
# The only intermediate cover of the zeros is the cover of the squared zeros

A cover between the cover of the zeros and the forward times is an equivalence relation on a
fibre that every forward monodromy preserves: its classes are the points of the intermediate
cover.

**Theorem** (`forwardMonodromy_invariant_equivalence`). Let `b` be a forward time off the branch
times. An equivalence relation on the zeros of `H_b` that is preserved by `G₊(b)` is equality,
or the relation `z' = ±z`, or the relation that identifies all zeros.

So the action of `G₊(b)` on the pairs `{z, −z}` is primitive, and the squared zeros are the only
invariant between a zero and the time: the Galois correspondence of the cover has one
intermediate term.

Proof (`IsWindowedSignedGroup.invariant_equivalence`). Let the relation hold for `x` and a point
`y` of another pair. A signed 3-cycle `y → u → s` through a fresh pair, or the double flip of the
pair of `y` with a fresh pair, fixes `x` and carries `y` to any `u` off the pair of `x`; the same
from `y` reaches the pair of `x`. If the relation holds only inside pairs and for one pair, it
holds for every pair by transitivity.
-/

open Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

namespace IsWindowedSignedGroup

variable {Ω : Type*} {P : PairCoordinate Ω} {G : Subgroup (Perm Ω)}
  (hG : IsWindowedSignedGroup P G) {R : Ω → Ω → Prop}
include hG

/-- An invariant relation that holds for `x` and a point of another pair holds for `x` and every
point off the pair of `x`. -/
theorem rel_of_rel_of_pair_ne (hinv : ∀ g ∈ G, ∀ x y, R x y → R (g x) (g y)) {x y : Ω}
    (hxy : R x y) (hne : P.pair x ≠ P.pair y) {u : Ω} (hu : P.pair u ≠ P.pair x) : R x u := by
  obtain ⟨s, hs⟩ := hG.exists_pair_not_mem ({P.pair x, P.pair y, P.pair u} : Finset ℤ)
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or] at hs
  obtain ⟨hsx, hsy, hsu⟩ := hs
  by_cases huy : P.pair u = P.pair y
  · rcases (P.pair_eq_iff y u).mp huy.symm with h | h
    · rw [h]
      exact hxy
    · -- the double flip of the pairs of `y` and `s` fixes `x`
      obtain ⟨T, hT, hTy, -, hTo⟩ := hG.hasDoubleFlip (p := y) (q := s) (Ne.symm hsy)
      have key := hinv T hT x y hxy
      rwa [hTo x hne (Ne.symm hsx), hTy, ← h] at key
  · -- the signed 3-cycle `y → u → s` fixes `x`
    obtain ⟨T, hT, hTy, -, -, hTo⟩ := hG.hasSignedCycle (p := y) (q := u) (r := s)
      (Ne.symm huy) (Ne.symm hsu) (Ne.symm hsy)
    have key := hinv T hT x y hxy
    rwa [hTo x hne (Ne.symm hu) (Ne.symm hsx), hTy] at key

/-- **The invariant equivalence relations.** An equivalence relation preserved by `G` is
equality, the relation of lying in one pair, or the relation that identifies all points. -/
theorem invariant_equivalence (hR : Equivalence R)
    (hinv : ∀ g ∈ G, ∀ x y, R x y → R (g x) (g y)) :
    (∀ x y, R x y ↔ x = y) ∨ (∀ x y, R x y ↔ P.pair x = P.pair y) ∨ ∀ x y, R x y := by
  by_cases hbig : ∃ x y, R x y ∧ P.pair x ≠ P.pair y
  · obtain ⟨x, y, hxy, hne⟩ := hbig
    -- `x` is related to every point
    have hx : ∀ v, R x v := by
      intro v
      by_cases hv : P.pair v = P.pair x
      · exact hR.trans hxy (hG.rel_of_rel_of_pair_ne hinv (hR.symm hxy) (Ne.symm hne)
          (by rw [hv]; exact hne))
      · exact hG.rel_of_rel_of_pair_ne hinv hxy hne hv
    exact Or.inr (Or.inr fun a b => hR.trans (hR.symm (hx a)) (hx b))
  have hsmall : ∀ x y, R x y → P.pair x = P.pair y := fun x y h => by
    by_contra hne
    exact hbig ⟨x, y, h, hne⟩
  by_cases hflip : ∃ x, R x (P.flip x) ∧ P.flip x ≠ x
  · obtain ⟨x₀, hx₀, -⟩ := hflip
    -- transitivity carries the related pair to every pair
    have hall : ∀ z, R z (P.flip z) := fun z => by
      obtain ⟨g, hg, hgz, -⟩ := hG.exists_apply_eq_of_fixed (∅ : Finset ℤ) (x := x₀) (y := z)
        (by simp) (by simp)
      have key := hinv g hg _ _ hx₀
      rwa [hG.comm g hg, hgz] at key
    refine Or.inr (Or.inl fun x y => ⟨hsmall x y, fun h => ?_⟩)
    rcases (P.pair_eq_iff x y).mp h with h' | h'
    · rw [h']
      exact hR.refl x
    · rw [h']
      exact hall x
  · refine Or.inl fun x y => ⟨fun h => ?_, fun h => by rw [h]; exact hR.refl y⟩
    rcases (P.pair_eq_iff x y).mp (hsmall x y h) with h' | h'
    · exact h'.symm
    · by_contra hxy
      refine hflip ⟨x, by rw [← h']; exact h, fun e => hxy ?_⟩
      rw [h', e]

end IsWindowedSignedGroup

open RHTower in
/-- **The intermediate covers.** An equivalence relation on the zeros of `H_b` that every forward
monodromy preserves is equality, the relation `z' = ±z`, or the relation that identifies all
zeros. -/
theorem forwardMonodromy_invariant_equivalence {b : ℂ} (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)
    {R : {z : ℂ // complexHeat b z = 0} → {z : ℂ // complexHeat b z = 0} → Prop}
    (hR : Equivalence R)
    (hinv : ∀ g ∈ forwardMonodromy b hb₀ hb, ∀ x y, R x y → R (g x) (g y)) :
    (∀ x y, R x y ↔ x = y) ∨ (∀ x y, R x y ↔ (y = x ∨ y = fibreNeg b x)) ∨ ∀ x y, R x y := by
  obtain ⟨P, hP, hG⟩ := exists_pairCoordinate_isWindowedSignedGroup hb₀ hb
  rcases hG.invariant_equivalence hR hinv with h | h | h
  · exact Or.inl h
  · refine Or.inr (Or.inl fun x y => (h x y).trans ?_)
    rw [P.pair_eq_iff, hP]
  · exact Or.inr (Or.inr h)

end GaloisForLFunctions.GaloisTheoryOfZeros
