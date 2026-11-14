import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupContainsTheEvenSignedPermutationsOfTheZeros

/-!
# The forward monodromy group moves finitely many zeros in distinct pairs at will

Let `p i` and `q i`, `i` in a finite set, be zeros of `H_b` at a forward time `b` off the branch
times, such that no two `p i` are equal or opposite and no two `q i` are equal or opposite. Then
one element of `G₊(b)` carries every `p i` to `q i`
(`exists_mem_forwardMonodromy_forall_apply_eq`).

So `G₊(b)` is `n`-fold transitive on the pairs `{z, -z}` for every `n`, with every choice of the
signs: on every finite union of pairs it induces all signed permutations. The cover of the zeros
over the forward half-plane is in the position of a generic curve over a finite field at every
finite level, and the only invariants left for `G₊` are the two signs of `W/W⁰`.

Proof. A group that contains every signed 3-cycle and every double flip
(`IsWindowedSignedGroup`) moves one point to another by a signed 3-cycle through a fresh pair, or
by a double flip with a fresh pair, and both fix the points of finitely many other pairs
(`IsWindowedSignedGroup.exists_apply_eq_of_fixed`). Induction on the number of points.
-/

open Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

namespace IsWindowedSignedGroup

variable {Ω : Type*} {P : PairCoordinate Ω} {G : Subgroup (Perm Ω)}
  (hG : IsWindowedSignedGroup P G)
include hG

/-- A point whose pair has a number outside a finite set. -/
theorem exists_pair_not_mem (A : Finset ℤ) : ∃ s, P.pair s ∉ A := by
  obtain ⟨m, hm⟩ := Infinite.exists_notMem_finset A
  obtain ⟨s, hs⟩ := hG.surjective m
  exact ⟨s, by rw [hs]; exact hm⟩

/-- **One point is moved to another while finitely many other pairs stay fixed.** -/
theorem exists_apply_eq_of_fixed (A : Finset ℤ) {x y : Ω} (hx : P.pair x ∉ A)
    (hy : P.pair y ∉ A) : ∃ h ∈ G, h x = y ∧ ∀ z, P.pair z ∈ A → h z = z := by
  -- a fresh pair
  obtain ⟨s, hs⟩ := hG.exists_pair_not_mem (insert (P.pair x) (insert (P.pair y) A))
  rw [Finset.mem_insert, Finset.mem_insert, not_or, not_or] at hs
  obtain ⟨hsx, hsy, hsA⟩ := hs
  by_cases hxy : P.pair x = P.pair y
  · rcases (P.pair_eq_iff x y).mp hxy with h | h
    · exact ⟨1, G.one_mem, h.symm, fun _ _ => rfl⟩
    · -- `y` is the partner of `x`: the double flip of the pair of `x` and the fresh pair
      obtain ⟨T, hT, h1, -, h3⟩ := hG.hasDoubleFlip (p := x) (q := s) (Ne.symm hsx)
      exact ⟨T, hT, h1.trans h.symm, fun z hz =>
        h3 z (fun e => hx (e ▸ hz)) (fun e => hsA (e ▸ hz))⟩
  · -- the signed 3-cycle of `x`, `y` and a point of the fresh pair
    obtain ⟨T, hT, h1, -, -, h4⟩ :=
      hG.hasSignedCycle (p := x) (q := y) (r := s) hxy (Ne.symm hsy) (Ne.symm hsx)
    exact ⟨T, hT, h1, fun z hz =>
      h4 z (fun e => hx (e ▸ hz)) (fun e => hy (e ▸ hz)) (fun e => hsA (e ▸ hz))⟩

/-- **Multiple transitivity.** Finitely many points `p i` in distinct pairs are moved to points
`q i` in distinct pairs by one element of `G`. -/
theorem exists_forall_apply_eq {ι : Type*} [Finite ι] {p q : ι → Ω}
    (hp : Function.Injective fun i => P.pair (p i))
    (hq : Function.Injective fun i => P.pair (q i)) : ∃ g ∈ G, ∀ i, g (p i) = q i := by
  classical
  cases nonempty_fintype ι
  suffices h : ∀ s : Finset ι, ∃ g ∈ G, ∀ i ∈ s, g (p i) = q i by
    obtain ⟨g, hg, h⟩ := h Finset.univ
    exact ⟨g, hg, fun i => h i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1, G.one_mem, fun i hi => by simp at hi⟩
  | insert a s ha ih =>
    obtain ⟨g₀, hg₀, h₀⟩ := ih
    -- the image of the new point and its target lie off the pairs already placed
    have hx : P.pair (g₀ (p a)) ∉ s.image fun i => P.pair (q i) := by
      rw [Finset.mem_image]
      rintro ⟨i, hi, e⟩
      have e' : P.pair (q i) = P.pair (g₀ (p a)) := e
      rw [← h₀ i hi, hG.pair_apply_eq_iff hg₀] at e'
      exact ha (hp e' ▸ hi)
    have hy : P.pair (q a) ∉ s.image fun i => P.pair (q i) := by
      rw [Finset.mem_image]
      rintro ⟨i, hi, e⟩
      exact ha (hq e ▸ hi)
    obtain ⟨h, hh, h1, h2⟩ := hG.exists_apply_eq_of_fixed _ hx hy
    refine ⟨h * g₀, G.mul_mem hh hg₀, fun i hi => ?_⟩
    show h (g₀ (p i)) = q i
    rcases Finset.mem_insert.mp hi with hia | hi'
    · rw [hia]
      exact h1
    · rw [h₀ i hi']
      exact h2 _ (Finset.mem_image_of_mem _ hi')

end IsWindowedSignedGroup

open RHTower in
/-- **`G₊` moves finitely many zeros in distinct pairs at will.** If no two of the zeros `p i`
of `H_b` are equal or opposite, and no two of the zeros `q i`, one element of `G₊(b)` carries
every `p i` to `q i`. -/
theorem exists_mem_forwardMonodromy_forall_apply_eq {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) {ι : Type*} [Finite ι] {p q : ι → {z : ℂ // complexHeat b z = 0}}
    (hp : ∀ i j, i ≠ j → p j ≠ p i ∧ p j ≠ fibreNeg b (p i))
    (hq : ∀ i j, i ≠ j → q j ≠ q i ∧ q j ≠ fibreNeg b (q i)) :
    ∃ g ∈ forwardMonodromy b hb₀ hb, ∀ i, g (p i) = q i := by
  obtain ⟨P, hP, hG⟩ := exists_pairCoordinate_isWindowedSignedGroup hb₀ hb
  have hinj : ∀ {u : ι → {z : ℂ // complexHeat b z = 0}},
      (∀ i j, i ≠ j → u j ≠ u i ∧ u j ≠ fibreNeg b (u i)) →
      Function.Injective fun i => P.pair (u i) := by
    intro u hu i j h
    by_contra hij
    rcases (P.pair_eq_iff (u i) (u j)).mp h with h' | h'
    · exact (hu i j hij).1 h'
    · exact (hu i j hij).2 (h'.trans (hP _))
  exact hG.exists_forall_apply_eq (hinj hp) (hinj hq)

end GaloisForLFunctions.GaloisTheoryOfZeros
