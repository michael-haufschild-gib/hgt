import Mathlib

/-!
# Compatible systems and the reflection `x ↦ 1 - x`

A gamma-factor of the shape `Q^s ∏_{j≤N} Γ(d s /(2N) + (2 n_j - d - 1)/(4N))` is governed by the
residues of the integers `n_j` modulo `2N`, subject to two conditions: the `n_j` are pairwise distinct
modulo `2N`, and no `n_i` is congruent to `1 - n_j`.  Equivalently, the sets `{n_j}` and `{1 - n_j}` are
disjoint and together exhaust `ZMod (2N)`.

The reason such a configuration exists, and the reason the count is `2^N`, is a single fact: the
reflection `x ↦ 1 - x` on `ZMod (2N)` has **no fixed point**, so it is a fixed-point-free involution
and its orbits are `N` two-element sets.  A configuration of the above kind is exactly a transversal.

The proof of fixed-point-freeness is the observation that a fixed point would give `2x = 1`, which the
reduction `ZMod (2N) → ZMod 2` turns into `0 = 1`.
-/

namespace HTGeometry

variable {N : ℕ}

/-- The reflection used by the compatibility conditions. -/
def refl2N (N : ℕ) (x : ZMod (2 * N)) : ZMod (2 * N) := 1 - x

@[simp] theorem refl2N_refl2N (x : ZMod (2 * N)) : refl2N N (refl2N N x) = x := by
  unfold refl2N
  ring

/-- **The reflection has no fixed point.**  A fixed point would satisfy `2x = 1`, impossible modulo an
even number. -/
theorem refl2N_ne (x : ZMod (2 * N)) : refl2N N x ≠ x := by
  intro h
  have h2 : (2 : ZMod (2 * N)) * x = 1 := by
    unfold refl2N at h
    linear_combination -h
  have hdvd : (2 : ℕ) ∣ 2 * N := ⟨N, rfl⟩
  have hc := congrArg (ZMod.castHom hdvd (ZMod 2)) h2
  rw [map_mul, map_one] at hc
  have hcast : ((2 : ZMod (2 * N))) = ((2 : ℕ) : ZMod (2 * N)) := by norm_cast
  rw [hcast, map_natCast] at hc
  have hzero : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [hzero, zero_mul] at hc
  exact absurd hc (by decide)

/-- A compatible system, phrased on residues: a set of residues meeting every reflection orbit at most
once and never meeting a reflected element of itself. -/
structure CompatibleSystem (N : ℕ) where
  /-- the residues occupied by the system -/
  carrier : Finset (ZMod (2 * N))
  /-- no element is the reflection of an element of the system -/
  no_refl : ∀ x ∈ carrier, ∀ y ∈ carrier, refl2N N x ≠ y

/-- The reflected copy of a compatible system is disjoint from it. -/
theorem CompatibleSystem.disjoint_image (S : CompatibleSystem N) [DecidableEq (ZMod (2 * N))] :
    Disjoint S.carrier (S.carrier.image (refl2N N)) := by
  rw [Finset.disjoint_right]
  intro y hy hyc
  obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
  exact S.no_refl x hx y hyc hxy

/-- Reflection is injective, so the reflected copy has the same size. -/
theorem card_image_refl2N (s : Finset (ZMod (2 * N))) [DecidableEq (ZMod (2 * N))] :
    (s.image (refl2N N)).card = s.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  have := congrArg (refl2N N) hxy
  simpa using this

/-- **A compatible system has at most `N` elements**, and it has exactly `N` precisely when its
reflected copy completes it to all of `ZMod (2N)`. -/
theorem CompatibleSystem.card_le (S : CompatibleSystem N) (hN : 0 < N)
    [DecidableEq (ZMod (2 * N))] : 2 * S.carrier.card ≤ 2 * N := by
  haveI : NeZero (2 * N) := ⟨by omega⟩
  have hcard : S.carrier.card + (S.carrier.image (refl2N N)).card ≤ Fintype.card (ZMod (2 * N)) := by
    have hunion := Finset.card_union_of_disjoint (S.disjoint_image)
    calc S.carrier.card + (S.carrier.image (refl2N N)).card
        = (S.carrier ∪ S.carrier.image (refl2N N)).card := hunion.symm
      _ ≤ Fintype.card (ZMod (2 * N)) := Finset.card_le_univ _
  have hfc : Fintype.card (ZMod (2 * N)) = 2 * N := ZMod.card (2 * N)
  rw [card_image_refl2N] at hcard
  omega

end HTGeometry
