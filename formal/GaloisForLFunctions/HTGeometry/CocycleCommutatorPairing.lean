import GaloisForLFunctions.HTGeometry.RankTwoRiemannRelations

/-!
# The commutator pairing of a two-cocycle on an abelian group

A factor of automorphy for a line bundle on `W / Gamma` is a two-cocycle on `Gamma`, and the
alternating integral form underlying the generalized Riemann relations is its commutator,

`A (x, y) = c (x, y) - c (y, x)`.

This module proves the purely algebraic content: for any two-cocycle on an abelian group, valued in
any abelian group, the commutator is alternating and biadditive.  Nothing analytic enters -- the
integrality of the Chern form is inherited from the value group alone, and the alternation and
bilinearity from the cocycle identity together with commutativity of the base.

The single computation behind biadditivity is the identity `T = K1 + K2 - K3` between the target and
three instances of the cocycle identity, at `(x, y, z)`, `(z, x, y)` and `(x, z, y)`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A]

/-- The commutator pairing of a two-cocycle. -/
def cocycleCommutator (c : G → G → A) (x y : G) : A := c x y - c y x

/-- The cocycle identity for a two-cocycle on an abelian group. -/
def IsAddTwoCocycle (c : G → G → A) : Prop :=
  ∀ x y z : G, c x y + c (x + y) z = c y z + c x (y + z)

omit [AddCommGroup G] in
theorem cocycleCommutator_self (c : G → G → A) (x : G) : cocycleCommutator c x x = 0 := by
  rw [cocycleCommutator, sub_self]

omit [AddCommGroup G] in
theorem cocycleCommutator_skew (c : G → G → A) (x y : G) :
    cocycleCommutator c y x = -cocycleCommutator c x y := by
  rw [cocycleCommutator, cocycleCommutator, neg_sub]

/-- **The commutator pairing is additive in its first argument.** -/
theorem cocycleCommutator_add_left {c : G → G → A} (hc : IsAddTwoCocycle c) (x y z : G) :
    cocycleCommutator c (x + y) z = cocycleCommutator c x z + cocycleCommutator c y z := by
  have h1 := hc x y z
  have h2 := hc z x y
  have h3 := hc x z y
  rw [add_comm y z] at h1
  rw [add_comm z x] at h2
  have k1 : c x y + c (x + y) z - (c y z + c x (z + y)) = 0 := by rw [sub_eq_zero]; exact h1
  have k2 : c z x + c (x + z) y - (c x y + c z (x + y)) = 0 := by rw [sub_eq_zero]; exact h2
  have k3 : c x z + c (x + z) y - (c z y + c x (z + y)) = 0 := by rw [sub_eq_zero]; exact h3
  have hsplit : cocycleCommutator c (x + y) z
      - (cocycleCommutator c x z + cocycleCommutator c y z)
      = (c x y + c (x + y) z - (c y z + c x (z + y)))
        + (c z x + c (x + z) y - (c x y + c z (x + y)))
        - (c x z + c (x + z) y - (c z y + c x (z + y))) := by
    simp only [cocycleCommutator]
    abel
  rw [← sub_eq_zero, hsplit, k1, k2, k3]
  abel

/-- **The commutator pairing is additive in its second argument.** -/
theorem cocycleCommutator_add_right {c : G → G → A} (hc : IsAddTwoCocycle c) (x y z : G) :
    cocycleCommutator c x (y + z) = cocycleCommutator c x y + cocycleCommutator c x z := by
  have h := cocycleCommutator_add_left hc y z x
  rw [cocycleCommutator_skew c x (y + z), cocycleCommutator_skew c x y,
    cocycleCommutator_skew c x z] at h
  have h' : -cocycleCommutator c x (y + z)
      = -(cocycleCommutator c x y + cocycleCommutator c x z) := by
    rw [h]
    abel
  exact neg_injective h'

theorem cocycleCommutator_zero_left {c : G → G → A} (hc : IsAddTwoCocycle c) (y : G) :
    cocycleCommutator c 0 y = 0 := by
  have h := cocycleCommutator_add_left hc 0 0 y
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem cocycleCommutator_neg_left {c : G → G → A} (hc : IsAddTwoCocycle c) (x y : G) :
    cocycleCommutator c (-x) y = -cocycleCommutator c x y := by
  have h := cocycleCommutator_add_left hc (-x) x y
  rw [neg_add_cancel, cocycleCommutator_zero_left hc] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- **The commutator pairing of a two-cocycle is an alternating biadditive form.**  This is the
algebraic content of the integral alternating form attached to a factor of automorphy: alternation
and biadditivity come from the cocycle identity alone, and integrality is inherited from the value
group. -/
theorem cocycleCommutator_isAlternatingBiadditive {c : G → G → A} (hc : IsAddTwoCocycle c) :
    (∀ x, cocycleCommutator c x x = 0) ∧
    (∀ x y, cocycleCommutator c y x = -cocycleCommutator c x y) ∧
    (∀ x y z, cocycleCommutator c (x + y) z
      = cocycleCommutator c x z + cocycleCommutator c y z) ∧
    (∀ x y z, cocycleCommutator c x (y + z)
      = cocycleCommutator c x y + cocycleCommutator c x z) :=
  ⟨cocycleCommutator_self c, cocycleCommutator_skew c,
    cocycleCommutator_add_left hc, cocycleCommutator_add_right hc⟩

end GaloisForLFunctions.HTGeometry
