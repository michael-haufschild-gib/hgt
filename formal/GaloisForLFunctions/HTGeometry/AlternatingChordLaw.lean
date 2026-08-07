import Mathlib

/-!
# The alternating chord law of a resolvent pair

Two shifted resolvent states of the same source differ from `A v` by multiples of `v`:
`u_beta = A v - alpha • v` and `u_alpha = A v - beta • v` for `v` the product-resolvent state.
Their image under any `2`-alternating map is therefore the *fixed* pair `(v, A v)` rescaled by the
shift gap.  This file proves that law for an arbitrary `2`-alternating map into an arbitrary
module, so it applies both to a pair of boundary functionals (the projective minor) and to the
exterior square itself (the Plücker blade), and both before and after homogenization.
-/

open scoped ExteriorAlgebra

namespace GaloisForLFunctions.HTGeometry

variable {R V N : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup N] [Module R N]

/-- Value of a `2`-alternating map on an ordered pair. -/
def altPair (ω : V [⋀^Fin 2]→ₗ[R] N) (x y : V) : N := ω ![x, y]

private theorem update_zero_pair {W : Type*} (x y z : W) :
    Function.update ![x, y] 0 z = ![z, y] := by
  funext i; fin_cases i <;> simp

private theorem update_one_pair {W : Type*} (x y z : W) :
    Function.update ![x, y] 1 z = ![x, z] := by
  funext i; fin_cases i <;> simp

theorem altPair_add_left (ω : V [⋀^Fin 2]→ₗ[R] N) (x x' y : V) :
    altPair ω (x + x') y = altPair ω x y + altPair ω x' y := by
  have h := ω.toMultilinearMap.map_update_add ![x, y] 0 x x'
  rw [update_zero_pair, update_zero_pair, update_zero_pair] at h
  exact h

theorem altPair_add_right (ω : V [⋀^Fin 2]→ₗ[R] N) (x y y' : V) :
    altPair ω x (y + y') = altPair ω x y + altPair ω x y' := by
  have h := ω.toMultilinearMap.map_update_add ![x, y] 1 y y'
  rw [update_one_pair, update_one_pair, update_one_pair] at h
  exact h

theorem altPair_smul_left (ω : V [⋀^Fin 2]→ₗ[R] N) (r : R) (x y : V) :
    altPair ω (r • x) y = r • altPair ω x y := by
  have h := ω.toMultilinearMap.map_update_smul ![x, y] 0 r x
  rw [update_zero_pair, update_zero_pair] at h
  exact h

theorem altPair_smul_right (ω : V [⋀^Fin 2]→ₗ[R] N) (r : R) (x y : V) :
    altPair ω x (r • y) = r • altPair ω x y := by
  have h := ω.toMultilinearMap.map_update_smul ![x, y] 1 r y
  rw [update_one_pair, update_one_pair] at h
  exact h

theorem altPair_self (ω : V [⋀^Fin 2]→ₗ[R] N) (x : V) : altPair ω x x = 0 := by
  apply ω.map_eq_zero_of_eq _ (i := 0) (j := 1) <;> simp

theorem altPair_swap (ω : V [⋀^Fin 2]→ₗ[R] N) (x y : V) :
    altPair ω y x = -altPair ω x y := by
  have h := altPair_add_right ω (x + y) x y
  have h0 : altPair ω (x + y) (x + y) = 0 := altPair_self ω _
  rw [h0] at h
  rw [altPair_add_left ω x y x, altPair_add_left ω x y y, altPair_self ω x,
    altPair_self ω y] at h
  have hz : altPair ω y x + altPair ω x y = 0 := by
    simp only [zero_add, add_zero] at h
    exact h.symm
  exact eq_neg_of_add_eq_zero_left hz

theorem altPair_sub_left (ω : V [⋀^Fin 2]→ₗ[R] N) (x x' y : V) :
    altPair ω (x - x') y = altPair ω x y - altPair ω x' y := by
  have h : altPair ω ((x - x') + x') y = altPair ω (x - x') y + altPair ω x' y :=
    altPair_add_left ω _ _ _
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

theorem altPair_sub_right (ω : V [⋀^Fin 2]→ₗ[R] N) (x y y' : V) :
    altPair ω x (y - y') = altPair ω x y - altPair ω x y' := by
  have h : altPair ω x ((y - y') + y') = altPair ω x (y - y') + altPair ω x y' :=
    altPair_add_right ω _ _ _
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-- **Alternating chord law.**  The two shifted states `w - alpha • v` and `w - beta • v` of a
common pair `(v, w)` span, under every `2`-alternating map, the fixed value of `(v, w)` rescaled by
the shift gap.  No positivity, spectral theory, or finite dimension is used. -/
theorem altPair_chord (ω : V [⋀^Fin 2]→ₗ[R] N) (α β : R) (v w : V) :
    altPair ω (w - α • v) (w - β • v) = (β - α) • altPair ω v w := by
  rw [altPair_sub_left, altPair_sub_right, altPair_sub_right,
    altPair_self, altPair_smul_right, altPair_smul_left, altPair_smul_left,
    altPair_smul_right, altPair_self, altPair_swap ω v w]
  rw [smul_zero, smul_zero, smul_neg, sub_zero, sub_smul]
  abel

/-- The chord law in the exterior square: the two shifted resolvent states span the fixed
decomposable blade `v ∧ w`, rescaled by the shift gap. -/
theorem exteriorPair_chord (α β : R) (v w : V) :
    exteriorPower.ιMulti R 2 ![w - α • v, w - β • v] =
      (β - α) • exteriorPower.ιMulti R 2 ![v, w] :=
  altPair_chord (exteriorPower.ιMulti R 2) α β v w

end GaloisForLFunctions.HTGeometry
