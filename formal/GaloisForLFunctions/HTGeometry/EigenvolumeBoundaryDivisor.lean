import GaloisForLFunctions.HTGeometry.EigenvolumeRamificationSystem

/-!
# The boundary divisor of an eigenvolume horizon

The horizon theorem gives the order of the eigenvolume at each place: it is `0` off the horizon
and `-1` on it.  The boundary is therefore reduced, and the ramification coefficient `e - 1`
agrees with the pullback difference of the boundary at every place, not only on the horizon.

That identity is the coefficient form of `R = f^* D - D`, which combined with the pullback formula
for the canonical class gives the invariance of `K + D`.
-/

namespace GaloisForLFunctions.HTGeometry

section Boundary

variable {α : Type*} {F : α → α} {c : α → ℤ} {e : α → ℕ}

/-- The boundary coefficient at a place: the negative of the order of the eigenvolume. -/
def boundaryCoeff (c : α → ℤ) (x : α) : ℤ := -(c x)

variable (hF : Function.Surjective F) (hone : ∀ y, 1 ≤ e y)
variable (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1))
variable (hfin : {y : α | c y ≠ 0}.Finite)
variable (hram : ∀ y : α, c y ≠ 0 → ∀ n : ℕ, 0 < n → F^[n] y = y → ∃ k < n, 1 < e (F^[k] y))

include hF hone hlaw hfin hram in
/-- **The boundary is reduced.**  The order of the eigenvolume takes only the values `0` and
`-1`. -/
theorem order_eq_zero_or_neg_one (x : α) : c x = 0 ∨ c x = -1 := by
  by_cases hx : c x = 0
  · exact Or.inl hx
  · exact Or.inr (eigenvolumeOrder_eq_neg_one_of_someRamified hF hone hlaw hfin hram hx)

include hF hone hlaw hfin hram in
/-- **The boundary coefficient is zero or one.** -/
theorem boundaryCoeff_eq_zero_or_one (x : α) :
    boundaryCoeff c x = 0 ∨ boundaryCoeff c x = 1 := by
  rcases order_eq_zero_or_neg_one hF hone hlaw hfin hram x with h | h
  · exact Or.inl (by simp [boundaryCoeff, h])
  · exact Or.inr (by simp [boundaryCoeff, h])

include hF hone hlaw hfin hram in
/-- **The horizon is totally invariant.** -/
theorem order_ne_zero_iff (x : α) : c x ≠ 0 ↔ c (F x) ≠ 0 := by
  refine ⟨fun hx => ?_, fun hx => order_ne_zero_of_image_ne_zero hlaw hx⟩
  have hval : c x = -1 := eigenvolumeOrder_eq_neg_one_of_someRamified hF hone hlaw hfin hram hx
  have h := hlaw x
  rw [hval] at h
  have hzero : (e x : ℤ) * (c (F x) + 1) = 0 := by linarith
  have hepos : (e x : ℤ) ≠ 0 := by
    have := hone x
    omega
  rcases mul_eq_zero.mp hzero with h' | h'
  · exact absurd h' hepos
  · omega

include hF hone hlaw hfin hram in
/-- **Ramification is the pullback difference of the boundary, at every place.**  This is the
coefficient form of `R = f^* D - D`.  On the horizon both boundary coefficients are one and the
identity reads `e - 1 = e - 1`; off the horizon both are zero and the map is unramified, so it
reads `0 = 0`. -/
theorem ramification_eq_pullback_sub (x : α) :
    (e x : ℤ) - 1 = (e x : ℤ) * boundaryCoeff c (F x) - boundaryCoeff c x := by
  by_cases hx : c x = 0
  · have hFx : c (F x) = 0 := by
      by_contra hcon
      exact (order_ne_zero_of_image_ne_zero hlaw hcon) hx
    have he : e x = 1 := ramificationIndex_eq_one_of_order_eq_zero hlaw hx
    simp [boundaryCoeff, hx, hFx, he]
  · have hval : c x = -1 := eigenvolumeOrder_eq_neg_one_of_someRamified hF hone hlaw hfin hram hx
    have hFne : c (F x) ≠ 0 := (order_ne_zero_iff hF hone hlaw hfin hram x).mp hx
    have hFval : c (F x) = -1 :=
      eigenvolumeOrder_eq_neg_one_of_someRamified hF hone hlaw hfin hram hFne
    rw [boundaryCoeff, boundaryCoeff, hval, hFval]
    ring

end Boundary

end GaloisForLFunctions.HTGeometry
