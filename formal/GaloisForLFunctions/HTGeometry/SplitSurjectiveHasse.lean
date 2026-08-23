import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Hasse coordinates for split surjective homomorphisms -/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- A split surjection of commutative groups decomposes its source into target and kernel
coordinates. -/
def splitSurjectiveCommGroupHomEquivProdKer
    {G : Type u} {H : Type v} [CommGroup G] [CommGroup H]
    (f : G →* H) (s : H →* G) (hs : Function.RightInverse s f) :
    G ≃* H × f.ker where
  toFun x := ⟨f x, ⟨x * (s (f x))⁻¹, by
    change f (x * (s (f x))⁻¹) = 1
    rw [map_mul, map_inv, hs (f x), mul_inv_cancel]⟩⟩
  invFun p := p.2.1 * s p.1
  left_inv x := by simp
  right_inv p := by
    rcases p with ⟨h, k⟩
    apply Prod.ext
    · change f (k.1 * s h) = h
      rw [map_mul, k.property, hs h, one_mul]
    · apply Subtype.ext
      change (k.1 * s h) * (s (f (k.1 * s h)))⁻¹ = k.1
      rw [map_mul, k.property, one_mul, hs h]
      simp
  map_mul' x y := by
    apply Prod.ext
    · exact map_mul f x y
    · apply Subtype.ext
      change (x * y) * (s (f (x * y)))⁻¹ =
        (x * (s (f x))⁻¹) * (y * (s (f y))⁻¹)
      rw [map_mul, map_mul, mul_inv_rev]
      ac_rfl

/-- Target and residual-kernel coordinates jointly detect equality in the source. -/
theorem splitSurjectiveCommGroupHom_congr_hasse_iff
    {G : Type u} {H : Type v} [CommGroup G] [CommGroup H]
    (f : G →* H) (s : H →* G) (x y : G) :
    f x = f y ∧ x * (s (f x))⁻¹ = y * (s (f y))⁻¹ ↔ x = y := by
  constructor
  · rintro ⟨hf, hk⟩
    calc
      x = (x * (s (f x))⁻¹) * s (f x) := by simp
      _ = (y * (s (f y))⁻¹) * s (f y) := by rw [hk, hf]
      _ = y := by simp
  · rintro rfl
    exact ⟨rfl, rfl⟩

end GaloisForLFunctions.HTGeometry
