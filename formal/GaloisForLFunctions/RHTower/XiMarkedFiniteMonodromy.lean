import GaloisForLFunctions.RHTower.XiMarkedConjugatePackets
import GaloisForLFunctions.RHTower.XiMarkedMeridian

open GaloisForLFunctions.HTGeometry

namespace RHTower.XiMarkedMonodromy

noncomputable section

/-- Marked tuples with the same zero-winding integer in every coordinate. -/
def diagonalWindingSubgroup (A : Finset ℝ) : Subgroup (JointGroup A) where
  carrier := {q | ∃ k : Multiplicative ℤ, ∀ a : A, zeroWinding (q a) = k}
  one_mem' := ⟨1, fun _ => zeroWinding.map_one⟩
  mul_mem' := by
    rintro x y ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k * l, fun a => by change zeroWinding (x a * y a) = _; rw [map_mul, hk, hl]⟩
  inv_mem' := by
    rintro x ⟨k, hk⟩
    exact ⟨k⁻¹, fun a => by change zeroWinding (x a)⁻¹ = _; rw [map_inv, hk]⟩

theorem jointMap_range_le_diagonal (A : Finset ℝ) :
    (jointMap A).range ≤ diagonalWindingSubgroup A := by
  rintro _ ⟨p, rfl⟩
  exact jointMap_zero_winding_diagonal A p

/-- Every finite group sees exactly the diagonal-winding subgroup of actual marked Xi monodromy. -/
theorem finite_image_jointMap_eq_diagonal (A : Finset ℝ)
    {G : Type*} [Group G] [Finite G] (f : JointGroup A →* G) :
    ((jointMap A).range).map f = (diagonalWindingSubgroup A).map f := by
  apply le_antisymm
  · exact Subgroup.map_mono (jointMap_range_le_diagonal A)
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hq
    obtain ⟨p, hp⟩ := xi_winding_surjective A k
    let u := jointMap A p
    have hu (a : A) : zeroWinding (u a) = k := (zeroWinding_jointMap A p a).trans hp
    have hker : ∀ a : A, zeroWinding ((q * u⁻¹) a) = 1 := by
      intro a
      change zeroWinding (q a * (u a)⁻¹) = 1
      rw [map_mul, map_inv, hk, hu, mul_inv_cancel]
    have hn := finite_image_contains_product_kernel A f (q * u⁻¹) hker
    have hm : f u ∈ ((jointMap A).range).map f := ⟨u, ⟨p, rfl⟩, rfl⟩
    have hprod := (((jointMap A).range).map f).mul_mem hn hm
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one] using hprod

end

end RHTower.XiMarkedMonodromy
