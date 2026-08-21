import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.SubgroupFinset

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

universe u

/-- Kneser's inequality for all pairs `(A, B)` with `#(A * B) + #A ≤ n`. -/
def KneserAt (n : ℕ) : Prop :=
  ∀ {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (A B : Finset G),
    A.Nonempty → B.Nonempty → (A * B).card + A.card ≤ n →
    (A * mulStab (A * B)).card + (B * mulStab (A * B)).card
      ≤ (A * B).card + (mulStab (A * B)).card

variable {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]

/-- A set stabilised by `mulStab` is the full preimage of its image in the quotient. -/
theorem mem_iff_mk_mem_image (s : Finset G) [DecidableEq (G ⧸ stabSubgroup s)] (x : G) :
    x ∈ s ↔ (QuotientGroup.mk x : G ⧸ stabSubgroup s)
      ∈ s.image (fun g : G => (QuotientGroup.mk g : G ⧸ stabSubgroup s)) := by
  constructor
  · intro hx; exact mem_image_of_mem _ hx
  · intro hx
    rw [mem_image] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hmem : y⁻¹ * x ∈ stabSubgroup s := by
      rw [← QuotientGroup.eq (s := stabSubgroup s)]
      exact hxy.symm
    have : y * (y⁻¹ * x) ∈ s * mulStab s :=
      mul_mem_mul hy (by rw [mem_mulStab]; exact hmem)
    rw [mul_mulStab, mul_inv_cancel_left] at this
    exact this

end GaloisForLFunctions.HTGeometry.AddComb
