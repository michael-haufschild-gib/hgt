import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PhysicalRotation

/-! # Only the squared couplings near a cut enter a local dilation error -/

open Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
variable {n : ℕ}

/-- The cut words and their incident interaction neighbours. -/
def seamNeighbourhood (C : Finset (PathLabel n)) : Finset (PathLabel n) :=
  C.biUnion fun q => insert q (pathOverlaps q)

theorem seamNeighbourhood_card (C : Finset (PathLabel n)) : (seamNeighbourhood C).card≤43*C.card := by
  classical
  apply (card_biUnion_le (s:=C) (t:=fun q => insert q (pathOverlaps q))).trans
  have h (q : PathLabel n) : (insert q (pathOverlaps q)).card≤43 :=
    (card_insert_le ..).trans (Nat.succ_le_succ (pathOverlaps_card_le q))
  calc _ ≤ ∑ _q ∈ C, 43 := sum_le_sum fun q _ => h q
       _ = 43*C.card := by simp [Nat.mul_comm]

/-- Restricting the shell to a common seam neighbourhood leaves every
overlapping pair across the selected boundary untouched. -/
theorem boundaryMass_le_seam (S C : Finset (PathLabel n)) (u : PathShell n)
    (hcut : ∀ q∉S, ∀ l∈S, l∈pathOverlaps q → q∈C) :
    boundaryMass u S≤84*‖restrictShell (seamNeighbourhood C) u‖^2 := by
  classical
  let v := restrictShell (seamNeighbourhood C) u
  let w (q l : PathLabel n) := (v q)^2+(v l)^2
  have hw (q l : PathLabel n) : 0≤w q l := add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    _ ≤ ∑ q ∈ Sᶜ, ∑ l ∈ S∩pathOverlaps q, w q l := by
      apply sum_le_sum
      intro q hq
      apply sum_le_sum
      intro l hl
      obtain ⟨hs,ho⟩ := mem_inter.mp hl
      have hc := hcut q (mem_compl.mp hq) l hs ho
      have hq' : q∈seamNeighbourhood C := mem_biUnion.mpr ⟨q,hc,mem_insert_self ..⟩
      have hl' : l∈seamNeighbourhood C := mem_biUnion.mpr ⟨q,hc,mem_insert_of_mem ho⟩
      change 2*|u q| * |u l| ≤ (v q)^2+(v l)^2
      rw [show v q=u q from if_pos hq',show v l=u l from if_pos hl']
      nlinarith only [sq_nonneg (|u q|-|u l|),sq_abs (u q),sq_abs (u l)]
    _ ≤ ∑ q ∈ Sᶜ, ∑ l ∈ pathOverlaps q, w q l := sum_le_sum fun q _ =>
      sum_le_sum_of_subset_of_nonneg inter_subset_right (fun l _ _ => hw q l)
    _ ≤ ∑ q, ∑ l ∈ pathOverlaps q, w q l :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun q _ _ => sum_nonneg fun l _ => hw q l)
    _ ≤ _ := path_sum_overlap_squares_le v

#print axioms seamNeighbourhood_card
#print axioms boundaryMass_le_seam
end
end GaloisForLFunctions.HTGeometry.BlockDilations
