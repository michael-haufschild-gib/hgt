import GaloisForLFunctions.RepresentationLifting.Lattices.RootWeightCoordinates
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The cyclic root-to-weight cokernel

Coordinate sum modulo the number of labels identifies the quotient of the
weight lattice by the root lattice with `ℤ/mℤ`. Two copies therefore have
index `m²`, the lattice degree appearing in the Bogomolov–Guan torus cover.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting
variable (ι : Type*) [Fintype ι]

/-- Total coordinate residue of a weight. -/
def rootWeightResidue (p : ι) : coordinateWeightLattice ι p →ₗ[ℤ] ZMod (Fintype.card ι) where
  toFun w := (∑ i, w.val i : ℤ)
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c w := by
    change ((∑ i, c * w.val i : ℤ) : ZMod (Fintype.card ι)) = c • _
    rw [← Finset.mul_sum, Int.cast_mul, zsmul_eq_mul]

/-- Root weights are exactly the weights with zero total residue. -/
theorem rootWeightResidue_ker (p : ι) :
    (rootWeightResidue ι p).ker = LinearMap.range (rootToWeight ι p) := by
  ext w
  rw [mem_range_rootToWeight_iff]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

variable [Nontrivial ι]

/-- A coordinate away from the pivot realizes every residue class. -/
theorem rootWeightResidue_surjective (p : ι) : Function.Surjective (rootWeightResidue ι p) := by
  classical
  intro a
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨j, hj⟩ := exists_ne p
  refine ⟨⟨(Pi.single j z : ι → ℤ), ?_⟩, ?_⟩
  · change (Pi.single j z : ι → ℤ) p = 0
    simp [hj, Ne.symm hj]
  · change ((∑ i : ι, (Pi.single j z : ι → ℤ) i : ℤ) : ZMod (Fintype.card ι)) = z
    simp

/-- The root-to-weight cokernel is cyclic of order the number of labels. -/
def rootWeightCokernelEquiv (p : ι) :
    (coordinateWeightLattice ι p ⧸ LinearMap.range (rootToWeight ι p)) ≃ₗ[ℤ]
      ZMod (Fintype.card ι) :=
  (Submodule.quotEquivOfEq _ _ (rootWeightResidue_ker ι p).symm).trans
    ((rootWeightResidue ι p).quotKerEquivOfSurjective (rootWeightResidue_surjective ι p))

/-- The lattice index is the number of labels. -/
theorem rootWeight_index (p : ι) :
    Nat.card (coordinateWeightLattice ι p ⧸ LinearMap.range (rootToWeight ι p)) =
      Fintype.card ι := by
  letI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  rw [Nat.card_congr (rootWeightCokernelEquiv ι p).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

/-- Tensoring the cyclic lattice defect with a rank-two lattice squares its order. -/
theorem rootWeight_pair_index (p : ι) :
    Nat.card ((coordinateWeightLattice ι p ⧸ LinearMap.range (rootToWeight ι p)) ×
      (coordinateWeightLattice ι p ⧸ LinearMap.range (rootToWeight ι p))) =
      Fintype.card ι ^ 2 := by
  rw [Nat.card_prod, rootWeight_index, pow_two]

#print axioms rootWeightResidue_ker
#print axioms rootWeightCokernelEquiv
#print axioms rootWeight_pair_index
end GaloisForLFunctions.RepresentationLifting
