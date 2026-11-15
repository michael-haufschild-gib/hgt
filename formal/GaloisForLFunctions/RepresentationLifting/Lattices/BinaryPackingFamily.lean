import GaloisForLFunctions.RepresentationLifting.Lattices.AbelianPackingDensity
import Mathlib.Data.ZMod.Basic

/-!
# A noncyclic family of augmentation-square packings

Elementary abelian two-groups of rank at least two provide noncyclic labels.
The resulting Euclidean lattices have dimension `2^(n+2)-1`, squared covolume
`2^(3*(n+2))`, exact packing radius one, and a genuine covered-volume density.
-/

open MeasureTheory Metric Module Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry HTGeometry.LatticePackingDensity

/-- Elementary abelian two-groups of rank at least two. -/
abbrev BinaryPackingGroup (n : ℕ) := Multiplicative (Fin (n+2) → ZMod 2)

abbrev BinaryPackingLattice (n : ℕ) := abelianAugmentationRealLattice (BinaryPackingGroup n)

theorem binaryPackingGroup_card (n : ℕ) : Fintype.card (BinaryPackingGroup n) = 2^(n+2) := by
  simp [BinaryPackingGroup]

theorem binaryPackingGroup_card_ge_four (n : ℕ) : 4 ≤ Fintype.card (BinaryPackingGroup n) := by
  rw [binaryPackingGroup_card, pow_add]
  have hn : 0 < (2:ℕ)^n := by positivity
  norm_num only [pow_two] at *
  omega

theorem binaryPackingGroup_square (n : ℕ) (g : BinaryPackingGroup n) : g^2 = 1 := by
  change Multiplicative.ofAdd (2 • Multiplicative.toAdd g) = Multiplicative.ofAdd 0
  congr 1
  ext i
  change (2:ℕ) • (Multiplicative.toAdd g i) = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- These label groups are never cyclic. -/
theorem binaryPackingGroup_not_cyclic (n : ℕ) : ¬ IsCyclic (BinaryPackingGroup n) := by
  intro h
  obtain ⟨g, hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard).mp h
  have hd := orderOf_dvd_of_pow_eq_one (binaryPackingGroup_square n g)
  rw [hg, Nat.card_eq_fintype_card] at hd
  have he := Nat.le_of_dvd (by norm_num : 0 < (2:ℕ)) hd
  have hn := binaryPackingGroup_card_ge_four n
  omega

theorem binaryPacking_rank (n : ℕ) :
    finrank ℝ (AbelianRealHyperplane (BinaryPackingGroup n)) = 2^(n+2)-1 := by
  have h := abelianRealHyperplane_rank (BinaryPackingGroup n)
  rw [binaryPackingGroup_card] at h
  omega

theorem binaryPacking_covolume_sq (n : ℕ) :
    ZLattice.covolume (BinaryPackingLattice n)^2 = (2^(n+2) : ℝ)^3 := by
  rw [BinaryPackingLattice, abelianAugmentationRealLattice_covolume_sq, binaryPackingGroup_card]
  norm_cast

/-- The noncyclic family has the same sharp radius as the cyclic construction. -/
theorem binaryPacking_balls_disjoint_iff (n : ℕ) (r : ℝ) :
    Pairwise (fun v w : BinaryPackingLattice n =>
      Disjoint (ball (v : AbelianRealHyperplane (BinaryPackingGroup n)) r)
        (ball (w : AbelianRealHyperplane (BinaryPackingGroup n)) r)) ↔ r ≤ 1 :=
  abelianAugmentationRealLattice_balls_disjoint_iff _ (binaryPackingGroup_card_ge_four n) r

/-- The elementary abelian family has a genuine asymptotic packing density. -/
theorem binaryPacking_density_limit (n : ℕ) :
    Tendsto (fun r : ℝ => densityAt (BinaryPackingLattice n) r) atTop
      (𝓝 (abelianPackingDensity (BinaryPackingGroup n))) :=
  abelianPackingDensity_limit _ (by have h := binaryPackingGroup_card_ge_four n; omega)

#print axioms binaryPacking_density_limit
#print axioms binaryPackingGroup_not_cyclic
#print axioms binaryPacking_covolume_sq
#print axioms binaryPacking_balls_disjoint_iff
end GaloisForLFunctions.RepresentationLifting
