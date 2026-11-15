import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicRootlessFamily
import GaloisForLFunctions.HTGeometry.Lattices.IntegralEnergyGeometry

/-!
# Unit ball packings from cyclic difference lattices

Embed the cyclic difference lattice into the real zero-sum hyperplane using
its integral regular coordinates. Squared Euclidean distance is the integral
energy of the difference, so distinct centers are at distance at least two.
Their open unit balls are pairwise disjoint. For every cyclic order at least
four, the norm-four witness gives two centers at distance exactly two.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry.IntegerLatticePoisson
variable (G : Type) [CommGroup G] [Fintype G] [IsCyclic G]

/-- The zero-sum hyperplane with its inherited Euclidean distance. -/
abbrev CyclicPackingHyperplane := {x : EuclideanSpace ℝ G // ∑ g, x g = 0}

/-- The Euclidean realization of an integral cyclic difference vector. -/
def cyclicDifferencePoint (v : CyclicDifferenceLattice G) : CyclicPackingHyperplane G :=
  ⟨euclideanIntegerPoint (cyclicMovingProfile G v), by
    change ∑ g, (cyclicMovingProfile G v g : ℝ) = 0
    exact_mod_cast cyclicMovingProfile_sum G v⟩

/-- Squared distance is the integral energy of the difference. -/
theorem cyclicDifferencePoint_dist_sq (v w : CyclicDifferenceLattice G) :
    dist (cyclicDifferencePoint G v) (cyclicDifferencePoint G w)^2 =
      (cyclicMovingEnergy G (v - w) : ℝ) := by
  change dist (euclideanIntegerPoint (cyclicMovingProfile G v))
    (euclideanIntegerPoint (cyclicMovingProfile G w))^2 = _
  rw [euclideanIntegerPoint_dist_sq]
  rw [← map_sub]
  rfl

/-- Distinct cyclic difference vectors give centers separated by at least two. -/
theorem cyclicDifferencePoint_separated (v w : CyclicDifferenceLattice G) (hvw : v ≠ w) :
    2 ≤ dist (cyclicDifferencePoint G v) (cyclicDifferencePoint G w) := by
  have h := cyclicDifference_energy_ge_four G (v - w) (sub_ne_zero.mpr hvw)
  have hr : (4 : ℝ) ≤ (cyclicMovingEnergy G (v - w) : ℝ) := by exact_mod_cast h
  rw [← cyclicDifferencePoint_dist_sq] at hr
  nlinarith only [hr, dist_nonneg (x := cyclicDifferencePoint G v) (y := cyclicDifferencePoint G w)]

/-- Integral cyclic difference vectors embed injectively into the hyperplane. -/
theorem cyclicDifferencePoint_injective : Function.Injective (cyclicDifferencePoint G) := by
  intro v w h
  by_contra hvw
  have hs := cyclicDifferencePoint_separated G v w hvw
  rw [h, dist_self] at hs
  norm_num at hs

/-- The rootless energy bound gives disjoint open unit balls. -/
theorem cyclicDifference_unitBalls_disjoint (v w : CyclicDifferenceLattice G) (hvw : v ≠ w) :
    Disjoint (Metric.ball (cyclicDifferencePoint G v) 1) (Metric.ball (cyclicDifferencePoint G w) 1) := by
  apply Metric.ball_disjoint_ball
  simpa only [one_add_one_eq_two] using cyclicDifferencePoint_separated G v w hvw

/-- The explicit cyclic family gives a unit ball packing in every rank at least three. -/
theorem cyclicPacking_unitBalls_disjoint (n : ℕ) :
    Pairwise (fun v w : CyclicPackingLattice n =>
      Disjoint (Metric.ball (cyclicDifferencePoint (CyclicPackingGroup n) v) 1)
        (Metric.ball (cyclicDifferencePoint (CyclicPackingGroup n) w) 1)) :=
  fun v w hvw => cyclicDifference_unitBalls_disjoint _ v w hvw

/-- The separation bound is attained in every lattice of the explicit family. -/
theorem cyclicPacking_distance_two_exists (n : ℕ) :
    ∃ v w : CyclicPackingLattice n, v ≠ w ∧
      dist (cyclicDifferencePoint (CyclicPackingGroup n) v)
        (cyclicDifferencePoint (CyclicPackingGroup n) w) = 2 := by
  obtain ⟨v, hv⟩ := cyclicDifference_energy_four_exists (CyclicPackingGroup n)
    (by rw [cyclicPackingGroup_card]; omega)
  have hs := cyclicDifferencePoint_dist_sq (CyclicPackingGroup n) v 0
  simp only [Submodule.coe_zero, sub_zero, hv, Int.cast_ofNat] at hs
  have hd : dist (cyclicDifferencePoint (CyclicPackingGroup n) v)
      (cyclicDifferencePoint (CyclicPackingGroup n) 0) = 2 := by
    nlinarith only [hs, dist_nonneg (x := cyclicDifferencePoint (CyclicPackingGroup n) v)
      (y := cyclicDifferencePoint (CyclicPackingGroup n) 0)]
  refine ⟨v, 0, ?_, hd⟩
  intro h
  rw [h, dist_self] at hd
  norm_num at hd

#print axioms cyclicPacking_distance_two_exists
#print axioms cyclicDifferencePoint_dist_sq
#print axioms cyclicPacking_unitBalls_disjoint
end GaloisForLFunctions.RepresentationLifting
