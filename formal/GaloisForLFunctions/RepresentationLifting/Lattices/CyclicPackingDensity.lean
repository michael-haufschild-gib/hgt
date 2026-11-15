import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicRealLattice
import GaloisForLFunctions.HTGeometry.Lattices.LatticePackingDensity

/-!
# The geometric density of cyclic lattice packings

The cyclic difference lattice embeds in a real hyperplane of dimension
`|G| - 1`, with covolume `sqrt(|G|^3)` and disjoint open unit balls. Its
covered-volume fraction has a limit along all real observation radii.
For the explicit order `n + 4` family, the limit is an explicit positive
Gamma-function quotient and is at most one.
-/

open MeasureTheory Metric Module Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry HTGeometry.LatticePackingDensity
variable (G : Type) [CommGroup G] [Fintype G] [IsCyclic G] [DecidableEq G]

omit [DecidableEq G] in
/-- Disjointness of the original centers passes to the actual real lattice. -/
theorem cyclicDifferenceRealLattice_unitBalls_disjoint :
    Pairwise (fun v w : cyclicDifferenceRealLattice G =>
      Disjoint (ball (v : CyclicRealHyperplane G) 1) (ball (w : CyclicRealHyperplane G) 1)) := by
  intro v w hvw
  obtain ⟨a, ha⟩ := v.property
  obtain ⟨b, hb⟩ := w.property
  have hab : a ≠ b := by
    intro h
    apply hvw
    apply Subtype.ext
    rw [← ha, ← hb, h]
  have hd := cyclicDifference_unitBalls_disjoint G a b hab
  change Disjoint (ball (cyclicDifferenceRealMap G a) 1) (ball (cyclicDifferenceRealMap G b) 1) at hd
  simpa only [ha, hb] using hd

/-- The occupied fraction tends to unit-ball volume divided by the arithmetic covolume. -/
theorem cyclicDifference_density_limit :
    Tendsto (fun r : ℝ => densityAt (cyclicDifferenceRealLattice G) r) atTop
      (𝓝 (volume.real (ball (0 : CyclicRealHyperplane G) 1) /
        Real.sqrt ((Fintype.card G : ℝ)^3))) := by
  have h := tendsto_density_real (cyclicDifferenceRealLattice G)
    (cyclicDifferenceRealLattice_unitBalls_disjoint G)
  rwa [cyclicDifferenceRealLattice_covolume] at h

theorem cyclicPackingHyperplane_finrank (n : ℕ) :
    finrank ℝ (CyclicRealHyperplane (CyclicPackingGroup n)) = n + 3 := by
  have h := cyclicRealHyperplane_rank (CyclicPackingGroup n)
  rw [cyclicPackingGroup_card] at h
  omega

/-- Unit-ball volume in the rank `n + 3` packing hyperplane. -/
theorem cyclicPacking_unitBall_volume (n : ℕ) :
    volume.real (ball (0 : CyclicRealHyperplane (CyclicPackingGroup n)) 1) =
      (Real.sqrt Real.pi)^(n + 3) / Real.Gamma ((n + 3 : ℝ) / 2 + 1) := by
  letI : Nontrivial (CyclicRealHyperplane (CyclicPackingGroup n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [cyclicPackingHyperplane_finrank]; omega)
  rw [measureReal_def, InnerProductSpace.volume_ball, cyclicPackingHyperplane_finrank,
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal]
  · norm_cast
  · exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.Gamma_pos_of_pos (by positivity)).le

/-- The explicit density of the rank `n + 3` cyclic unit-ball packing. -/
def cyclicPackingDensity (n : ℕ) : ℝ :=
  (Real.sqrt Real.pi)^(n + 3) /
    (Real.Gamma ((n + 3 : ℝ) / 2 + 1) * Real.sqrt ((n + 4 : ℝ)^3))

/-- The explicit quotient is the limit of actual covered-volume ratios. -/
theorem cyclicPacking_density_limit (n : ℕ) :
    Tendsto (fun r : ℝ => densityAt (cyclicDifferenceRealLattice (CyclicPackingGroup n)) r)
      atTop (𝓝 (cyclicPackingDensity n)) := by
  have h := cyclicDifference_density_limit (CyclicPackingGroup n)
  rw [cyclicPacking_unitBall_volume, cyclicPackingGroup_card] at h
  simpa only [Nat.cast_add, Nat.cast_ofNat, div_div, cyclicPackingDensity] using h

theorem cyclicPackingDensity_eq (n : ℕ) :
    cyclicPackingDensity n =
      volume.real (ball (0 : CyclicRealHyperplane (CyclicPackingGroup n)) 1) /
        ZLattice.covolume (cyclicDifferenceRealLattice (CyclicPackingGroup n)) := by
  rw [cyclicPacking_unitBall_volume, cyclicPacking_covolume, div_div]
  rfl

theorem cyclicPackingDensity_pos (n : ℕ) : 0 < cyclicPackingDensity n := by
  rw [cyclicPackingDensity_eq]
  exact div_pos (unitBall_volume_pos (E := CyclicRealHyperplane (CyclicPackingGroup n)))
    (ZLattice.covolume_pos (cyclicDifferenceRealLattice (CyclicPackingGroup n)) volume)

theorem cyclicPackingDensity_le_one (n : ℕ) : cyclicPackingDensity n ≤ 1 := by
  rw [cyclicPackingDensity_eq]
  exact unitBall_div_covolume_le_one _
    (cyclicDifferenceRealLattice_unitBalls_disjoint (CyclicPackingGroup n))

#print axioms cyclicPacking_density_limit
#print axioms cyclicPackingDensity_pos
#print axioms cyclicPackingDensity_le_one
end GaloisForLFunctions.RepresentationLifting
