import GaloisForLFunctions.HTGeometry.StokesPuiseuxMicrolocalIndex
import GaloisForLFunctions.HTGeometry.StokesCellularCategory
import GaloisForLFunctions.HTGeometry.StokesFilteredReesCoarea

/-!
# The finite polarized Stokes--microlocal Witt law

For common-cover Puiseux coefficients, highest-difference contact generates both the directed
microlocal Hom index and the canonical threshold coarea decomposition.  The resulting quadratic
form is a sum of positive terminal and graded local channels minus one global rank square.  Thus
its restriction to the physical-rank-zero hyperplane is positive, and every nonnegative Rees
specialization preserves that positivity.

The theorem below packages these conclusions without taking a rooted tree, an irregularity
matrix, a microlocal multiplicity, or a cut decomposition as input.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

noncomputable section

namespace PuiseuxOrbitCoareaDatum

variable {n m K N : ℕ}

/-- **Finite polarized Stokes--microlocal Witt law.**  Puiseux coefficients alone generate:

1. every normalized directed microlocal Hom index;
2. the positive-channel-minus-one-rank-channel decomposition;
3. strict positivity after removal of the global physical-rank direction; and
4. the associated-graded norm of the canonical threshold filtration.
-/
theorem polarizedStokesMicrolocalWittLaw
    (d : PuiseuxOrbitCoareaDatum n m K N)
    (fiberRank : Fin n → ℕ) (x : Fin n → ℝ) :
    (∀ i j,
      d.normalizedMicrolocalHomMass fiberRank i j =
        d.toOrbitCoareaDatum.homIrregularity i j *
          ((fiberRank i : ℝ) * fiberRank j)) ∧
    d.toOrbitCoareaDatum.cartanQuadratic x =
      d.toOrbitCoareaDatum.terminalEnergy x +
        d.toOrbitCoareaDatum.blockEnergy x -
      (((K + 1 : ℕ) : ℝ) / N - 1) *
        d.toOrbitCoareaDatum.physicalRank x ^ 2 ∧
    (d.toOrbitCoareaDatum.physicalRank x = 0 → x ≠ 0 →
      0 < d.toOrbitCoareaDatum.cartanQuadratic x) ∧
    (∑ edge, d.toOrbitCoareaDatum.gradedChannel x edge ^ 2) =
      d.toOrbitCoareaDatum.blockEnergy x := by
  refine ⟨?_, d.cartanQuadratic_eq_coefficient_onePort x, ?_,
    d.toOrbitCoareaDatum.sum_gradedChannel_sq_eq_blockEnergy x⟩
  · exact fun i j => d.normalizedMicrolocalHomMass_eq fiberRank i j
  · exact fun hrank hx => d.cartanQuadratic_pos_of_physicalRank_eq_zero hrank hx

/-- The global negative channel is rigid under the whole nonnegative multi-Rees cone: all Rees
parameters act only on positive local channels. -/
theorem polarizedStokesMicrolocalWittLaw_rees
    (d : PuiseuxOrbitCoareaDatum n m K N)
    {parameter : Fin d.edgeCount → ℝ}
    (hparameter : ∀ edge, 0 ≤ parameter edge) {x : Fin n → ℝ}
    (hrank : d.toOrbitCoareaDatum.physicalRank x = 0) (hx : x ≠ 0) :
    0 < d.toOrbitCoareaDatum.reesCartanQuadratic parameter x :=
  d.toOrbitCoareaDatum.reesCartanQuadratic_pos_of_physicalRank_eq_zero
    hparameter hrank hx

end PuiseuxOrbitCoareaDatum

namespace CellularStokesCategory

open CellularMicrolocal

/-- Every cellular Stokes germ has an exact arc-to-nearby-to-vanishing sequence, functorially in
the germ; for the exponential germ, exactly one of the two oriented vanishing-cycle spaces has the
full fiber rank. -/
theorem categoricalVanishingShadow
    (F : GermCategory) (s : ConormalSide) {d : ℕ} (hd : 0 < d) (active : Bool) :
    Function.Exact (sideMap F s).hom (nearbyToVanishing F s) ∧
      Function.Surjective (nearbyToVanishing F s) ∧
      ((Module.finrank ℚ (microstalkSpace (exponentialGerm d active) .left) = d ∧
          Module.finrank ℚ (microstalkSpace (exponentialGerm d active) .right) = 0) ∨
        (Module.finrank ℚ (microstalkSpace (exponentialGerm d active) .left) = 0 ∧
          Module.finrank ℚ (microstalkSpace (exponentialGerm d active) .right) = d)) := by
  exact ⟨arc_wall_vanishing_exact F s, nearbyToVanishing_surjective F s,
    exponentialGerm_exactly_one_vanishing hd active⟩

end CellularStokesCategory

end
end IrregularStokes
end GaloisForLFunctions
