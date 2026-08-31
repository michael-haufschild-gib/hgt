import GaloisForLFunctions.HTGeometry.FreeToricIsogenyTail
import GaloisForLFunctions.HTGeometry.ToricDiagonalExpandingTail

/-!
# Unconditional coordinatewise diagonal split-torus tail

The free differential rational field constructs every genericity, generation, and constant-field
witness needed by the coordinatewise diagonal torus theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

local instance freeDiagonalComplexDifferential : Differential ℂ := ⟨0⟩

local instance freeDiagonalDifferentialAlgebra (r : ℕ) :
    DifferentialAlgebra ℂ (JetField ℂ (Fin r)) := by
  refine ⟨fun z => ?_⟩
  rw [JetField.deriv_algebraMap z]
  exact (map_zero _).symm

/-- **Unconditional coordinatewise diagonal split-torus isogeny tail.**  Every coordinate degree
is encoded as an integer at least two, so nonsingularity and character separation are constructed
rather than supplied. -/
theorem freeToricDiagonalIsogenyTail (r : ℕ) (D : Fin r → {n : ℕ // 2 ≤ n}) :
    let x := freeTorusGenerator r
    let d : Fin r → ℕ := fun i => (D i).1
    stableRangeCore
        (torusEndo (differentialIndependent_freeTorusGenerator r)
          (differentialAdjoin_freeTorusGenerator_eq_top r)
          (det_diagonalPowerMatrix_ne_zero fun i => (D i).2)) =
        torusVelocityField ℂ x
      ∧ DifferentialIndependent ℂ (fun k => Differential.logDeriv (x k))
      ∧ torusVelocityField ℂ x ⊓ IntermediateField.adjoin ℂ (Set.range x) =
          (⊥ : IntermediateField ℂ (JetField ℂ (Fin r)))
      ∧ ∀ i, torusEndo (differentialIndependent_freeTorusGenerator r)
          (differentialAdjoin_freeTorusGenerator_eq_top r)
          (det_diagonalPowerMatrix_ne_zero fun j => (D j).2)
          (Differential.logDeriv (x i)) =
            (d i : JetField ℂ (Fin r)) * Differential.logDeriv (x i) := by
  exact toricDiagonalIsogenyTail
    (differentialIndependent_freeTorusGenerator r)
    (differentialAdjoin_freeTorusGenerator_eq_top r)
    deriv_complex_eq_zero (fun i => (D i).2)

end

end GaloisForLFunctions.HTGeometry
