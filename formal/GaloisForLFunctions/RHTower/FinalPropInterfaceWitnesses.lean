import GaloisForLFunctions.RHTower.FinitePrimeAutonomousOrderFloor
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiAdaptiveCofinalLanding
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCheckpointAffineReduction
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyReporterSecantSharpArithmeticLocalization
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAffineMixtureTriangularCurvatureReduction
import GaloisForLFunctions.RHTower.EulerSquarefreeWickArtinInteractionNoGo
import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedJetHorizontalFaithfulness
import GaloisForLFunctions.RHTower.RealCoronaUniversalTransgression
import GaloisForLFunctions.RHTower.ZeroResonanceIndependence

/-!
# Final proposition-interface witnesses

Concrete endpoint models for structural predicates used throughout `RHTower`: the zero autonomous
carrier, a zero reporter lag, the zero gauge-invariant reader, and reflexive projective agreement of
the completed Euler--Wick jet.
-/

open scoped BoundedContinuousFunction NNReal

namespace GaloisForLFunctions

noncomputable section

/-- The Bohr hull of the zero bounded continuous function is a singleton. -/
theorem bohrHull_zero_subsingleton (x y : BohrHull (0 : ℝ →ᵇ ℂ)) : x = y := by
  refine GaloisForLFunctions.bohrHull_ext
    (f := (0 : ℝ →ᵇ ℂ)) (hf := uniformContinuous_const) ?_
  intro t
  have hx0 : bohrEval (0 : ℝ →ᵇ ℂ)
      (x + bohrIota (0 : ℝ →ᵇ ℂ) t) = 0 := by
    have hle := norm_bohrEval_le (0 : ℝ →ᵇ ℂ)
      (x + bohrIota (0 : ℝ →ᵇ ℂ) t)
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hle) (norm_nonneg _)
  have hy0 : bohrEval (0 : ℝ →ᵇ ℂ)
      (y + bohrIota (0 : ℝ →ᵇ ℂ) t) = 0 := by
    have hle := norm_bohrEval_le (0 : ℝ →ᵇ ℂ)
      (y + bohrIota (0 : ℝ →ᵇ ℂ) t)
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hle) (norm_nonneg _)
  rw [hx0, hy0]

/-- Every order admits the regular locally unique carrier furnished by the zero Bohr hull. -/
theorem hasRegularLocallyUniqueAutonomousCarrier_zero (n : ℕ) :
    HasRegularLocallyUniqueAutonomousCarrier (0 : ℝ →ᵇ ℂ) n := by
  let J : BohrHull (0 : ℝ →ᵇ ℂ) → EuclideanSpace ℝ (Fin (n * 2)) := fun _ => 0
  refine ⟨J, continuous_const, ?_, ?_⟩
  · intro x y _
    exact bohrHull_zero_subsingleton x y
  · intro t x
    refine ⟨Set.univ, id, isOpen_univ, Set.mem_univ _, continuousOn_id,
      Set.injOn_id Set.univ, ?_⟩
    intro y hy
    rfl

end

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Zero in the first reporter leg gives literal transition separation from every lag. -/
theorem suzukiReporterSecantTransitionSeparated_zero_left (q : ℝ≥0) :
    suzukiReporterSecantTransitionSeparated 0 q :=
  Or.inl rfl

/-- The zero scalar reader is invariant under every quadratic-residue gauge translation. -/
theorem quadraticResidueGaugeInvariantScalarReader_zero :
    QuadraticResidueGaugeInvariantScalarReader
      (0 : (FullValueSubtype QuadraticResidueGaugeSpace → ℂ) →ₗ[ℂ] ℂ) := by
  intro u f
  simp

/-- Every completed Euler--Wick jet agrees projectively with itself. -/
theorem eulerWickPrimitiveCompletedJetsProjectivelyAgree_refl (s : ℂ) :
    EulerWickPrimitiveCompletedJetsProjectivelyAgree s s := by
  refine ⟨1, one_ne_zero, ?_⟩
  intro n
  simp

end
end RHTower
end GaloisForLFunctions
