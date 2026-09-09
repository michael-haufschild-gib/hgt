import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinFidelity
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinDensityFlow
import GaloisForLFunctions.HTGeometry.FiniteBuresKrausDataProcessingLaw
import GaloisForLFunctions.HTGeometry.FiniteNuclearIncidenceLaw

/-!
# Deterministic quantum-channel obstruction for damped spin evolution

The Schaffer–Exl spin mechanism (arXiv:2609.04530) is combined with the
corpus's Bures rank-one identity and normalized finite-Kraus data-processing
law. A constructed nonorthogonal pure-state pair becomes orthogonal at a
positive finite time. Thus no common normalized finite Kraus channel can
implement those two outputs, and no such channel implements the full spin
map. The selective-instrument replacement is formalized separately.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- The corpus's full matrix Bures fidelity agrees with spinor fidelity on the constructed densities. -/
theorem spinChartDensity_bures_sq (z w : ℂ) :
    finiteBuresRootFidelity (spinChartDensity z) (spinChartDensity w) ^ 2 =
      finitePureStateFidelity (spinChartSpinor z) (spinChartSpinor w) := by
  have h := finiteBuresTrace_sq_weightedTargetMixture
    (fun _ : Unit => (1 : NNReal)) (fun _ : Unit => spinChartSpinor w) (spinChartSpinor z)
  simpa [finiteBuresRootFidelity, spinChartDensity, higgsSpinorEventMatrix,
    finiteWeightedCovarianceMatrix, finitePureStateFidelity] using h

/-- Bures fidelity of actual spin densities is exactly complementary chordal separation. -/
theorem spinChartDensity_bures_chordal (z w : ℂ) :
    finiteBuresRootFidelity (spinChartDensity z) (spinChartDensity w) ^ 2 =
      1 - _root_.Bottcher.chordalDist z w ^ 2 := by
  rw [spinChartDensity_bures_sq, spinChartSpinor_fidelity]

/-- The actual density trajectory inherits the previously proved spinor-fidelity law. -/
theorem spinDensityFlow_bures_sq (a : ℝ) (z w : ℂ) (t : ℝ) :
    finiteBuresRootFidelity (spinDensityFlow a z t) (spinDensityFlow a w t) ^ 2 =
      finitePureStateFidelity (spinSpinorFlow a z t) (spinSpinorFlow a w t) := by
  exact spinChartDensity_bures_sq _ _

/-- The constructed initial density pair has strictly positive full Bures root fidelity. -/
theorem spinSeparation_initial_bures_pos (x : ℝ) :
    0 < finiteBuresRootFidelity (spinChartDensity (spinSeparationSeed x))
      (spinChartDensity (-spinSeparationSeed x)) := by
  have h := spinSeparation_initial_fidelity_pos x
  rw [← spinChartDensity_bures_sq] at h
  have hn := finiteBuresRootFidelity_nonneg (C := spinChartDensity (spinSeparationSeed x))
    (spinChartDensity_posSemidef (-spinSeparationSeed x))
  nlinarith

/-- The evolved density pair has zero full Bures root fidelity at its positive separation time. -/
theorem spinSeparation_final_bures_zero (s x : ℝ) :
    finiteBuresRootFidelity
      (spinDensityFlow (Real.exp s) (spinSeparationSeed x) (spinSeparationTime s x))
      (spinDensityFlow (Real.exp s) (-spinSeparationSeed x) (spinSeparationTime s x)) = 0 := by
  have h := spinSeparation_final_fidelity_zero s x
  rw [← spinDensityFlow_bures_sq] at h
  nlinarith [sq_nonneg (finiteBuresRootFidelity
    (spinDensityFlow (Real.exp s) (spinSeparationSeed x) (spinSeparationTime s x))
    (spinDensityFlow (Real.exp s) (-spinSeparationSeed x) (spinSeparationTime s x)))]

/-- No normalized finite Kraus channel can implement even the constructed two-input evolution. -/
theorem spinSeparation_no_common_kraus {κ : Type*} [Fintype κ] [DecidableEq κ] (s x : ℝ) :
    ¬ ∃ Phi : FiniteRectangularKrausChannel 2 2 κ,
      Phi.evolveMatrix (spinChartDensity (spinSeparationSeed x)) =
        spinDensityFlow (Real.exp s) (spinSeparationSeed x) (spinSeparationTime s x) ∧
      Phi.evolveMatrix (spinChartDensity (-spinSeparationSeed x)) =
        spinDensityFlow (Real.exp s) (-spinSeparationSeed x) (spinSeparationTime s x) := by
  rintro ⟨Phi, hplus, hminus⟩
  have h := Phi.finiteBuresRootFidelity_le_evolve
    (spinChartDensity_posSemidef (spinSeparationSeed x))
    (spinChartDensity_posSemidef (-spinSeparationSeed x))
  rw [hplus, hminus, spinSeparation_final_bures_zero] at h
  exact (not_le_of_gt (spinSeparation_initial_bures_pos x)) h

/-- In particular, the nonlinear spin evolution at this positive time is not one deterministic channel. -/
theorem spinSeparation_no_global_kraus {κ : Type*} [Fintype κ] [DecidableEq κ] (s x : ℝ) :
    ¬ ∃ Phi : FiniteRectangularKrausChannel 2 2 κ,
      ∀ z : ℂ, Phi.evolveMatrix (spinChartDensity z) =
        spinDensityFlow (Real.exp s) z (spinSeparationTime s x) := by
  rintro ⟨Phi, h⟩
  exact spinSeparation_no_common_kraus s x ⟨Phi, h _, h _⟩

end
end GaloisForLFunctions.HTGeometry.SchafferExl
