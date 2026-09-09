import GaloisForLFunctions.HTGeometry.ConservativeDissipativeKMS
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeMasterFlow
import GaloisForLFunctions.RHTower.MobiusIncidenceClockGiniFisherFourUnit

set_option autoImplicit false

/-!
# Incidence Gini clock energy as an actual dissipation rate

Applying the Schaffer–Exl energy mechanism (arXiv:2609.04530) to the
corpus's finite incidence KMS realization gives a concrete positive
transport. At its initial normalized Gibbs state, the free-energy loss
rate equals the negative Gini clock energy, equivalently the negative
layer-cake relative clock energy. Exponential parameters and consecutive
positive labels discharge every sign and injectivity condition.
-/
open scoped BigOperators NNReal
namespace GaloisForLFunctions.RHTower.SchafferExl
noncomputable section
open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.SchafferExl

/-- Positive distinct labels of an arbitrary finite incidence packet. -/
def incidenceTransportLabels (n : ℕ) (i : Fin (n + 1)) : ℕ := i.val + 1

theorem incidenceTransportLabels_pos (n : ℕ) (i : Fin (n + 1)) :
    0 < incidenceTransportLabels n i := Nat.zero_lt_succ _

theorem incidenceTransportLabels_injective (n : ℕ) : Function.Injective (incidenceTransportLabels n) := by
  intro i j h
  exact Fin.ext (Nat.add_right_cancel h)

/-- Logarithmic Gibbs populations for the existing incidence Hamiltonian. -/
def incidenceTransportCoordinates (n : ℕ) (s e : ℝ) : Fin (n + 1) → ℝ :=
  entropyGibbsCoordinate (finiteIncidenceInverseTemperature (Real.exp s) (Real.exp e))
    (finiteIncidenceEnergy (Real.exp e) (incidenceTransportLabels n))

/-- Phase-insensitive transport coefficients obtained from the existing Hermitian incidence amplitudes. -/
def incidenceTransportWeights (n : ℕ) (s e : ℝ) (i j : Fin (n + 1)) : ℝ :=
  ‖finiteIncidenceKMSAmplitude (Real.exp s) (Real.exp e) (incidenceTransportLabels n) i j‖

/-- The constructed transport starts from the literal normalized incidence populations. -/
theorem exp_incidenceTransportCoordinates (n : ℕ) (s e : ℝ) (i : Fin (n + 1)) :
    Real.exp (incidenceTransportCoordinates n s e i) =
      finiteIncidenceProbability (Real.exp s) (incidenceTransportLabels n) i := by
  rw [incidenceTransportCoordinates, exp_entropyGibbsCoordinate]
  exact finiteGibbsStateWeight_incidence (Real.exp_pos s) (Real.exp_pos e)
    (incidenceTransportLabels_pos n) i

/-- Symmetrization doubles precisely the existing squared amplitude. -/
theorem incidenceTransportConductance (n : ℕ) (s e : ℝ) (i j : Fin (n + 1)) :
    entropyConductance (incidenceTransportWeights n s e) i j =
      2 * Complex.normSq (finiteIncidenceKMSAmplitude (Real.exp s) (Real.exp e)
        (incidenceTransportLabels n) i j) := by
  simp only [entropyConductance, incidenceTransportWeights,
    finiteIncidenceKMSAmplitude_hermitian (Real.exp s) (Real.exp e) (incidenceTransportLabels n) i j,
    norm_star, Complex.sq_norm]
  ring

/-- Exact transport-to-KMS edge loss, with no assumed Hermitian or positive data. -/
theorem incidenceTransport_production (n : ℕ) (s e : ℝ) (i j : Fin (n + 1)) :
    entropyConductance (incidenceTransportWeights n s e) i j *
      entropyProductionValue (Real.exp (incidenceTransportCoordinates n s e i))
        (Real.exp (incidenceTransportCoordinates n s e j)) =
      2 * finiteKMSEntropyProductionTransitionIntensity
        (finiteIncidenceInverseTemperature (Real.exp s) (Real.exp e))
        (finiteIncidenceEnergy (Real.exp e) (incidenceTransportLabels n))
        (finiteIncidenceKMSAmplitude (Real.exp s) (Real.exp e) (incidenceTransportLabels n)) i j := by
  rw [incidenceTransportConductance,
    finiteKMSEntropyProductionTransitionIntensity_eq_entropyProductionValue_mul_normSq _ _ _
      (finiteIncidenceKMSAmplitude_hermitian _ _ _)]
  simp only [incidenceTransportCoordinates, exp_entropyGibbsCoordinate]
  rw [entropyProductionValue_reverse (_root_.HTGeometry.finiteGibbsStateWeight_pos _ _ j)
    (_root_.HTGeometry.finiteGibbsStateWeight_pos _ _ i)]
  ring

/-- Actual positive forward transport attached to the finite incidence packet. -/
def incidenceTransportFlow (n : ℕ) (s e : ℝ) (t : ℝ) : Fin (n + 1) → ℝ :=
  masterLogFlow (incidenceTransportWeights n s e) 0 (incidenceTransportCoordinates n s e) t

/-- The finite Gini clock energy is exactly the initial free-energy dissipation rate. -/
theorem hasDerivAt_incidenceTransport_energy (n : ℕ) (s e : ℝ) :
    HasDerivAt (fun t : ℝ => relativeEntropyEnergy 0 (incidenceTransportFlow n s e t))
      (-finiteIncidenceGiniEnergy (Real.exp s) (Real.exp e) (incidenceTransportLabels n)) 0 := by
  apply (hasDerivAt_masterLogFlow_energy (incidenceTransportWeights n s e) 0
    (incidenceTransportCoordinates n s e) (0 : ℝ≥0)).congr_deriv
  simp only [NNReal.coe_zero, masterLogFlow_zero, incidenceTransport_production, ← Finset.mul_sum]
  rw [sum_finiteKMSEntropyProductionTransitionIntensity_incidence (Real.exp_pos s) (Real.exp_pos e)
    (incidenceTransportLabels_pos n) (incidenceTransportLabels_injective n)]
  ring

/-- The same initial rate is the existing layer-cake relative clock energy. -/
theorem hasDerivAt_incidenceTransport_relativeClockEnergy (n : ℕ) (s e : ℝ) :
    HasDerivAt (fun t : ℝ => relativeEntropyEnergy 0 (incidenceTransportFlow n s e t))
      (-finiteIncidenceRelativeClockEnergy (Real.exp s) (Real.exp e) (incidenceTransportLabels n)) 0 := by
  rw [finiteIncidenceRelativeClockEnergy_eq_gini (incidenceTransportLabels_pos n)]
  exact hasDerivAt_incidenceTransport_energy n s e

/-- Normalized incidence population mass is preserved for the full positive forward trajectory. -/
theorem incidenceTransport_mass (n : ℕ) (s e : ℝ) (t : ℝ≥0) :
    ∑ i, Real.exp (incidenceTransportFlow n s e t i) = 1 := by
  have hp (i : Fin (n + 1)) : Real.exp (incidenceTransportFlow n s e t i) =
      masterPopulationFlow (incidenceTransportWeights n s e) 0 (incidenceTransportCoordinates n s e) t i := by
    simpa only [Pi.zero_apply, zero_add, incidenceTransportFlow] using
      exp_masterLogFlow (incidenceTransportWeights n s e) 0 (incidenceTransportCoordinates n s e) t i
  simp_rw [hp]
  rw [masterPopulationFlow, masterEvolution_mass]
  simp only [Pi.zero_apply, zero_add, exp_incidenceTransportCoordinates]
  exact sum_finiteIncidenceProbability (incidenceTransportLabels_pos n)

end
end GaloisForLFunctions.RHTower.SchafferExl
