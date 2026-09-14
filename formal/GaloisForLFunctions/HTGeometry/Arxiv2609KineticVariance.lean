import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank
import GaloisForLFunctions.HTGeometry.MomentMatrixMechanics
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite kinetic variance and endpoint domain loss

Closed, unconditional kernels extracted from arXiv:2609.10085.

The paper's finite-state moment computation fits the corpus's spectral-moment and
moment-mechanics APIs exactly: kinetic-energy variance is the fourth velocity moment minus the
square of the second, divided by four, and its pure-state quantum Fisher value removes that
factor. Local unit phases preserve every finite energy moment and hence every polynomial QFI.

The paper's singular-flow existence input is explicitly not imported. Instead, the endpoint
domain mechanism is realized by the concrete compactly supported profile `x^(-1/4)`, which is in
`L²` and not in `L⁴`. This is the multiplication-operator model of form-domain membership without
operator-domain membership.
-/

open MeasureTheory Polynomial
open scoped BigOperators Interval

namespace HTGeometry

noncomputable section

/-! ## Finite kinetic moments -/

/-- Uniform probability mass on a guaranteed-nonempty finite velocity space. -/
def uniformKineticMass (n : ℕ) : Fin (n + 1) → ℝ :=
  fun _ ↦ ((n + 1 : ℕ) : ℝ)⁻¹

/-- Pointwise kinetic energy `u²/2`. -/
def kineticEnergy {n : ℕ} (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i ↦ u i ^ 2 / 2

/-- Uniform finite spectral moments of kinetic energy. -/
def uniformKineticMomentSequence {n : ℕ} (u : Fin (n + 1) → ℝ) : ℕ → ℝ :=
  finiteSpectralMoment (uniformKineticMass n) (kineticEnergy u)

/-- Uniform `k`th velocity-power mean. -/
def uniformVelocityPowerMean {n : ℕ} (u : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  (∑ i, u i ^ k) / (n + 1 : ℕ)

@[simp] theorem uniformKineticMomentSequence_zero {n : ℕ} (u : Fin (n + 1) → ℝ) :
    uniformKineticMomentSequence u 0 = 1 := by
  simp [uniformKineticMomentSequence, finiteSpectralMoment, uniformKineticMass]
  field_simp

/-- Uniform kinetic moments as a normalized corpus moment-mechanics state. -/
def uniformKineticMomentState {n : ℕ} (u : Fin (n + 1) → ℝ) :
    MomentMechanicsState where
  sequence := uniformKineticMomentSequence u
  vacuumMass_ne := by simp

theorem uniformKineticMomentSequence_one {n : ℕ} (u : Fin (n + 1) → ℝ) :
    uniformKineticMomentSequence u 1 = uniformVelocityPowerMean u 2 / 2 := by
  simp only [uniformKineticMomentSequence, finiteSpectralMoment, uniformKineticMass,
    kineticEnergy, uniformVelocityPowerMean, pow_one]
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem uniformKineticMomentSequence_two {n : ℕ} (u : Fin (n + 1) → ℝ) :
    uniformKineticMomentSequence u 2 = uniformVelocityPowerMean u 4 / 4 := by
  simp only [uniformKineticMomentSequence, finiteSpectralMoment, uniformKineticMass,
    kineticEnergy, uniformVelocityPowerMean]
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Paper's exact first/second-moment variance identity for a uniform finite state. -/
theorem uniformKineticVariance_formula {n : ℕ} (u : Fin (n + 1) → ℝ) :
    momentNormalizedVariance (uniformKineticMomentSequence u) X =
      (uniformVelocityPowerMean u 4 - uniformVelocityPowerMean u 2 ^ 2) / 4 := by
  rw [show (X : Polynomial ℝ) = X ^ 1 by simp,
    momentNormalizedVariance_X_pow, uniformKineticMomentSequence_zero,
    uniformKineticMomentSequence_one, uniformKineticMomentSequence_two]
  ring

/-- Existing moment-mechanics QFI is exactly the fourth-moment fluctuation numerator. -/
theorem uniformKineticQuantumFisher_formula {n : ℕ} (u : Fin (n + 1) → ℝ) :
    pureStateQuantumFisherValue
        ((uniformKineticMomentState u).sequence 0)
        (momentFunctional (uniformKineticMomentState u).sequence X)
        (momentFunctional (uniformKineticMomentState u).sequence (X ^ 2)) =
      uniformVelocityPowerMean u 4 - uniformVelocityPowerMean u 2 ^ 2 := by
  rw [momentMechanics_quantumFisher_eq_four_variance]
  exact (congrArg (fun x : ℝ ↦ 4 * x) (uniformKineticVariance_formula u)).trans (by ring)

/-! ## Exact finite phase transfer -/

/-- Finite normalized wavefunction, with normalization carried as state data. -/
structure FiniteSchrodingerState (d : ℕ) where
  amplitude : Fin d → ℂ
  normalized : ∑ i, Complex.normSq (amplitude i) = 1

/-- Spectral energy moments of a normalized finite wavefunction. -/
def finiteSchrodingerEnergyMoment {d : ℕ} (state : FiniteSchrodingerState d)
    (energy : Fin d → ℝ) : ℕ → ℝ :=
  finiteSpectralMoment (fun i ↦ Complex.normSq (state.amplitude i)) energy

@[simp] theorem finiteSchrodingerEnergyMoment_zero {d : ℕ}
    (state : FiniteSchrodingerState d) (energy : Fin d → ℝ) :
    finiteSchrodingerEnergyMoment state energy 0 = 1 := by
  simpa [finiteSchrodingerEnergyMoment, finiteSpectralMoment] using state.normalized

/-- Pointwise multiplication by arbitrary unit-circle phases preserves normalization. -/
def phaseRotateFiniteState {d : ℕ} (phase : Fin d → Circle)
    (state : FiniteSchrodingerState d) : FiniteSchrodingerState d where
  amplitude i := (phase i : ℂ) * state.amplitude i
  normalized := by
    simpa [Complex.normSq_mul] using state.normalized

/-- Every finite spectral energy moment survives local unit-phase transfer exactly. -/
theorem finiteSchrodingerEnergyMoment_phase_invariant {d : ℕ}
    (phase : Fin d → Circle) (state : FiniteSchrodingerState d) (energy : Fin d → ℝ) :
    finiteSchrodingerEnergyMoment (phaseRotateFiniteState phase state) energy =
      finiteSchrodingerEnergyMoment state energy := by
  funext k
  simp [finiteSchrodingerEnergyMoment, finiteSpectralMoment, phaseRotateFiniteState,
    Complex.normSq_mul]

/-- Finite Schrödinger energy moments packaged for corpus moment mechanics. -/
def finiteSchrodingerMomentState {d : ℕ} (state : FiniteSchrodingerState d)
    (energy : Fin d → ℝ) : MomentMechanicsState where
  sequence := finiteSchrodingerEnergyMoment state energy
  vacuumMass_ne := by simp

/-- Local unit phases preserve QFI of every polynomial energy observable. -/
theorem finiteSchrodingerQFI_phase_invariant {d : ℕ}
    (phase : Fin d → Circle) (state : FiniteSchrodingerState d)
    (energy : Fin d → ℝ) (observable : Polynomial ℝ) :
    pureStateQuantumFisherValue
        ((finiteSchrodingerMomentState (phaseRotateFiniteState phase state) energy).sequence 0)
        (momentFunctional
          (finiteSchrodingerMomentState (phaseRotateFiniteState phase state) energy).sequence
          observable)
        (momentFunctional
          (finiteSchrodingerMomentState (phaseRotateFiniteState phase state) energy).sequence
          (observable ^ 2)) =
      pureStateQuantumFisherValue
        ((finiteSchrodingerMomentState state energy).sequence 0)
        (momentFunctional (finiteSchrodingerMomentState state energy).sequence observable)
        (momentFunctional (finiteSchrodingerMomentState state energy).sequence (observable ^ 2)) := by
  rw [momentMechanics_quantumFisher_eq_four_variance,
    momentMechanics_quantumFisher_eq_four_variance]
  change 4 * momentNormalizedVariance
      (finiteSchrodingerEnergyMoment (phaseRotateFiniteState phase state) energy) observable =
    4 * momentNormalizedVariance (finiteSchrodingerEnergyMoment state energy) observable
  rw [finiteSchrodingerEnergyMoment_phase_invariant]

/-! ## Shell exponent and endpoint form/operator boundary -/

/-- Shell volume times fourth power of the paper's connection amplitude. -/
def exteriorShellFourthMomentExponent (h tau : ℝ) : ℝ :=
  tau ^ (3 / 2 - h) * (tau ^ (-1 / 2 - h)) ^ 4

/-- Exact exponent bookkeeping behind the fourth-moment growth rate. -/
theorem exteriorShellFourthMomentExponent_eq (h : ℝ) (tau : Set.Ioi (0 : ℝ)) :
    exteriorShellFourthMomentExponent h tau = tau ^ (-1 / 2 - 5 * h) := by
  rw [exteriorShellFourthMomentExponent, ← Real.rpow_natCast]
  rw [← Real.rpow_mul tau.2.le, ← Real.rpow_add tau.2]
  congr 1
  ring

/-- Explicit endpoint amplitude with critical fourth power. -/
def endpointConnectionAmplitude (x : ℝ) : ℝ := x ^ (-(1 : ℝ) / 4)

/-- Square of the endpoint amplitude. -/
def endpointConnectionEnergyDensity (x : ℝ) : ℝ := x ^ (-(1 : ℝ) / 2)

/-- Fourth power of the endpoint amplitude. -/
def endpointConnectionFourthDensity (x : ℝ) : ℝ := x ^ (-(1 : ℝ))

theorem endpointConnectionAmplitude_sq (x : Set.Ioi (0 : ℝ)) :
    endpointConnectionAmplitude x ^ 2 = endpointConnectionEnergyDensity x := by
  rw [endpointConnectionAmplitude, endpointConnectionEnergyDensity,
    ← Real.rpow_natCast, ← Real.rpow_mul x.2.le]
  congr 1
  norm_num

theorem endpointConnectionAmplitude_fourth (x : Set.Ioi (0 : ℝ)) :
    endpointConnectionAmplitude x ^ 4 = endpointConnectionFourthDensity x := by
  rw [endpointConnectionAmplitude, endpointConnectionFourthDensity,
    ← Real.rpow_natCast, ← Real.rpow_mul x.2.le]
  congr 1
  norm_num

/-- Sharp scalar boundary: the energy density is integrable but the fourth density is not. -/
theorem endpointConnection_integrability_boundary :
    IntegrableOn endpointConnectionEnergyDensity (Set.Ioo 0 1) ∧
      ¬ IntegrableOn endpointConnectionFourthDensity (Set.Ioo 0 1) := by
  constructor
  · change IntegrableOn (fun x : ℝ ↦ x ^ (-(1 : ℝ) / 2)) (Set.Ioo 0 1)
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff
      (by norm_num : (0 : ℝ) < 1)).2 (by norm_num)
  · change ¬ IntegrableOn (fun x : ℝ ↦ x ^ (-(1 : ℝ))) (Set.Ioo 0 1)
    intro h
    have hexponent := (intervalIntegral.integrableOn_Ioo_rpow_iff
      (by norm_num : (0 : ℝ) < 1)).1 h
    norm_num at hexponent

/-- Compactly supported endpoint profile on the ambient real line. -/
def endpointConnectionProfile : ℝ → ℝ :=
  (Set.Ioo (0 : ℝ) 1).indicator endpointConnectionAmplitude

private theorem endpointConnectionAmplitude_aestronglyMeasurable_restrict :
    AEStronglyMeasurable endpointConnectionAmplitude
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
  intro x hx
  exact (continuousAt_id.rpow_const (.inl hx.1.ne')).continuousWithinAt

private theorem endpointConnectionProfile_aestronglyMeasurable :
    AEStronglyMeasurable endpointConnectionProfile volume := by
  rw [endpointConnectionProfile, aestronglyMeasurable_indicator_iff measurableSet_Ioo]
  exact endpointConnectionAmplitude_aestronglyMeasurable_restrict

theorem endpointConnectionProfile_memLp_two :
    MemLp endpointConnectionProfile 2 volume := by
  rw [memLp_two_iff_integrable_sq endpointConnectionProfile_aestronglyMeasurable]
  have hsquare : (fun x ↦ endpointConnectionProfile x ^ 2) =
      (Set.Ioo (0 : ℝ) 1).indicator endpointConnectionEnergyDensity := by
    funext x
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · simpa [endpointConnectionProfile, Set.indicator_of_mem hx] using
        endpointConnectionAmplitude_sq ⟨x, hx.1⟩
    · simp [endpointConnectionProfile, hx]
  rw [hsquare, integrable_indicator_iff measurableSet_Ioo]
  exact endpointConnection_integrability_boundary.1

theorem endpointConnectionProfile_not_memLp_four :
    ¬ MemLp endpointConnectionProfile 4 volume := by
  intro h
  have hfour := h.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hpow : (fun x ↦ ‖endpointConnectionProfile x‖ ^ 4) =
      (Set.Ioo (0 : ℝ) 1).indicator endpointConnectionFourthDensity := by
    funext x
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · have hamp : 0 ≤ endpointConnectionAmplitude x :=
        Real.rpow_nonneg hx.1.le _
      simp only [endpointConnectionProfile, Set.indicator_of_mem hx]
      rw [Real.norm_eq_abs, abs_of_nonneg hamp]
      exact endpointConnectionAmplitude_fourth ⟨x, hx.1⟩
    · simp [endpointConnectionProfile, hx]
  rw [hpow, integrable_indicator_iff measurableSet_Ioo] at hfour
  exact endpointConnection_integrability_boundary.2 hfour

/-- Explicit form-domain/operator-domain separation: `L²` but not `L⁴`. -/
theorem endpointConnectionProfile_form_not_operator_domain :
    MemLp endpointConnectionProfile 2 volume ∧
      ¬ MemLp endpointConnectionProfile 4 volume :=
  ⟨endpointConnectionProfile_memLp_two, endpointConnectionProfile_not_memLp_four⟩

end

end HTGeometry
