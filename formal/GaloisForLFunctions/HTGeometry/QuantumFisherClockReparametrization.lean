import GaloisForLFunctions.HTGeometry.FiniteClockQuantumFisher

/-!
# Quantum-Fisher clock reparameterization

Quantum Fisher information is a quadratic density in the chosen clock coordinate, not an
absolute rate.  If a local change of clock multiplies the state tangent by `clockRate`, its QFI
is multiplied by `clockRate ^ 2`; the reciprocal coordinate increment cancels that factor.
Consequently the Fisher line value and the distinction between observable and invisible clock
tangents are independent of clock calibration.

This is a static observability law.  It assumes no Hamiltonian evolution.  It applies directly
to the finite-clock QFI/Kadison-variance identity: clock averaging supplies the observer algebra,
while the line value removes the arbitrary coordinate rate.

Physics provenance: the Fisher/Bures/Fubini--Study line element is the operational statistical
distance of Braunstein--Caves, Phys. Rev. Lett. 72 (1994), 3439--3443,
DOI 10.1103/PhysRevLett.72.3439.  Quantum-clock redshift as a local change of relational time is
used by Cafasso--Pranzini--Malo--Giovannetti--Chiofalo, Phys. Rev. D 110 (2024), 106014,
DOI 10.1103/PhysRevD.110.106014.  The separation between a generator and an operator carrying
nonzero time Fisher information is emphasized by Wani--Quach--Faizal, EPL 139 (2022), 62002,
arXiv:2106.07121.  The algebra below isolates the common coordinate-free value relation without
adopting the dynamics or interpretation of any one model.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

/-- The local quantum-Fisher length contributed by one clock-coordinate increment. -/
def quantumFisherClockLineValue
    (mass overlap speedSq clockIncrement : ℝ) : ℝ :=
  pureStateQuantumFisherValue mass overlap speedSq * clockIncrement ^ 2

/-- Rescaling the clock tangent rescales its projective value quadratically. -/
theorem projectiveQuantumTangentValue_clockRateScale
    (mass overlap speedSq clockRate : ℝ) :
    projectiveQuantumTangentValue mass (clockRate * overlap)
        (clockRate ^ 2 * speedSq) =
      clockRate ^ 2 * projectiveQuantumTangentValue mass overlap speedSq := by
  unfold projectiveQuantumTangentValue
  ring

/-- Quantum Fisher information is a covariant quadratic density under a change of clock rate. -/
theorem pureStateQuantumFisherValue_clockRateScale
    (mass overlap speedSq clockRate : ℝ) :
    pureStateQuantumFisherValue mass (clockRate * overlap)
        (clockRate ^ 2 * speedSq) =
      clockRate ^ 2 * pureStateQuantumFisherValue mass overlap speedSq := by
  unfold pureStateQuantumFisherValue
  rw [projectiveQuantumTangentValue_clockRateScale]
  ring

/-- The Fisher line value is unchanged when the tangent and coordinate increment transform
contragrediently. -/
theorem quantumFisherClockLineValue_reparameterize
    (mass overlap speedSq clockRate newIncrement : ℝ) :
    quantumFisherClockLineValue mass (clockRate * overlap)
        (clockRate ^ 2 * speedSq) newIncrement =
      quantumFisherClockLineValue mass overlap speedSq
        (clockRate * newIncrement) := by
  unfold quantumFisherClockLineValue
  rw [pureStateQuantumFisherValue_clockRateScale]
  ring

/-- Local clock redshift changes the numerical QFI but not Fisher length. -/
theorem quantumFisherClockLineValue_invariant_of_reciprocalClockChange
    (mass overlap speedSq clockRate oldIncrement newIncrement : ℝ)
    (hchange : clockRate * newIncrement = oldIncrement) :
    quantumFisherClockLineValue mass (clockRate * overlap)
        (clockRate ^ 2 * speedSq) newIncrement =
      quantumFisherClockLineValue mass overlap speedSq oldIncrement := by
  rw [quantumFisherClockLineValue_reparameterize, hchange]

/-- A nondegenerate change of clock coordinate preserves whether the clock tangent is observable. -/
theorem pureStateQuantumFisherValue_clockRateScale_eq_zero_iff
    (mass overlap speedSq : ℝ) {clockRate : ℝ} (hrate : clockRate ≠ 0) :
    pureStateQuantumFisherValue mass (clockRate * overlap)
        (clockRate ^ 2 * speedSq) = 0 ↔
      pureStateQuantumFisherValue mass overlap speedSq = 0 := by
  rw [pureStateQuantumFisherValue_clockRateScale]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero 2 hrate))

/-- A nondegenerate change of clock coordinate preserves strict Fisher observability. -/
theorem pureStateQuantumFisherValue_clockRateScale_pos_iff
    (mass overlap speedSq : ℝ) {clockRate : ℝ} (hrate : clockRate ≠ 0) :
    0 < pureStateQuantumFisherValue mass (clockRate * overlap)
        (clockRate ^ 2 * speedSq) ↔
      0 < pureStateQuantumFisherValue mass overlap speedSq := by
  rw [pureStateQuantumFisherValue_clockRateScale]
  exact mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hrate)

/-- The line value corresponding to a static finite-clock observability variance. -/
def finiteClockObservabilityLineValue
    (observabilityVariance clockIncrement : ℝ) : ℝ :=
  4 * observabilityVariance * clockIncrement ^ 2

/-- Quadratic clock-rate covariance also makes the static observability line coordinate-free. -/
theorem finiteClockObservabilityLineValue_reparameterize
    (observabilityVariance clockRate oldIncrement newIncrement : ℝ)
    (hchange : clockRate * newIncrement = oldIncrement) :
    finiteClockObservabilityLineValue
        (clockRate ^ 2 * observabilityVariance) newIncrement =
      finiteClockObservabilityLineValue observabilityVariance oldIncrement := by
  unfold finiteClockObservabilityLineValue
  rw [← hchange]
  ring

variable {K E : Type*} [RCLike K]
  [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]

/-- The finite-clock QFI/variance identity is exactly an equality of coordinate-free clock line
values, not a premise about Hamiltonian evolution. -/
theorem finiteClock_erasedQuantumFisherClockLineValue_eq_observabilityLineValue
    (U X : E →L[K] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ)
    (clockIncrement : ℝ) :
    quantumFisherClockLineValue (‖ψ‖ ^ 2)
        (‖inner K ψ ((1 - finiteCyclicGaugeAverage U N) (X ψ))‖)
        (‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ 2)
        clockIncrement =
      finiteClockObservabilityLineValue
        (RCLike.re
          (inner K ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)))
        clockIncrement := by
  unfold quantumFisherClockLineValue finiteClockObservabilityLineValue
  rw [finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_observabilityVariance
    U X N hN hadjoint_mul hperiod hX hψnorm hψ]

end

end HTGeometry
