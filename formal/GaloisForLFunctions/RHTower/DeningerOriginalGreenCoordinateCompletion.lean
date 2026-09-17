import GaloisForLFunctions.RHTower.DeningerOriginalGreenZeroDampingGerm
import GaloisForLFunctions.RHTower.DeningerOriginalPrimeGreenXiAdmission

/-!
# Coordinatewise zero-damping completion of the original prime Green source

Every native Xi coordinate of the literal original Green continuation has a
pole whose order is twice its own Xi multiplicity.  Consequently no common
scalar normalization can retain the complete divisor unless all multiplicities
are uniformly prescribed, and the literal field has no finite Xi-Hilbert
limit.  The source nevertheless has a canonical non-scalar completion: apply
the forced twice-multiplicity normalization separately at every native copy and
take the product topology.

This module retains the literal original-prime Mellin source on its admitted
half-plane, both native zeta jets, and every Xi copy.  It proves only the
coordinate product completion.  It does not identify that product completion
with a Green/BV source-domain completion or with the fixed physical reader.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The multiplicity-adaptively regularized original Green continuation, retaining every
native Xi copy as a coordinate.  This is deliberately a product field, not an `L²` vector. -/
def deningerOriginalPrimeGreenZeroDampingCoordinateField (p : Nat.Primes) (a : ℂ) :
    XiZeroCopy → ℂ :=
  fun q => deningerOriginalPrimeGreenZeroDampingRegularization p q.1 a

/-- The full coordinatewise leading field forced by the original prime and both zeta jets. -/
def deningerOriginalPrimeGreenZeroDampingCoefficientField (p : Nat.Primes) :
    XiZeroCopy → ℂ :=
  fun q => deningerOriginalPrimeGreenZeroDampingCoefficient p q.1

theorem deningerOriginalPrimeGreenZeroDampingCoordinateField_apply
    (p : Nat.Primes) (a : ℂ) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenZeroDampingCoordinateField p a q =
      deningerOriginalPrimeGreenZeroDampingRegularization p q.1 a := rfl

theorem deningerOriginalPrimeGreenZeroDampingCoefficientField_apply
    (p : Nat.Primes) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenZeroDampingCoefficientField p q =
      deningerOriginalPrimeGreenZeroDampingCoefficient p q.1 := rfl

/-- Every native coordinate has its forced, nonzero zero-damping coefficient. -/
theorem deningerOriginalPrimeGreenZeroDampingCoefficientField_apply_ne_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenZeroDampingCoefficientField p q ≠ 0 := by
  exact deningerOriginalPrimeGreenZeroDampingCoefficient_ne_zero p q.1

/-- The multiplicity-adaptively regularized field has an unconditional product-topology
zero-damping limit.  No common scalar power and no Hilbert norm are claimed. -/
theorem tendsto_deningerOriginalPrimeGreenZeroDampingCoordinateField
    (p : Nat.Primes) :
    Tendsto (deningerOriginalPrimeGreenZeroDampingCoordinateField p) (𝓝 (0 : ℂ))
      (𝓝 (deningerOriginalPrimeGreenZeroDampingCoefficientField p)) := by
  rw [tendsto_pi_nhds]
  intro q
  simpa only [deningerOriginalPrimeGreenZeroDampingCoordinateField_apply,
    deningerOriginalPrimeGreenZeroDampingCoefficientField_apply,
    deningerOriginalPrimeGreenZeroDampingRegularization_zero] using
    (deningerOriginalPrimeGreenZeroDampingRegularization_analyticAt p q.1).continuousAt.tendsto

/-- On the literal admitted half-plane, every coordinate is exactly the original Green Mellin
source multiplied by its own forced twice-multiplicity damping power. -/
theorem deningerOriginalPrimeGreenZeroDampingCoordinateField_eq_normalizedLiteral
    (a : {a : ℝ // 1 < a}) (p : Nat.Primes) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenZeroDampingCoordinateField p (a.val : ℂ) q =
      (a.val : ℂ) ^ (2 * xiSupportMultiplicity q.1) *
        deningerMeyerStrongLogMellin
          (deningerDampedOriginalPrimeGreen ⟨a.val, by linarith [a.property]⟩ p) (q.1 : ℂ) := by
  rw [deningerOriginalPrimeGreenZeroDampingCoordinateField_apply,
    deningerOriginalPrimeGreenZeroDampingRegularization,
    if_neg (ofReal_ne_zero.mpr (by linarith [a.property])),
    deningerOriginalPrimeGreenDampingContinuation_eq_literal]

/-- The coordinatewise boundary vector in the existing singular Gamma-six graph. -/
def deningerOriginalPrimeGreenZeroDampingCoordinateGraphBoundary
    (p : Nat.Primes) (a : ℂ) (q : XiZeroCopy) : DeningerGammaSixCofinalSingularGraph :=
  deningerOriginalPrimeGreenZeroDampingCoordinateField p a q •
    deningerGammaSixCofinalGraphSingularVector

/-- The unchanged fixed physical reader, applied at every coordinate of the product boundary. -/
def deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalReadoutField
    (p : Nat.Primes) (a : ℂ) : XiZeroCopy → DeningerGammaSixSoninPhysicalOperator :=
  fun q => deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
    (deningerOriginalPrimeGreenZeroDampingCoordinateGraphBoundary p a q)

/-- The fixed-reader limit of the full multiplicity-adaptive coordinate boundary. -/
def deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalLimitField
    (p : Nat.Primes) : XiZeroCopy → DeningerGammaSixSoninPhysicalOperator :=
  fun q => deningerOriginalPrimeGreenZeroDampingCoefficientField p q •
    deningerGammaSixFixedSoninPhysicalReceiver (2 * (q.1 : ℂ).re - 1)

/-- On the admitted source half-plane, the product-boundary vector is the actual full-Xi
Green boundary multiplied by the forced coordinatewise damping power. -/
theorem deningerOriginalPrimeGreenZeroDampingCoordinateGraphBoundary_eq_normalizedLiteral
    (a : {a : ℝ // 1 < a}) (p : Nat.Primes) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenZeroDampingCoordinateGraphBoundary p (a.val : ℂ) q =
      (a.val : ℂ) ^ (2 * xiSupportMultiplicity q.1) •
        deningerOriginalPrimeGreenXiGraphBoundary a p q := by
  change deningerOriginalPrimeGreenZeroDampingCoordinateField p (a.val : ℂ) q •
      deningerGammaSixCofinalGraphSingularVector =
    (a.val : ℂ) ^ (2 * xiSupportMultiplicity q.1) •
      (deningerOriginalPrimeGreenXiField a p q • deningerGammaSixCofinalGraphSingularVector)
  rw [deningerOriginalPrimeGreenZeroDampingCoordinateField_eq_normalizedLiteral,
    deningerOriginalPrimeGreenXiField_mellin, smul_smul]

/-- The existing Gamma-six physical transport commutes exactly with the non-scalar
coordinate boundary. -/
theorem deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalReadoutField_apply
    (p : Nat.Primes) (a : ℂ) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalReadoutField p a q =
      deningerOriginalPrimeGreenZeroDampingCoordinateField p a q •
        deningerGammaSixFixedSoninPhysicalReceiver (2 * (q.1 : ℂ).re - 1) := by
  rw [deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalReadoutField,
    deningerOriginalPrimeGreenZeroDampingCoordinateGraphBoundary, map_smul,
    deningerGammaSixCofinalGraphPhysicalTransport_singularVector]

/-- On admitted literal source fields, fixed physical transport commutes with the forced
coordinatewise normalization. -/
theorem deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalReadoutField_eq_normalizedLiteral
    (a : {a : ℝ // 1 < a}) (p : Nat.Primes) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalReadoutField p (a.val : ℂ) q =
      (a.val : ℂ) ^ (2 * xiSupportMultiplicity q.1) •
        deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
          (deningerOriginalPrimeGreenXiGraphBoundary a p q) := by
  change deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
      (deningerOriginalPrimeGreenZeroDampingCoordinateGraphBoundary p (a.val : ℂ) q) = _
  rw [deningerOriginalPrimeGreenZeroDampingCoordinateGraphBoundary_eq_normalizedLiteral,
    map_smul]

/-- The fixed physical reader has an unconditional product-topology zero-damping limit on the
complete multiplicity-adaptive boundary. -/
theorem tendsto_deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalReadoutField
    (p : Nat.Primes) :
    Tendsto (deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalReadoutField p) (𝓝 (0 : ℂ))
      (𝓝 (deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalLimitField p)) := by
  rw [tendsto_pi_nhds]
  intro q
  simpa only [deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalReadoutField,
    deningerOriginalPrimeGreenZeroDampingCoordinateGraphBoundary, map_smul,
    deningerGammaSixCofinalGraphPhysicalTransport_singularVector,
    deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalLimitField] using
    (tendsto_pi_nhds.mp (tendsto_deningerOriginalPrimeGreenZeroDampingCoordinateField p) q).smul
      tendsto_const_nhds

/-- The completed fixed-reader coordinate is zero exactly on the critical line. -/
theorem deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalLimitField_apply_eq_zero_iff
    (p : Nat.Primes) (q : XiZeroCopy) :
    deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalLimitField p q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerOriginalPrimeGreenZeroDampingCoordinatePhysicalLimitField, smul_eq_zero,
    or_iff_right (deningerOriginalPrimeGreenZeroDampingCoefficientField_apply_ne_zero p q),
    deningerGammaSixFixedSoninPhysicalReceiver_eq_zero_iff]
  constructor <;> intro h <;> linarith

end

end RHTower
