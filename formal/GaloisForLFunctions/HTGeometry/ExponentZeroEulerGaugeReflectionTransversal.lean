import GaloisForLFunctions.HTGeometry.MaximalIsodivisorialHTFreeFrame

/-!
# Exponent-zero Euler-gauge reflection transversals

This module packages the exact dense/codense foliation and isolates the analytic strong
multiplicity-one boundary for a completed reflection class.  Once that class is separated under
exponent-zero Euler discrepancies, every gauge orbit meets it in at most one point; an orbit
through a member meets it in exactly that distinguished point.
-/

namespace GaloisForLFunctions.HTGeometry

open Cardinal Set Topology

noncomputable section

/-- The full topological and cardinal geometry of the exponent-zero foliation on the prime-phase
torus. -/
theorem exponentZeroEulerGaugeFoliation_exactGeometry :
    (∀ eta : PrimePhase Nat.Primes,
      Dense (exponentZeroEulerGaugeClass natPrimeSize ⁻¹'
        {exponentZeroEulerGaugeClass natPrimeSize eta}) ∧
      Dense ((exponentZeroEulerGaugeClass natPrimeSize ⁻¹'
        {exponentZeroEulerGaugeClass natPrimeSize eta})ᶜ)) ∧
    TopologicalSpace.coinduced (exponentZeroEulerGaugeClass natPrimeSize)
        inferInstance = ⊤ ∧
    #(exponentZeroEulerGaugeQuotient natPrimeSize) = 𝔠 := by
  refine ⟨?_, exponentZeroEulerGaugeQuotient_coinduced_eq_indiscrete natPrimeSize,
    cardinalMk_exponentZeroEulerGaugeQuotient_natPrimes⟩
  intro eta
  exact ⟨exponentZeroEulerGaugeClass_fiber_dense natPrimeSize eta,
    exponentZeroEulerGaugeClass_fiber_codense_natPrimes eta⟩

/-- Analytic strong multiplicity one, expressed at the exact boundary needed by the transversal
theorem: two members of `R` cannot have an exponent-zero relative Euler discrepancy unless their
prime phases agree.  For a fixed order-one completed Euler class, the paper proof supplies this
property from the common functional equation, Hadamard quotient theorem, normalization at
positive infinity, and Dirichlet coefficient uniqueness. -/
def ExponentZeroGaugeSeparatedReflectionClass
    (R : Set (PrimePhase Nat.Primes)) : Prop :=
  ∀ eta ∈ R, ∀ psi ∈ R,
    IsExponentZeroEulerGauge natPrimeSize (eta⁻¹ * psi) → eta = psi

/-- A gauge-separated completed reflection class is a partial transversal: every exponent-zero
gauge orbit meets it in at most one point. -/
theorem exponentZeroGaugeSeparatedReflectionClass_inter_fiber_subsingleton
    (R : Set (PrimePhase Nat.Primes))
    (hR : ExponentZeroGaugeSeparatedReflectionClass R)
    (q : exponentZeroEulerGaugeQuotient natPrimeSize) :
    (R ∩ exponentZeroEulerGaugeClass natPrimeSize ⁻¹' {q}).Subsingleton := by
  intro eta heta psi hpsi
  apply hR eta heta.1 psi hpsi.1
  exact (exponentZeroEulerGaugeClass_eq_iff natPrimeSize eta psi).mp
    (heta.2.trans hpsi.2.symm)

/-- Pointed form of the rigid transversal: if `eta` belongs to the fixed completed reflection
class, its exponent-zero orbit intersects that class in exactly `{eta}`. -/
theorem exponentZeroGaugeSeparatedReflectionClass_pointed_inter_eq
    (R : Set (PrimePhase Nat.Primes))
    (hR : ExponentZeroGaugeSeparatedReflectionClass R)
    (eta : PrimePhase Nat.Primes) (heta : eta ∈ R) :
    R ∩ exponentZeroEulerGaugeClass natPrimeSize ⁻¹'
        {exponentZeroEulerGaugeClass natPrimeSize eta} = {eta} := by
  apply Set.ext
  intro psi
  constructor
  · intro hpsi
    have hsub := exponentZeroGaugeSeparatedReflectionClass_inter_fiber_subsingleton
      R hR (exponentZeroEulerGaugeClass natPrimeSize eta)
    have heta' : eta ∈ R ∩ exponentZeroEulerGaugeClass natPrimeSize ⁻¹'
        {exponentZeroEulerGaugeClass natPrimeSize eta} :=
      ⟨heta, rfl⟩
    exact Set.mem_singleton_iff.mpr (hsub hpsi heta')
  · intro hpsi
    rw [Set.mem_singleton_iff.mp hpsi]
    exact ⟨heta, rfl⟩

/-- Orbit-level divisor rigidity, included here as the analytic leaf component of the combined
foliation/transversal geometry. -/
theorem exponentZeroEulerGaugeLeaf_completeDivisor_eq
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega)
    (f : ℂ → ℂ) :
    ∀ z ∈ positiveHalfPlane,
      meromorphicOrderAt (exponentZeroGaugeContinuedSource eta omega f) z =
        meromorphicOrderAt f z :=
  exponentZeroGauge_completePositiveHalfPlaneDivisor_eq eta omega homega f

end

end GaloisForLFunctions.HTGeometry
