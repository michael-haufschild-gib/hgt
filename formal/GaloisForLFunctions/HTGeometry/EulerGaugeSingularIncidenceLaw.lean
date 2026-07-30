import GaloisForLFunctions.HTGeometry.ExponentZeroEulerGaugeReflectionTransversal

/-!
# Singular incidence of exponent-zero Euler-gauge leaves

Exponent-zero Euler-gauge classes are dense in the full prime-phase torus.  This file records two
sharp consequences for source-to-divisor reconstruction.

* Every nonconstant separated readout which is constant on gauge classes is discontinuous at every
  prime phase.
* There is no continuous global choice of one phase representative from every gauge class.

The statements are independent of a particular divisor model.  Analytic divisor preservation
along the classes is supplied by `ExponentZeroIsodivisorialContinuation`; completed functional
equations give rigid partial transversals in
`ExponentZeroEulerGaugeReflectionTransversal`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Topology

noncomputable section

/-- Every nonconstant separated invariant of exponent-zero Euler-gauge classes is nowhere
continuous on the prime-phase torus. -/
theorem nowhereContinuousAt_of_nonconstant_exponentZeroEulerGaugeInvariant
    {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    (F : PrimePhase Nat.Primes → Y)
    (hinvariant : ∀ eta psi,
      exponentZeroEulerGaugeClass natPrimeSize eta =
        exponentZeroEulerGaugeClass natPrimeSize psi →
      F eta = F psi)
    (hnonconstant : ∃ eta psi, F eta ≠ F psi) :
    ∀ eta, ¬ ContinuousAt F eta := by
  obtain ⟨x, y, hxy⟩ := hnonconstant
  intro eta hF
  have hconstant :=
    GaloisForLFunctions.continuousAt_constant_of_dense_fibers
      (exponentZeroEulerGaugeClass natPrimeSize) F eta hF
      (exponentZeroEulerGaugeClass_fiber_dense natPrimeSize)
      hinvariant
  exact hxy ((hconstant x).trans (hconstant y).symm)

/-- A phase-level global gauge selector chooses one representative of every exponent-zero
Euler-gauge class and depends only on the class. -/
def IsExponentZeroEulerGaugeSelector
    (S : PrimePhase Nat.Primes → PrimePhase Nat.Primes) : Prop :=
  (∀ eta,
    exponentZeroEulerGaugeClass natPrimeSize (S eta) =
      exponentZeroEulerGaugeClass natPrimeSize eta) ∧
  (∀ eta psi,
    exponentZeroEulerGaugeClass natPrimeSize eta =
        exponentZeroEulerGaugeClass natPrimeSize psi →
      S eta = S psi)

/-- There is no continuous global choice of one phase representative from every exponent-zero
Euler-gauge class. -/
theorem not_exists_continuous_exponentZeroEulerGaugeSelector :
    ¬ ∃ S : PrimePhase Nat.Primes → PrimePhase Nat.Primes,
      Continuous S ∧ IsExponentZeroEulerGaugeSelector S := by
  rintro ⟨S, hS, hsection, hfactor⟩
  have hconstant :=
    GaloisForLFunctions.continuous_constant_of_dense_fibers
      (exponentZeroEulerGaugeClass natPrimeSize) S hS
      (exponentZeroEulerGaugeClass_fiber_dense natPrimeSize)
      hfactor
  let pos : PrimePhase Nat.Primes := constantPrimePhase 1
  let neg : PrimePhase Nat.Primes := constantPrimePhase (-1)
  have hclass :
      exponentZeroEulerGaugeClass natPrimeSize pos =
        exponentZeroEulerGaugeClass natPrimeSize neg := by
    calc
      exponentZeroEulerGaugeClass natPrimeSize pos =
          exponentZeroEulerGaugeClass natPrimeSize (S pos) :=
        (hsection pos).symm
      _ = exponentZeroEulerGaugeClass natPrimeSize (S neg) := by
        rw [hconstant pos neg]
      _ = exponentZeroEulerGaugeClass natPrimeSize neg :=
        hsection neg
  have hcircle : (1 : Circle) = -1 := constantPrimePhase_class_injective hclass
  have hcoe := congrArg ((↑) : Circle → ℂ) hcircle
  norm_num at hcoe

end

end GaloisForLFunctions.HTGeometry
