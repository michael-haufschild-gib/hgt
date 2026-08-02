import GaloisForLFunctions.RHTower.DeningerCalderonWittSingularGammaTransgression
import GaloisForLFunctions.RHTower.RiemannDerivedPolarizationLaw
import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw

/-!
# Singular Green--Hodge admission law for the Riemann boundary

Finite Gamma/co-Poisson transport is already a lossless grading action on
the Calderón--Witt Green source.  Reflection introduces one reciprocal
sewing cocycle.  Its displacement is the Riemann boundary fracture

`2 * (re rho - 1 / 2)`.

This file identifies the exact unitary locus of that cocycle.  On every
canonical cross-prime secondary Green boundary:

* the two reflected sewing costs multiply to one;
* the boundary is Hodge-admitted exactly when the fracture vanishes;
* positive fracture forces sewing growth beyond every finite Rees order;
* global admission is equivalent to boundary-character neutrality and RH.

Thus the unresolved issue is not existence of a local transport.  It is the
single global assertion that the divisor-indexed secondary Green boundary is
admitted by the source Hodge polarization.
-/

namespace RHTower

open Complex

noncomputable section

/--
Reflection sewing is reciprocal before any scalar orientation: reversing
the modular displacement inverts the exact source sewing cost.
-/
theorem deningerCalderonWittGammaReflectionSewingCost_mul_reflection
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaReflectionSewingCost a p q n *
        deningerCalderonWittGammaReflectionSewingCost (-a) p q n =
      1 := by
  rw [deningerCalderonWittGammaReflectionSewingCost_eq_exp,
    deningerCalderonWittGammaReflectionSewingCost_eq_exp,
    ← Real.exp_add]
  have hzero :
      (2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))) *
            ((n : ℝ) + 1) +
          (2 * -a * (Real.log (p : ℝ) + Real.log (q : ℝ))) *
            ((n : ℝ) + 1) =
        0 := by
    ring
  rw [hzero, Real.exp_zero]

/-- Zero displacement is the unique constant unit sewing phase. -/
theorem deningerCalderonWittGammaReflectionSewingCost_zero
    (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaReflectionSewingCost 0 p q n = 1 := by
  rw [deningerCalderonWittGammaReflectionSewingCost_eq_exp]
  simp

/--
**Pointwise singular Green--Hodge admission law.**  A canonical cross-prime
secondary Green boundary is admitted at the Riemann fracture exactly on the
critical line.
-/
theorem
    deningerCalderonWittCrossPrimeGammaWitness_mem_boundaryFractureSector_iff
    {p q : Nat.Primes} (hpq : p ≠ q)
    (rho : ℂ) (n : ℕ) :
    deningerCalderonWittCrossPrimeGammaWitness hpq ∈
        deningerCalderonWittGammaAdmittedHodgeSector
          (xiNearbyPoleDualityAdjunctionFracture rho).re ↔
      rho.re = 1 / 2 := by
  rw [
    deningerCalderonWittCrossPrimeGammaWitness_mem_admittedHodgeSector_sameDepth_iff
      hpq (xiNearbyPoleDualityAdjunctionFracture rho).re n,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp
  constructor <;> intro h <;> linarith

/--
At a Riemann boundary point the exact sewing cost has centered exponent
`4 (re rho - 1/2) (log p + log q) (n+1)`.
-/
theorem
    deningerCalderonWittGammaReflectionSewingCost_boundaryFracture_eq_exp
    (rho : ℂ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaReflectionSewingCost
        (xiNearbyPoleDualityAdjunctionFracture rho).re p q n =
      Real.exp
        ((4 * (rho.re - 1 / 2) *
            (Real.log (p : ℝ) + Real.log (q : ℝ))) *
          ((n : ℝ) + 1)) := by
  rw [deningerCalderonWittGammaReflectionSewingCost_eq_exp]
  have hfracture :
      (xiNearbyPoleDualityAdjunctionFracture rho).re =
        2 * (rho.re - 1 / 2) := by
    rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
    simp
  apply congrArg Real.exp
  rw [hfracture]
  ring

/--
Every right-of-line Riemann fracture produces an exact source sewing cost
which dominates every finite Rees order.
-/
theorem
    deningerCalderonWittGammaReflectionSewingCost_boundaryFracture_exceeds_every_finiteReesOrder
    {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (p q : Nat.Primes) :
    ∀ K : ℕ,
      (fun n : ℕ => ((n : ℝ) + 1) ^ K) =o[Filter.atTop]
        fun n : ℕ =>
          deningerCalderonWittGammaReflectionSewingCost
            (xiNearbyPoleDualityAdjunctionFracture rho).re p q n := by
  apply
    deningerCalderonWittGammaReflectionSewingCost_exceeds_every_finiteReesOrder
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp
  linarith

/--
Global admission of one fixed nontrivial cross-prime secondary Green
boundary across the Xi divisor.
-/
def XiCanonicalSecondaryGreenHodgeAdmitted
    {p q : Nat.Primes} (hpq : p ≠ q) : Prop :=
  ∀ rho : XiDivisorSupport,
    deningerCalderonWittCrossPrimeGammaWitness hpq ∈
      deningerCalderonWittGammaAdmittedHodgeSector
        (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)).re

/--
Global source Hodge admission is exactly neutrality of the already
identified boundary character.
-/
theorem xiCanonicalSecondaryGreenHodgeAdmitted_iff_boundaryCharacterNeutral
    {p q : Nat.Primes} (hpq : p ≠ q) :
    XiCanonicalSecondaryGreenHodgeAdmitted hpq ↔
      XiBoundaryCharacterNeutral := by
  constructor
  · intro hadmit rho
    apply
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).2
    exact
      (deningerCalderonWittCrossPrimeGammaWitness_mem_boundaryFractureSector_iff
        hpq (rho : ℂ) 0).1 (hadmit rho)
  · intro hneutral rho
    apply
      (deningerCalderonWittCrossPrimeGammaWitness_mem_boundaryFractureSector_iff
        hpq (rho : ℂ) 0).2
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).1 (hneutral rho)

/--
**Global singular Green--Hodge law.**  Admission of any one canonical
cross-prime secondary Green boundary at every Xi divisor fibre is equivalent
to RH.
-/
theorem xiCanonicalSecondaryGreenHodgeAdmitted_iff_riemannHypothesis
    {p q : Nat.Primes} (hpq : p ≠ q) :
    XiCanonicalSecondaryGreenHodgeAdmitted hpq ↔
      RiemannHypothesis := by
  rw [xiCanonicalSecondaryGreenHodgeAdmitted_iff_boundaryCharacterNeutral,
    xiBoundaryCharacterNeutral_iff_riemannHypothesis]

end

end RHTower
