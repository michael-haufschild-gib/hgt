import GaloisForLFunctions.HTGeometry.ExponentZeroEulerGaugeFoliation
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Complex.Cardinality

/-!
# Cardinality and codensity of exponent-zero Euler-gauge leaves

This file completes the set-theoretic part of the exponent-zero Euler-gauge foliation for the
actual prime index set.  Constant prime phases lie in pairwise different gauge classes because the
reciprocal-prime series diverges.  They give the continuum lower bound, while the countable product
description of the prime-phase torus gives the matching upper bound.  A fixed nontrivial constant
twist also supplies, next to every dense class, a disjoint dense class; hence every class is
codense.
-/

namespace GaloisForLFunctions.HTGeometry

open Cardinal Complex Set

noncomputable section

/-- The standard real size of a prime. -/
abbrev natPrimeSize (p : Nat.Primes) : ℝ := p

/-- A phase which is constant on every prime. -/
def constantPrimePhase (theta : Circle) : PrimePhase Nat.Primes := fun _ => theta

@[simp]
theorem constantPrimePhase_apply (theta : Circle) (p : Nat.Primes) :
    constantPrimePhase theta p = theta := rfl

@[simp]
theorem constantPrimePhase_mul (theta phi : Circle) :
    constantPrimePhase (theta * phi) = constantPrimePhase theta * constantPrimePhase phi := rfl

@[simp]
theorem constantPrimePhase_inv (theta : Circle) :
    constantPrimePhase theta⁻¹ = (constantPrimePhase theta)⁻¹ := rfl

/-- At exponent one, the exponent-zero weight is exactly the reciprocal-prime weight. -/
theorem exponentZeroWeight_natPrime_one (p : Nat.Primes) :
    exponentZeroWeight natPrimeSize ⟨1, zero_lt_one⟩ p = 1 / (p : ℝ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  simp [exponentZeroWeight, Real.exp_neg, Real.exp_log hp]

/-- Distinct constant phases have a nonzero relative phase cost. -/
theorem norm_one_sub_circle_inv_mul_ne_zero {theta phi : Circle} (h : theta ≠ phi) :
    ‖1 - (((theta⁻¹ * phi : Circle) : ℂ))‖ ≠ 0 := by
  rw [norm_ne_zero_iff]
  intro hz
  have hrel : theta⁻¹ * phi = 1 :=
    Circle.coe_injective (by simpa using (sub_eq_zero.mp hz).symm)
  exact h (by
    have := congrArg (fun z : Circle => theta * z) hrel
    simpa [mul_assoc] using this.symm)

/-- A nontrivial constant relative phase is not an exponent-zero Euler gauge.

The obstruction is already visible at exponent one, where the gauge cost is a nonzero constant
multiple of the divergent sum of the reciprocals of the primes. -/
theorem not_isExponentZeroEulerGauge_constant_relative {theta phi : Circle}
    (h : theta ≠ phi) :
    ¬ IsExponentZeroEulerGauge natPrimeSize
      ((constantPrimePhase theta)⁻¹ * constantPrimePhase phi) := by
  intro hgauge
  let c : ℝ := ‖1 - (((theta⁻¹ * phi : Circle) : ℂ))‖
  have hc : c ≠ 0 := norm_one_sub_circle_inv_mul_ne_zero h
  have hsigma := hgauge ⟨1, zero_lt_one⟩
  have hscaled : Summable (fun p : Nat.Primes => (1 / (p : ℝ)) * c) := by
    simpa [IsExponentZeroEulerGauge, IsWeightedEulerGauge, constantPrimePhase,
      exponentZeroWeight_natPrime_one, c] using hsigma
  have hunscaled := hscaled.mul_right c⁻¹
  have hreciprocal : Summable (fun p : Nat.Primes => (1 / (p : ℝ))) := by
    convert hunscaled using 1
    funext p
    simp [hc]
  exact Nat.Primes.not_summable_one_div hreciprocal

/-- Constant phases represent pairwise distinct exponent-zero gauge classes. -/
theorem constantPrimePhase_class_injective :
    Function.Injective
      (fun theta : Circle => exponentZeroEulerGaugeClass natPrimeSize (constantPrimePhase theta)) := by
  intro theta phi hclass
  by_contra hne
  rw [exponentZeroEulerGaugeClass_eq_iff] at hclass
  exact not_isExponentZeroEulerGauge_constant_relative hne hclass

/-- The unit circle has cardinality continuum. -/
theorem cardinalMk_circle : #(Circle) = 𝔠 := by
  apply le_antisymm
  · exact (Cardinal.mk_subtype_le _).trans_eq Cardinal.mk_complex
  · rw [← Cardinal.mk_Ico_real (show (0 : ℝ) < 2 * Real.pi by positivity)]
    apply Cardinal.mk_le_of_injective
    intro x y hxy
    apply Subtype.ext
    exact Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) x.2 y.2 hxy

/-- The full prime-phase torus has cardinality continuum. -/
theorem cardinalMk_primePhase_natPrimes : #(PrimePhase Nat.Primes) = 𝔠 := by
  rw [show #(PrimePhase Nat.Primes) = #(Nat.Primes → Circle) by rfl]
  rw [Cardinal.mk_pi, Cardinal.prod_const', cardinalMk_circle,
    Cardinal.mk_eq_aleph0 Nat.Primes, Cardinal.continuum_power_aleph0]

/-- There are exactly continuum-many exponent-zero Euler-gauge orbits. -/
theorem cardinalMk_exponentZeroEulerGaugeQuotient_natPrimes :
    #(exponentZeroEulerGaugeQuotient natPrimeSize) = 𝔠 := by
  apply le_antisymm
  · exact Cardinal.mk_quotient_le.trans_eq cardinalMk_primePhase_natPrimes
  · rw [← cardinalMk_circle]
    exact Cardinal.mk_le_of_injective constantPrimePhase_class_injective

/-- Multiplication by any phase preserves equality of exponent-zero gauge classes. -/
theorem exponentZeroEulerGaugeClass_mul_left_eq_iff (eta x y : PrimePhase Nat.Primes) :
    exponentZeroEulerGaugeClass natPrimeSize (eta * x) =
        exponentZeroEulerGaugeClass natPrimeSize (eta * y) ↔
      exponentZeroEulerGaugeClass natPrimeSize x =
        exponentZeroEulerGaugeClass natPrimeSize y := by
  simp only [exponentZeroEulerGaugeClass_eq_iff]
  have hrel : (eta * x)⁻¹ * (eta * y) = x⁻¹ * y := by
    funext p
    change (eta p * x p)⁻¹ * (eta p * y p) = (x p)⁻¹ * y p
    simp only [mul_inv_rev]
    calc
      (x p)⁻¹ * (eta p)⁻¹ * (eta p * y p) =
          (eta p)⁻¹ * eta p * ((x p)⁻¹ * y p) := by ac_rfl
      _ = (x p)⁻¹ * y p := by simp
  rw [hrel]

/-- Every exponent-zero Euler-gauge orbit is codense as well as dense. -/
theorem exponentZeroEulerGaugeClass_fiber_codense_natPrimes (eta : PrimePhase Nat.Primes) :
    Dense ((exponentZeroEulerGaugeClass natPrimeSize ⁻¹'
      {exponentZeroEulerGaugeClass natPrimeSize eta})ᶜ) := by
  let twist : PrimePhase Nat.Primes := constantPrimePhase (-1)
  have hconst :
      exponentZeroEulerGaugeClass natPrimeSize (constantPrimePhase 1) ≠
        exponentZeroEulerGaugeClass natPrimeSize twist := by
    intro h
    have hcircle : (1 : Circle) = -1 := constantPrimePhase_class_injective h
    have hcoe := congrArg ((↑) : Circle → ℂ) hcircle
    norm_num at hcoe
  have hdistinct :
      exponentZeroEulerGaugeClass natPrimeSize eta ≠
        exponentZeroEulerGaugeClass natPrimeSize (eta * twist) := by
    intro h
    apply hconst
    apply (exponentZeroEulerGaugeClass_mul_left_eq_iff eta (constantPrimePhase 1) twist).mp
    have hone : eta * constantPrimePhase 1 = eta := by
      funext p
      simp [constantPrimePhase]
    rw [hone]
    exact h
  refine (exponentZeroEulerGaugeClass_fiber_dense natPrimeSize (eta * twist)).mono ?_
  intro z hz
  simp only [mem_preimage, mem_singleton_iff] at hz
  simp only [mem_compl_iff, mem_preimage, mem_singleton_iff]
  intro hzeta
  exact hdistinct (hzeta.symm.trans hz)

end

end GaloisForLFunctions.HTGeometry
