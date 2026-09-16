import GaloisForLFunctions.RHTower.PrimeHodgeCubicOrbitBirth
import GaloisForLFunctions.RHTower.PrimeLogCubicLaplaceGraphFormation

/-!
# Prime--Hodge cubic critical-Laplace bridge

The PCOB cubic birth is not an independent formal source: at each strictly positive
aperture it is exactly the pre-existing literal prime-log critical-Laplace reporter,
with the scalar forced by the formed Stokes current.  This gives a labelled source
Hilbert representative of the cubic birth before any theta quotient or Xi
specialization.

This module deliberately does not manufacture a theta map, a graph morphism, a
Calderón class, or a divisor evaluation.  It fixes their required input instead:
every candidate must carry this exact all-prime reporter.
-/

open Complex Matrix Filter Topology Set
open scoped Kronecker ComplexOrder BigOperators

namespace RHTower

noncomputable section

/-- Exact square of one literal critical prime-log reporter coordinate. -/
theorem primeLogCriticalLaplaceFeature_sq
    {d : ℝ} (p : Nat.Primes) :
    (primeLogCriticalLaplaceFeature p d) ^ 2 =
      4 * d ^ 2 * Real.log (p : ℝ) ^ 4 / (p : ℝ) *
        (p : ℝ) ^ (-(2 * d)) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hsqrt : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hexp : Real.exp (-(d * Real.log (p : ℝ))) ^ 2 =
      (p : ℝ) ^ (-(2 * d)) := by
    rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [primeLogCriticalLaplaceFeature]
  field_simp [hsqrt]
  rw [Real.sq_sqrt hp.le, hexp]
  ring

/-- Every PCOB cubic birth coordinate is strictly positive before its real embedding. -/
theorem primeHodgeCubicBirthVector_re_pos
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    0 < (primeHodgeCubicBirthVector d p).re := by
  have hJ : 0 < gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d :=
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  have hscale : 0 < routePPrimitiveGammaJuliaStokesApertureScaleSq d p :=
    routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd p
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hvm : 0 < ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, 0)) /
      xiGammaEulerValuationNat (p, 0) := by
    rw [xiGammaEulerValuationNat, vonMangoldt_prime_pow_succ_eq_log]
    norm_num
    exact div_pos hlog (by exact_mod_cast p.property.pos)
  simp only [primeHodgeCubicBirthVector, Complex.ofReal_re]
  positivity

/--
The literal PCOB cubic birth vector is the exact critical-Laplace reporter at the same
aperture.  The coefficient is global and forced by the already formed Stokes current;
no prime-dependent reweighting occurs.
-/
theorem primeHodgeCubicBirthVector_eq_criticalLaplaceFeature
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    primeHodgeCubicBirthVector d p =
      ((Real.sqrt (2 / (d * gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)) : ℝ) : ℂ) *
        primeLogCriticalLaplaceFeatureC p d := by
  have hJ : 0 < gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d :=
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hfeature : 0 < primeLogCriticalLaplaceFeature p d := by
    unfold primeLogCriticalLaplaceFeature
    positivity
  have hcoeff : 0 < Real.sqrt (2 /
      (d * gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)) :=
    Real.sqrt_pos.2 (by positivity)
  have hbirthsq : (primeHodgeCubicBirthVector d p).re ^ 2 =
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d *
          Real.log (p : ℝ) ^ 3 := by
    have hdiag := primeHodgeCubicBirthVector_diagonal hd p
    have hbcast : primeHodgeCubicBirthVector d p =
        ((primeHodgeCubicBirthVector d p).re : ℂ) := rfl
    rw [hbcast] at hdiag
    simp only [Complex.star_def, Complex.conj_ofReal] at hdiag
    norm_cast at hdiag
    simpa [pow_two] using hdiag
  have htargetsq :
      (Real.sqrt (2 / (d * gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)) *
        primeLogCriticalLaplaceFeature p d) ^ 2 =
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d *
          Real.log (p : ℝ) ^ 3 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), primeLogCriticalLaplaceFeature_sq,
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hd p,
      gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm, abs_of_pos hd,
      xiMassPrimeSquareEulerWeight_eq]
    have hpow : (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-(2 * d)) =
        (p : ℝ) ^ (-(1 + 2 * d)) := by
      rw [← Real.rpow_add hp]
      congr 1
      ring
    calc
      2 / (d * gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) *
          (4 * d ^ 2 * Real.log (p : ℝ) ^ 4 / (p : ℝ) *
            (p : ℝ) ^ (-(2 * d))) =
          (8 * d * Real.log (p : ℝ) ^ 4 /
            gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) *
            ((p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-(2 * d))) := by
        field_simp [hd.ne', hJ.ne']
        rw [Real.rpow_neg_one]
        field_simp [hp.ne']
        ring
      _ = (8 * d * Real.log (p : ℝ) ^ 4 /
            gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) *
            (p : ℝ) ^ (-(1 + 2 * d)) := by rw [hpow]
      _ = (8 * d * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d))) /
            gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) *
            Real.log (p : ℝ) ^ 3 := by ring
  have htarget : 0 < Real.sqrt (2 /
      (d * gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)) *
        primeLogCriticalLaplaceFeature p d := mul_pos hcoeff hfeature
  have hre : (primeHodgeCubicBirthVector d p).re =
      Real.sqrt (2 / (d * gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)) *
        primeLogCriticalLaplaceFeature p d := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hbirthsq.trans htargetsq.symm) with h | h
    · exact h
    · have hbirth := primeHodgeCubicBirthVector_re_pos hd p
      nlinarith
  rw [show primeHodgeCubicBirthVector d p =
      ((primeHodgeCubicBirthVector d p).re : ℂ) by rfl,
    primeLogCriticalLaplaceFeatureC]
  exact_mod_cast hre

/--
The PCOB birth, represented in the existing critical source Hilbert chart.  This is an
actual source vector, not a replacement for the unbounded synthesis graph or its theta
quotient.
-/
def primeHodgeCubicBirthCriticalReporter (d : ℝ) (hd : 0 < d) :
    primeLogCriticalSourceL2 :=
  ((Real.sqrt (2 / (d * gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)) : ℝ) : ℂ) •
    primeLogCriticalEvaluationVector d hd

/-- The source-Hilbert representative has exactly the literal PCOB coordinate at each prime. -/
theorem primeHodgeCubicBirthCriticalReporter_apply
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    (primeHodgeCubicBirthCriticalReporter d hd : Nat.Primes → ℂ) p =
      primeHodgeCubicBirthVector d p := by
  rw [primeHodgeCubicBirthCriticalReporter]
  simp only [primeLogCriticalEvaluationVector]
  exact (primeHodgeCubicBirthVector_eq_criticalLaplaceFeature hd p).symm

/-- No literal prime label disappears in the critical source-Hilbert representative. -/
theorem primeHodgeCubicBirthCriticalReporter_apply_ne_zero
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    (primeHodgeCubicBirthCriticalReporter d hd : Nat.Primes → ℂ) p ≠ 0 := by
  rw [primeHodgeCubicBirthCriticalReporter_apply hd p]
  exact primeHodgeCubicBirthVector_ne_zero hd p

end

end RHTower
