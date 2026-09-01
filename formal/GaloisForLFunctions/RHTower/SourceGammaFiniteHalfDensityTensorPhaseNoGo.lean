import GaloisForLFunctions.RHTower.SourceGammaFiniteHalfDensityTensorPowerRadialNoGo
import GaloisForLFunctions.HTGeometry.RealBaseCpowPolar
import GaloisForLFunctions.HTGeometry.WeldClassTable

/-!
# Finite physical half-density tensor phases cannot realize positive source/Gamma naturality

The radial classification leaves degree four as the unique finite tensor power with the exact
Gamma-Ward norm exponent.  This file retains the full complex phase instead of discarding it.
After radial normalization, the degree-`n` literal physical half-density character at prime `p` is

`exp (-i * n * Im(rho) * log p)`.

A positive real archimedean readout, as required by the corpus source-natural Gamma reporter, would
force the normalized phases at primes two and three to be the same positive real.  Unit norm makes
that scalar one.  Integral winding numbers and the corpus two-prime logarithmic independence then
force `n * Im(rho) = 0`.  For positive degree this contradicts the unconditional Xi-support height
gap `1 < |Im(rho)|`.

Thus every positive finite tensor degree fails pointwise on every actual Xi divisor, including the
radially exact degree four.  The surviving source law must be non-tensorial, prime-coupled, or leave
the positive-real archimedean interface.

`[NEW] [SHARED-WARD ROUTE-CLASS NO-GO] [SOURCE-PURE] [LEAN-PROVED]`
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Full complex phase of the degree-`n` literal physical half-density character after removing
its exact radial norm at prime `p`. -/
def ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase
    (p : ℕ) (rho : XiDivisorSupport) (n : ℕ) : ℂ :=
  (((p : ℝ) ^ ((n : ℝ) * (2 * (rho : ℂ).re - 1) / 2) : ℝ) : ℂ) *
    bilateralHalfDensityCharacter p (rho : ℂ) ^ n

/-- Exact polar formula: radial normalization leaves only the ordinate-driven prime phase. -/
theorem ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase_eq_exp
    {p : ℕ} (hp : 0 < p) (rho : XiDivisorSupport) (n : ℕ) :
    ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase p rho n =
      Complex.exp (-Complex.I *
        (((n : ℝ) * (rho : ℂ).im * Real.log (p : ℝ) : ℝ) : ℂ)) := by
  rw [ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase,
    bilateralHalfDensityCharacter]
  change (((p : ℝ) ^ ((n : ℝ) * (2 * (rho : ℂ).re - 1) / 2) : ℝ) : ℂ) *
      (((p : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - (rho : ℂ))) ^ n = _
  rw [
    GaloisForLFunctions.HTGeometry.ofReal_cpow_eq_exp (by exact_mod_cast hp),
    ← Complex.exp_nat_mul,
    Real.rpow_def_of_pos (by exact_mod_cast hp), Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- Radial normalization puts every finite tensor phase on the unit circle. -/
theorem norm_ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase
    {p : ℕ} (hp : 0 < p) (rho : XiDivisorSupport) (n : ℕ) :
    ‖ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase p rho n‖ = 1 := by
  rw [ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase_eq_exp hp,
    Complex.norm_exp]
  have hre : (-Complex.I *
      (((n : ℝ) * (rho : ℂ).im * Real.log (p : ℝ) : ℝ) : ℂ)).re = 0 := by
    rw [Complex.mul_re]
    simp only [Complex.neg_re, Complex.I_re, neg_zero, zero_mul,
      Complex.neg_im, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre, Real.exp_zero]

/-- Candidate finite physical realization of the positive common archimedean readout required by
two-prime source/Gamma naturality. -/
def PrimeGammaTwoThreePositiveArchPhysicalHalfDensityTensorPhase
    (rho : XiDivisorSupport) (n : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase 2 rho n = (c : ℂ) ∧
    ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase 3 rho n = (c : ℂ)

/-- **Pointwise full-phase obstruction.**  No positive finite tensor degree can give one positive
archimedean value at primes two and three for an actual Xi divisor. -/
theorem not_primeGammaTwoThreePositiveArchPhysicalHalfDensityTensorPhase
    (rho : XiDivisorSupport) (n : ℕ) (hn : 0 < n) :
    ¬ PrimeGammaTwoThreePositiveArchPhysicalHalfDensityTensorPhase rho n := by
  rintro ⟨c, hc, htwo, hthree⟩
  have hnorm := congrArg norm htwo
  rw [norm_ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase
      (by norm_num : 0 < 2), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc] at hnorm
  have hc1 : c = 1 := hnorm.symm
  subst c
  have htwoExp : Complex.exp (-Complex.I *
      (((n : ℝ) * (rho : ℂ).im * Real.log (2 : ℝ) : ℝ) : ℂ)) = 1 := by
    simpa using
      (ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase_eq_exp
        (by norm_num : 0 < 2) rho n).symm.trans htwo
  have hthreeExp : Complex.exp (-Complex.I *
      (((n : ℝ) * (rho : ℂ).im * Real.log (3 : ℝ) : ℝ) : ℂ)) = 1 := by
    simpa using
      (ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase_eq_exp
        (by norm_num : 0 < 3) rho n).symm.trans hthree
  obtain ⟨k₂, hk₂⟩ := Complex.exp_eq_one_iff.mp htwoExp
  obtain ⟨k₃, hk₃⟩ := Complex.exp_eq_one_iff.mp hthreeExp
  have hk₂im := congrArg Complex.im hk₂
  simp only [Complex.mul_im, Complex.I_re,
    Complex.ofReal_im, zero_mul, Complex.neg_im, Complex.I_im,
    Complex.ofReal_re, neg_mul, one_mul, Complex.intCast_re,
    Complex.intCast_im, zero_add, add_zero, mul_zero] at hk₂im
  norm_num at hk₂im
  have hk₃im := congrArg Complex.im hk₃
  simp only [Complex.mul_im, Complex.I_re,
    Complex.ofReal_im, zero_mul, Complex.neg_im, Complex.I_im,
    Complex.ofReal_re, neg_mul, one_mul, Complex.intCast_re,
    Complex.intCast_im, zero_add, add_zero, mul_zero] at hk₃im
  norm_num at hk₃im
  have hA : (n : ℝ) * (rho : ℂ).im ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hn.ne'
    · have hgap := xiDivisorSupport_one_lt_abs_im rho
      exact abs_pos.mp (lt_trans zero_lt_one hgap)
  have hcross : ((n : ℝ) * (rho : ℂ).im) *
      ((k₃ : ℝ) * Real.log 2 - (k₂ : ℝ) * Real.log 3) = 0 := by
    calc
      ((n : ℝ) * (rho : ℂ).im) *
          ((k₃ : ℝ) * Real.log 2 - (k₂ : ℝ) * Real.log 3) =
          -(k₃ : ℝ) *
              (-((n : ℝ) * (rho : ℂ).im * Real.log (2 : ℝ))) +
            (k₂ : ℝ) *
              (-((n : ℝ) * (rho : ℂ).im * Real.log (3 : ℝ))) := by ring
      _ = -(k₃ : ℝ) * ((k₂ : ℝ) * (2 * Real.pi)) +
            (k₂ : ℝ) * ((k₃ : ℝ) * (2 * Real.pi)) := by
          rw [hk₂im, hk₃im]
      _ = 0 := by ring
  have hrel0 : (k₃ : ℝ) * Real.log 2 - (k₂ : ℝ) * Real.log 3 = 0 :=
    (mul_eq_zero.mp hcross).resolve_left hA
  have hrel : (k₃ : ℝ) * Real.log 2 + ((-k₂ : ℤ) : ℝ) * Real.log 3 = 0 := by
    push_cast
    linarith
  have hk := GaloisForLFunctions.RHTower.two_prime_log_indep
    (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 3)
    (by norm_num : (2 : ℕ) ≠ 3) k₃ (-k₂) hrel
  have hk₂zero : k₂ = 0 := by omega
  rw [hk₂zero] at hk₂im
  simp only [Int.cast_zero, zero_mul] at hk₂im
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hprod : ((n : ℝ) * (rho : ℂ).im) * Real.log 2 = 0 := by
    linarith
  have : (n : ℝ) * (rho : ℂ).im = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hlog2
  exact hA this

/-- Closed route-class statement over every actual Xi divisor and every positive finite degree. -/
def SharedWardFiniteHalfDensityTensorPhaseRouteKilled : Prop :=
  ∀ (rho : XiDivisorSupport) (n : ℕ), 0 < n →
    ¬ PrimeGammaTwoThreePositiveArchPhysicalHalfDensityTensorPhase rho n

/-- **[SHARED-WARD ROUTE-CLASS KILL].**  Full complex phase eliminates the unique radial survivor:
no positive finite physical tensor character can realize the positive two-prime source-natural
Gamma interface, even at one actual Xi divisor. -/
theorem sharedWardFiniteHalfDensityTensorPhaseRouteKilled :
    SharedWardFiniteHalfDensityTensorPhaseRouteKilled := by
  intro rho n hn
  exact not_primeGammaTwoThreePositiveArchPhysicalHalfDensityTensorPhase rho n hn

end

end RHTower
