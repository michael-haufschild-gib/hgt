import GaloisForLFunctions.RHTower.DeningerGammaSixActualGammaBoundaryLogTransgression
import GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesCalkinPolarHandoff
import GaloisForLFunctions.RHTower.GammaCoorientedPositiveConeNoShorting

/-!
# Cofinal full-grade Gamma-six transport to the fixed Sonin receiver

The fixed-local-grade Gamma-six reflection carrier has nontrivial Wold
holonomy away from neutral grade.  The actual source character, however,
depends on total grade: local grade times valuation depth.  Holding total
grade `g` fixed forces local half-grade `g/(2m)` at depth `m`.

This inverse-depth connection is Wold-flat at every total grade.  Its two
logarithmic branches are constant nonzero multiples of the actual
Gamma-six Wold--Jordan primitive, so their cofaces remain in the same
non-trace-class principal source class.  Genuine equal-depth
Gamma/co-Poisson evaluations reconstruct both branches.

The reflection-odd exterior at every depth has the same frequency
`sinh (g * log 6 / 2)`.  A division-free positive calibration therefore
identifies its literal two-sheet Euler orientation Gram with Route R's
fixed `(2,3)` noncompact Sonin commutator.  Prime labels, valuation depth,
total grade, actual Gamma transport, and the fixed physical receiver all
remain explicit.  No Xi divisor, compactness premise, or RH statement is
used.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Local half-grade forced at depth `m` by fixed total grade `g`. -/
def deningerGammaSixCofinalLocalHalfGrade
    (g : ℝ) (m : MobiusHonestDepth) : ℝ :=
  g / (2 * (m : ℝ))

/-- Reflection multiplier along the fixed-total-grade cofinal section. -/
def deningerGammaSixCofinalFullGradeReflectionMultiplier
    (g : ℝ) (n : ℕ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^
    (g / (deningerGammaSixShellDepth n : ℝ))

/-- The inverse-depth connection removes all Wold-depth dependence from
the reflection multiplier. -/
theorem deningerGammaSixCofinalFullGradeReflectionMultiplier_eq
    (g : ℝ) (n : ℕ) :
    deningerGammaSixCofinalFullGradeReflectionMultiplier g n =
      (1 / 6 : ℝ) ^ g := by
  rw [deningerGammaSixCofinalFullGradeReflectionMultiplier,
    deningerGammaSixShellEigenvalue]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  have hm : (deningerGammaSixShellDepth n : ℝ) ≠ 0 := by
    have hmNat : 0 < deningerGammaSixShellDepth n :=
      lt_of_lt_of_le (by norm_num) (three_le_deningerGammaSixShellDepth n)
    exact_mod_cast hmNat.ne'
  congr 1
  field_simp

/-- **Cofinal full-grade Wold flatness.**  Transporting local grade from
`g/m` to `g/(m+1)` makes the reflection multiplier stationary for every
total grade, without asserting that a fixed local grade is stationary. -/
theorem deningerGammaSixCofinalFullGradeReflectionMultiplier_wold
    (g : ℝ) (n : ℕ) :
    deningerGammaSixCofinalFullGradeReflectionMultiplier g
        (deningerGammaSixWoldCoordinate n) =
      deningerGammaSixCofinalFullGradeReflectionMultiplier g n := by
  rw [deningerGammaSixCofinalFullGradeReflectionMultiplier_eq,
    deningerGammaSixCofinalFullGradeReflectionMultiplier_eq]

/-- Forward logarithmic branch at fixed total grade. -/
def deningerGammaSixCofinalFullGradeForwardLogWeight
    (g : ℝ) (n : ℕ) : ℝ :=
  (deningerGammaSixShellDepth n : ℝ) * Real.log 6 *
    deningerGammaSixShellEigenvalue n ^
      (1 - g / (2 * (deningerGammaSixShellDepth n : ℝ)))

/-- Reflected logarithmic branch at fixed total grade. -/
def deningerGammaSixCofinalFullGradeReflectedLogWeight
    (g : ℝ) (n : ℕ) : ℝ :=
  (deningerGammaSixShellDepth n : ℝ) * Real.log 6 *
    deningerGammaSixShellEigenvalue n ^
      (1 + g / (2 * (deningerGammaSixShellDepth n : ℝ)))

/-- Fixed-total-grade forward branch is a constant multiple of the
critical logarithmic primitive. -/
theorem deningerGammaSixCofinalFullGradeForwardLogWeight_eq
    (g : ℝ) (n : ℕ) :
    deningerGammaSixCofinalFullGradeForwardLogWeight g n =
      (1 / 6 : ℝ) ^ (-g / 2) * deningerGammaSixLogWeight n := by
  have hm : (deningerGammaSixShellDepth n : ℝ) ≠ 0 := by
    have hmNat : 0 < deningerGammaSixShellDepth n :=
      lt_of_lt_of_le (by norm_num) (three_le_deningerGammaSixShellDepth n)
    exact_mod_cast hmNat.ne'
  rw [deningerGammaSixCofinalFullGradeForwardLogWeight,
    deningerGammaSixShellEigenvalue,
    deningerGammaSixLogWeight, deningerGammaSixShellLogWeight]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  rw [show (deningerGammaSixShellDepth n : ℝ) *
      (1 - g / (2 * (deningerGammaSixShellDepth n : ℝ))) =
      -g / 2 + (deningerGammaSixShellDepth n : ℝ) by field_simp; ring]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 6),
    Real.rpow_natCast]
  ring

/-- Fixed-total-grade reflected branch is the inverse constant multiple of
the critical logarithmic primitive. -/
theorem deningerGammaSixCofinalFullGradeReflectedLogWeight_eq
    (g : ℝ) (n : ℕ) :
    deningerGammaSixCofinalFullGradeReflectedLogWeight g n =
      (1 / 6 : ℝ) ^ (g / 2) * deningerGammaSixLogWeight n := by
  have hm : (deningerGammaSixShellDepth n : ℝ) ≠ 0 := by
    have hmNat : 0 < deningerGammaSixShellDepth n :=
      lt_of_lt_of_le (by norm_num) (three_le_deningerGammaSixShellDepth n)
    exact_mod_cast hmNat.ne'
  rw [deningerGammaSixCofinalFullGradeReflectedLogWeight,
    deningerGammaSixShellEigenvalue,
    deningerGammaSixLogWeight, deningerGammaSixShellLogWeight]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  rw [show (deningerGammaSixShellDepth n : ℝ) *
      (1 + g / (2 * (deningerGammaSixShellDepth n : ℝ))) =
      g / 2 + (deningerGammaSixShellDepth n : ℝ) by field_simp; ring]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 6),
    Real.rpow_natCast]
  ring

/-- Forward full-grade logarithmic coface remains the principal Gamma-six
source, with its source-forced constant character. -/
theorem deningerGammaSixCofinalFullGradeForwardLogWeight_wold
    (g : ℝ) (n : ℕ) :
    deningerGammaSixCofinalFullGradeForwardLogWeight g
          (deningerGammaSixWoldCoordinate n) -
        (1 / 6 : ℝ) *
          deningerGammaSixCofinalFullGradeForwardLogWeight g n =
      (1 / 6 : ℝ) ^ (-g / 2) * (Real.log 6 / 6) *
        deningerGammaSixShellEigenvalue n := by
  rw [deningerGammaSixCofinalFullGradeForwardLogWeight_eq,
    deningerGammaSixCofinalFullGradeForwardLogWeight_eq]
  calc
    (1 / 6) ^ (-g / 2) *
          deningerGammaSixLogWeight (deningerGammaSixWoldCoordinate n) -
        1 / 6 * ((1 / 6) ^ (-g / 2) * deningerGammaSixLogWeight n) =
      (1 / 6) ^ (-g / 2) *
        (deningerGammaSixLogWeight (deningerGammaSixWoldCoordinate n) -
          1 / 6 * deningerGammaSixLogWeight n) := by ring
    _ = _ := by rw [deningerGammaSixLogWeight_wold]; ring

/-- Reflected full-grade logarithmic coface remains the same principal
source with inverse character. -/
theorem deningerGammaSixCofinalFullGradeReflectedLogWeight_wold
    (g : ℝ) (n : ℕ) :
    deningerGammaSixCofinalFullGradeReflectedLogWeight g
          (deningerGammaSixWoldCoordinate n) -
        (1 / 6 : ℝ) *
          deningerGammaSixCofinalFullGradeReflectedLogWeight g n =
      (1 / 6 : ℝ) ^ (g / 2) * (Real.log 6 / 6) *
        deningerGammaSixShellEigenvalue n := by
  rw [deningerGammaSixCofinalFullGradeReflectedLogWeight_eq,
    deningerGammaSixCofinalFullGradeReflectedLogWeight_eq]
  calc
    (1 / 6) ^ (g / 2) *
          deningerGammaSixLogWeight (deningerGammaSixWoldCoordinate n) -
        1 / 6 * ((1 / 6) ^ (g / 2) * deningerGammaSixLogWeight n) =
      (1 / 6) ^ (g / 2) *
        (deningerGammaSixLogWeight (deningerGammaSixWoldCoordinate n) -
          1 / 6 * deningerGammaSixLogWeight n) := by ring
    _ = _ := by rw [deningerGammaSixLogWeight_wold]; ring

/-- Signed same-full-grade relation before target scalarization. -/
theorem deningerGammaSixCofinalFullGradeLogWeight_signed_relation
    (g : ℝ) (n : ℕ) :
    (1 / 6 : ℝ) ^ (g / 2) *
        deningerGammaSixCofinalFullGradeForwardLogWeight g n =
      (1 / 6 : ℝ) ^ (-g / 2) *
        deningerGammaSixCofinalFullGradeReflectedLogWeight g n := by
  rw [deningerGammaSixCofinalFullGradeForwardLogWeight_eq,
    deningerGammaSixCofinalFullGradeReflectedLogWeight_eq]
  ring

/-- Actual modular exterior at arbitrary local grade on equally deep
ordered `(2,3)` cells. -/
def deningerGammaSixTwoThreeEqualDepthModularExterior
    (alpha : ℝ) (m : MobiusHonestDepth) : ℝ :=
  xiGammaEulerPrimitiveModularExterior alpha
    ((⟨2, by norm_num⟩ : Nat.Primes), (m : ℕ) - 1)
    ((⟨3, by norm_num⟩ : Nat.Primes), (m : ℕ) - 1)

/-- Total modular rate on depth `m` is `-m log 6`. -/
theorem deningerGammaSixTwoThreeEqualDepthTotalModularRate_eq
    (m : MobiusHonestDepth) :
    xiGammaEulerPrimitiveModularRate
        ((⟨2, by norm_num⟩ : Nat.Primes), (m : ℕ) - 1) +
      xiGammaEulerPrimitiveModularRate
        ((⟨3, by norm_num⟩ : Nat.Primes), (m : ℕ) - 1) =
      -(m : ℝ) * Real.log 6 := by
  have hm : (m : ℕ) - 1 + 1 = (m : ℕ) := by omega
  have hmR : (((m : ℕ) - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast hm
  rw [xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
  simp only [xiGammaEulerBoundaryHalfHeight]
  rw [hmR]
  norm_num
  rw [show (6 : ℝ) = 2 * 3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- Arbitrary-grade actual exterior is critical exterior times the forced
depth character. -/
theorem deningerGammaSixTwoThreeEqualDepthModularExterior_eq
    (alpha : ℝ) (m : MobiusHonestDepth) :
    deningerGammaSixTwoThreeEqualDepthModularExterior alpha m =
      deningerGammaSixTwoThreeEqualDepthCriticalExterior m *
        Real.exp (-(alpha * (m : ℝ) * Real.log 6)) := by
  rw [deningerGammaSixTwoThreeEqualDepthModularExterior,
    deningerGammaSixTwoThreeEqualDepthCriticalExterior,
    xiGammaEulerPrimitiveModularExterior_eq,
    xiGammaEulerPrimitiveModularExterior_eq,
    deningerGammaSixTwoThreeEqualDepthTotalModularRate_eq]
  simp only [zero_mul, Real.exp_zero]
  ring_nf

/-- Reflection-odd actual Gamma exterior along fixed total grade. -/
def deningerGammaSixCofinalFullGradeOddExterior
    (g : ℝ) (m : MobiusHonestDepth) : ℝ :=
  xiGammaEulerPrimitiveReflectionOddExterior
    (deningerGammaSixCofinalLocalHalfGrade g m)
    ((⟨2, by norm_num⟩ : Nat.Primes), (m : ℕ) - 1)
    ((⟨3, by norm_num⟩ : Nat.Primes), (m : ℕ) - 1)

/-- Every labelled depth carries the same fixed-total-grade hyperbolic
frequency. -/
theorem deningerGammaSixCofinalFullGradeOddExterior_eq
    (g : ℝ) (m : MobiusHonestDepth) :
    deningerGammaSixCofinalFullGradeOddExterior g m =
      (m : ℝ) * deningerGammaSixTwoThreeExteriorVolume *
        deningerGammaSixHalfWeight m *
          Real.sinh (g * Real.log 6 / 2) := by
  rw [deningerGammaSixCofinalFullGradeOddExterior,
    xiGammaEulerPrimitiveReflectionOddExterior_eq_sinh,
    deningerGammaSixTwoThreeEqualDepthTotalModularRate_eq]
  rw [deningerGammaSixCofinalLocalHalfGrade]
  have hcritical :=
    deningerGammaSixTwoThreeEqualDepthCriticalExterior_eq m
  rw [deningerGammaSixTwoThreeEqualDepthCriticalExterior,
    xiGammaEulerPrimitiveModularExterior_eq] at hcritical
  simp only [zero_mul, Real.exp_zero, mul_one] at hcritical
  rw [show g / (2 * (m : ℝ)) * (-(m : ℝ) * Real.log 6) =
      -(g * Real.log 6 / 2) by
    have hmposNat : 0 < (m : ℕ) :=
      lt_of_lt_of_le (by norm_num) m.property
    have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hmposNat.ne'
    field_simp [hmne],
    Real.sinh_neg]
  rw [show
    xiGammaEulerPrimitiveBoundaryAmplitude 0
          ((⟨2, by norm_num⟩ : Nat.Primes), (m : ℕ) - 1) *
        xiGammaEulerPrimitiveBoundaryAmplitude 0
          ((⟨3, by norm_num⟩ : Nat.Primes), (m : ℕ) - 1) *
        (xiGammaEulerBoundaryHalfHeight
            (⟨2, by norm_num⟩ : Nat.Primes) ((m : ℕ) - 1) -
          xiGammaEulerBoundaryHalfHeight
            (⟨3, by norm_num⟩ : Nat.Primes) ((m : ℕ) - 1)) =
      -((m : ℝ) * deningerGammaSixTwoThreeExteriorVolume *
        deningerGammaSixHalfWeight m) by linarith]
  ring

/-- Actual oriented common-test boundary evaluation at arbitrary local
grade on the equal-depth canonical Calderon--Witt witness. -/
def deningerGammaSixTwoThreeEqualDepthActualModularBoundary
    (alpha : ℝ) (m : MobiusHonestDepth) : ℂ :=
  let p : Nat.Primes := ⟨2, by norm_num⟩
  let q : Nat.Primes := ⟨3, by norm_num⟩
  let hpq : p ≠ q := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num at hv
  let e := (m : ℕ) - 1
  (deningerCalderonWittGammaBoundaryVectorOrientation q
      (deningerCalderonWittGammaPolarizedVectorTransport alpha
        (deningerCalderonWittCrossPrimeGammaWitness hpq)
        p q e e)).1
    (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, e))

/-- The arbitrary-grade scalar is the genuine Gamma/co-Poisson transport. -/
theorem deningerGammaSixTwoThreeEqualDepthActualModularBoundary_eq
    (alpha : ℝ) (m : MobiusHonestDepth) :
    deningerGammaSixTwoThreeEqualDepthActualModularBoundary alpha m =
      (deningerGammaSixTwoThreeEqualDepthModularExterior alpha m : ℂ) := by
  rw [deningerGammaSixTwoThreeEqualDepthActualModularBoundary]
  rw [
    deningerCalderonWittGammaPolarizedVectorTransport_crossPrime_orientation_eq_coPoisson]
  rw [xiGammaEulerPrimitiveGammaCoPoissonModularExterior_eq]
  rfl

/-- Forward logarithmic weight reconstructed from actual boundary data. -/
def deningerGammaSixCofinalActualForwardLogWeight
    (g : ℝ) (n : ℕ) : ℝ :=
  let m := deningerGammaSixShellHonestDepth n;
  -(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
    deningerGammaSixHalfWeight m *
      (deningerGammaSixTwoThreeEqualDepthActualModularBoundary
        (-deningerGammaSixCofinalLocalHalfGrade g m) m).re

/-- Reflected logarithmic weight reconstructed from actual boundary data. -/
def deningerGammaSixCofinalActualReflectedLogWeight
    (g : ℝ) (n : ℕ) : ℝ :=
  let m := deningerGammaSixShellHonestDepth n;
  -(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
    deningerGammaSixHalfWeight m *
      (deningerGammaSixTwoThreeEqualDepthActualModularBoundary
        (deningerGammaSixCofinalLocalHalfGrade g m) m).re

private theorem exp_halfGrade_eq_rpow (g : ℝ) :
    Real.exp (g * Real.log 6 / 2) = (1 / 6 : ℝ) ^ (-g / 2) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
  rw [show Real.log (1 / 6 : ℝ) = -Real.log 6 by
    rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by norm_num, Real.log_inv]]
  congr 1
  ring

private theorem exp_neg_halfGrade_eq_rpow (g : ℝ) :
    Real.exp (-(g * Real.log 6 / 2)) = (1 / 6 : ℝ) ^ (g / 2) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
  rw [show Real.log (1 / 6 : ℝ) = -Real.log 6 by
    rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by norm_num, Real.log_inv]]
  congr 1
  ring

/-- Actual Gamma boundary reconstruction equals the forward full-grade
logarithmic branch. -/
theorem deningerGammaSixCofinalActualForwardLogWeight_eq
    (g : ℝ) (n : ℕ) :
    deningerGammaSixCofinalActualForwardLogWeight g n =
      deningerGammaSixCofinalFullGradeForwardLogWeight g n := by
  let m := deningerGammaSixShellHonestDepth n
  have hmne : (m : ℝ) ≠ 0 := by
    have hmposNat : 0 < (m : ℕ) :=
      lt_of_lt_of_le (by norm_num) m.property
    exact_mod_cast hmposNat.ne'
  rw [deningerGammaSixCofinalActualForwardLogWeight]
  change -(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
      deningerGammaSixHalfWeight m *
        (deningerGammaSixTwoThreeEqualDepthActualModularBoundary
          (-deningerGammaSixCofinalLocalHalfGrade g m) m).re = _
  rw [deningerGammaSixTwoThreeEqualDepthActualModularBoundary_eq]
  norm_num only [Complex.ofReal_re]
  rw [deningerGammaSixTwoThreeEqualDepthModularExterior_eq]
  rw [show -(-deningerGammaSixCofinalLocalHalfGrade g m *
        (m : ℝ) * Real.log 6) = g * Real.log 6 / 2 by
    rw [deningerGammaSixCofinalLocalHalfGrade]
    field_simp [hmne]]
  rw [exp_halfGrade_eq_rpow]
  calc
    -(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
          deningerGammaSixHalfWeight m *
          (deningerGammaSixTwoThreeEqualDepthCriticalExterior m *
            (1 / 6 : ℝ) ^ (-g / 2)) =
        (-(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
          deningerGammaSixHalfWeight m *
          deningerGammaSixTwoThreeEqualDepthCriticalExterior m) *
            (1 / 6 : ℝ) ^ (-g / 2) := by ring
    _ = deningerGammaSixShellLogWeight (m : ℕ) *
          (1 / 6 : ℝ) ^ (-g / 2) := by
      rw [deningerGammaSixShellLogWeight_eq_gammaBoundary]
    _ = deningerGammaSixCofinalFullGradeForwardLogWeight g n := by
      rw [deningerGammaSixCofinalFullGradeForwardLogWeight_eq,
        deningerGammaSixLogWeight]
      dsimp [m]
      ring

/-- Actual Gamma boundary reconstruction equals the reflected full-grade
logarithmic branch. -/
theorem deningerGammaSixCofinalActualReflectedLogWeight_eq
    (g : ℝ) (n : ℕ) :
    deningerGammaSixCofinalActualReflectedLogWeight g n =
      deningerGammaSixCofinalFullGradeReflectedLogWeight g n := by
  let m := deningerGammaSixShellHonestDepth n
  have hmne : (m : ℝ) ≠ 0 := by
    have hmposNat : 0 < (m : ℕ) :=
      lt_of_lt_of_le (by norm_num) m.property
    exact_mod_cast hmposNat.ne'
  rw [deningerGammaSixCofinalActualReflectedLogWeight]
  change -(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
      deningerGammaSixHalfWeight m *
        (deningerGammaSixTwoThreeEqualDepthActualModularBoundary
          (deningerGammaSixCofinalLocalHalfGrade g m) m).re = _
  rw [deningerGammaSixTwoThreeEqualDepthActualModularBoundary_eq]
  norm_num only [Complex.ofReal_re]
  rw [deningerGammaSixTwoThreeEqualDepthModularExterior_eq]
  rw [show -(deningerGammaSixCofinalLocalHalfGrade g m *
        (m : ℝ) * Real.log 6) = -(g * Real.log 6 / 2) by
    rw [deningerGammaSixCofinalLocalHalfGrade]
    field_simp [hmne]]
  rw [exp_neg_halfGrade_eq_rpow]
  calc
    -(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
          deningerGammaSixHalfWeight m *
          (deningerGammaSixTwoThreeEqualDepthCriticalExterior m *
            (1 / 6 : ℝ) ^ (g / 2)) =
        (-(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
          deningerGammaSixHalfWeight m *
          deningerGammaSixTwoThreeEqualDepthCriticalExterior m) *
            (1 / 6 : ℝ) ^ (g / 2) := by ring
    _ = deningerGammaSixShellLogWeight (m : ℕ) *
          (1 / 6 : ℝ) ^ (g / 2) := by
      rw [deningerGammaSixShellLogWeight_eq_gammaBoundary]
    _ = deningerGammaSixCofinalFullGradeReflectedLogWeight g n := by
      rw [deningerGammaSixCofinalFullGradeReflectedLogWeight_eq,
        deningerGammaSixLogWeight]
      dsimp [m]
      ring

/-- Positive depth calibration between actual Gamma exterior and the fixed
Sonin receiver. -/
def deningerGammaSixCofinalGammaSoninCalibration
    (m : MobiusHonestDepth) : ℝ :=
  (m : ℝ) * deningerGammaSixTwoThreeExteriorVolume *
    deningerGammaSixHalfWeight m / 2

theorem deningerGammaSixCofinalGammaSoninCalibration_pos
    (m : MobiusHonestDepth) :
    0 < deningerGammaSixCofinalGammaSoninCalibration m := by
  rw [deningerGammaSixCofinalGammaSoninCalibration]
  have hmposNat : 0 < (m : ℕ) :=
    lt_of_lt_of_le (by norm_num) m.property
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast hmposNat
  exact div_pos
    (mul_pos (mul_pos hmpos deningerGammaSixTwoThreeExteriorVolume_pos)
      (deningerGammaSixHalfWeight_pos m)) (by norm_num)

/-- **Division-free actual Gamma-to-Sonin scalar transport.**  Every depth
has the same fixed Sonin frequency; only the positive source calibration
varies. -/
theorem deningerGammaSixCofinalFullGradeOddExterior_sonin
    (g : ℝ) (m : MobiusHonestDepth) :
    routeRCrossPrimeStokesGauge 2 3 g *
        deningerGammaSixCofinalFullGradeOddExterior g m =
      -deningerGammaSixCofinalGammaSoninCalibration m *
        routeRCrossPrimeStokesOddCurvature 2 3 g := by
  rw [deningerGammaSixCofinalFullGradeOddExterior_eq,
    routeRCrossPrimeStokesOddCurvature_eq,
    routeRCrossPrimeStokesPhase_eq_log_mul
      (by norm_num) (by norm_num)]
  norm_num only [Nat.cast_ofNat]
  unfold deningerGammaSixCofinalGammaSoninCalibration
  ring

/-- Genuine reflected two-sheet Gamma packet at fixed total grade. -/
def deningerGammaSixCofinalFullGradeGammaPacket
    (g : ℝ) (m : MobiusHonestDepth) : Fin 2 → ℂ :=
  ![(deningerGammaSixTwoThreeEqualDepthModularExterior
      (deningerGammaSixCofinalLocalHalfGrade g m) m : ℂ),
    (deningerGammaSixTwoThreeEqualDepthModularExterior
      (-deningerGammaSixCofinalLocalHalfGrade g m) m : ℂ)]

theorem deningerGammaSixCofinalFullGradeGammaPacket_difference
    (g : ℝ) (m : MobiusHonestDepth) :
    deningerGammaSixCofinalFullGradeGammaPacket g m 0 -
        deningerGammaSixCofinalFullGradeGammaPacket g m 1 =
      (2 * deningerGammaSixCofinalFullGradeOddExterior g m : ℝ) := by
  simp only [deningerGammaSixCofinalFullGradeGammaPacket,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [deningerGammaSixCofinalFullGradeOddExterior,
    xiGammaEulerPrimitiveReflectionOddExterior]
  unfold deningerGammaSixTwoThreeEqualDepthModularExterior
  push_cast
  ring

/-- Division-free equality of the full two-sheet orientation matrices. -/
theorem deningerGammaSixCofinalFullGradeGamma_orientationMatrix
    (g : ℝ) (m : MobiusHonestDepth) :
    (routeRCrossPrimeStokesGauge 2 3 g : ℂ) •
        finiteEulerOrientationMatrix
          (deningerGammaSixCofinalFullGradeGammaPacket g m) =
      ((-2 * deningerGammaSixCofinalGammaSoninCalibration m : ℝ) : ℂ) •
        finiteEulerOrientationMatrix
          (routeRTwoThreeStokesCurvaturePacket g) := by
  have hscalar :=
    deningerGammaSixCofinalFullGradeOddExterior_sonin g m
  have hcomplex :
      ((routeRCrossPrimeStokesGauge 2 3 g : ℝ) : ℂ) *
          ((2 * deningerGammaSixCofinalFullGradeOddExterior g m : ℝ) : ℂ) =
        (((-2 * deningerGammaSixCofinalGammaSoninCalibration m : ℝ) : ℂ)) *
          (routeRCrossPrimeStokesOddCurvature 2 3 g : ℂ) := by
    exact_mod_cast (show
      routeRCrossPrimeStokesGauge 2 3 g *
          (2 * deningerGammaSixCofinalFullGradeOddExterior g m) =
        (-2 * deningerGammaSixCofinalGammaSoninCalibration m) *
          routeRCrossPrimeStokesOddCurvature 2 3 g by linarith)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [finiteEulerOrientationMatrix]
  · simpa [finiteEulerOrientationMatrix,
      deningerGammaSixCofinalFullGradeGammaPacket_difference,
      routeRTwoThreeStokesCurvaturePacket,
      routeRCrossPrimeStokesOddCurvature] using hcomplex
  · change
      (routeRCrossPrimeStokesGauge 2 3 g : ℂ) *
          (deningerGammaSixCofinalFullGradeGammaPacket g m 1 -
            deningerGammaSixCofinalFullGradeGammaPacket g m 0) =
        ((-2 * deningerGammaSixCofinalGammaSoninCalibration m : ℝ) : ℂ) *
          (routeRTwoThreeStokesCurvaturePacket g 1 -
            routeRTwoThreeStokesCurvaturePacket g 0)
    rw [show
      deningerGammaSixCofinalFullGradeGammaPacket g m 1 -
          deningerGammaSixCofinalFullGradeGammaPacket g m 0 =
        -((2 * deningerGammaSixCofinalFullGradeOddExterior g m : ℝ) : ℂ) by
      rw [← deningerGammaSixCofinalFullGradeGammaPacket_difference]
      ring]
    rw [show routeRTwoThreeStokesCurvaturePacket g 1 -
          routeRTwoThreeStokesCurvaturePacket g 0 =
        -(routeRCrossPrimeStokesOddCurvature 2 3 g : ℂ) by
      simp [routeRTwoThreeStokesCurvaturePacket,
        routeRCrossPrimeStokesOddCurvature]]
    rw [show
      (routeRCrossPrimeStokesGauge 2 3 g : ℂ) *
          -((2 * deningerGammaSixCofinalFullGradeOddExterior g m : ℝ) : ℂ) =
        -((routeRCrossPrimeStokesGauge 2 3 g : ℂ) *
          ((2 * deningerGammaSixCofinalFullGradeOddExterior g m : ℝ) : ℂ))
      by ring,
      hcomplex]
    ring
  · simp [finiteEulerOrientationMatrix]

/-- Division-free equality of the literal Gamma and fixed Sonin orientation
Grams. -/
theorem deningerGammaSixCofinalFullGradeGamma_orientationGram
    (A g : ℝ) (m : MobiusHonestDepth) :
    (routeRCrossPrimeStokesGauge 2 3 g : ℂ) •
        finiteArchimedeanEulerOrientationGram A
          (fun i ↦ (primeTwoThreePacket i : ℝ))
          (deningerGammaSixCofinalFullGradeGammaPacket g m) =
      ((-2 * deningerGammaSixCofinalGammaSoninCalibration m : ℝ) : ℂ) •
        finiteArchimedeanEulerOrientationGram A
          (fun i ↦ (primeTwoThreePacket i : ℝ))
          (routeRTwoThreeStokesCurvaturePacket g) := by
  classical
  rw [finiteArchimedeanEulerOrientationGram,
    finiteArchimedeanEulerOrientationGram]
  unfold finiteArchimedeanPrimeEulerGramCombination
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_smul, smul_smul]
  congr 1
  exact congrFun
    (congrFun
      (deningerGammaSixCofinalFullGradeGamma_orientationMatrix g m) i) j

/-- **Actual Gamma-to-fixed-Sonin operator transport.**  Every depth-labelled
Gamma packet represents the same fixed noncompact Sonin commutator after
its strictly positive source calibration. -/
theorem deningerGammaSixCofinalFullGradeGamma_orientationGram_eq_soninCommutator
    (A g : ℝ) (m : MobiusHonestDepth) :
    (routeRCrossPrimeStokesGauge 2 3 g : ℂ) •
        finiteArchimedeanEulerOrientationGram A
          (fun i ↦ (primeTwoThreePacket i : ℝ))
          (deningerGammaSixCofinalFullGradeGammaPacket g m) =
      ((2 * deningerGammaSixCofinalGammaSoninCalibration m : ℝ) : ℂ) •
        routeRTwoThreeStokesSoninCommutator A g := by
  rw [deningerGammaSixCofinalFullGradeGamma_orientationGram,
    routeRTwoThreeStokesSoninCommutator_eq_neg_orientationGram]
  module

end

end RHTower
