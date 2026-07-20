import GaloisForLFunctions.RHTower.GammaSewnApertureExteriorHeight
import GaloisForLFunctions.RHTower.VonMangoldtGammaConormalEulerBoundary

/-!
# Euler calibration of the Gamma-sewn exterior height current

The Gamma-sewn Rees boundary sees the midpoint clock

`H_Gamma(p,e) = (e + 1/2) log p`,

whereas the literal phase of the existing von Mangoldt--Gamma Euler boundary feature sees

`H_Euler(p,e) = (1/2) log(p^(e+1)) = ((e+1)/2) log p`.

These clocks are not equal.  Their unique affine calibration is

`H_Euler(p,e) = (1/2) H_Gamma(p,e) + (1/4) log p`.

Consequently the raw Gamma-sewn exterior current cannot be identified directly with the physical
Euler boundary current: it is twice the Euler current on one prime tower and misses a forced
quarter-prime-log seam across different towers.  This module constructs the uniquely calibrated
current, proves that it is exactly the exterior phase current of the literal Euler feature, and
records the source-amplitude recovery without asserting that recovery is a bounded ambient
operator.

No Xi zero, target-selected coefficient, or RH-equivalent positivity assumption occurs here.
-/

namespace RHTower

noncomputable section

/-- Physical half-height in the phase of one von Mangoldt--Gamma Euler boundary cell. -/
def xiGammaEulerBoundaryHalfHeight (p : Nat.Primes) (e : ℕ) : ℝ :=
  (((e : ℝ) + 1) / 2) * Real.log (p : ℝ)

/-- The cell half-height is literally one half of the logarithm of its prime power. -/
theorem xiGammaEulerBoundaryHalfHeight_eq_half_log_valuation
    (p : Nat.Primes) (e : ℕ) :
    xiGammaEulerBoundaryHalfHeight p e =
      Real.log (xiGammaEulerValuationNat (p, e) : ℝ) / 2 := by
  have hlog : Real.log ((((p : ℕ) ^ (e + 1) : ℕ) : ℝ)) =
      ((e + 1 : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
    rw [show (((p : ℕ) ^ (e + 1) : ℕ) : ℝ) =
        ((p : ℕ) : ℝ) ^ (e + 1) by norm_num, Real.log_pow]
  rw [xiGammaEulerBoundaryHalfHeight, xiGammaEulerValuationNat, hlog]
  push_cast
  ring

/-- **Forced half-plus-quarter calibration.**  The physical Euler half-height is one half of the
Gamma-sewn midpoint height plus one quarter of the prime logarithm. -/
theorem xiGammaEulerBoundaryHalfHeight_eq_half_midHeight_add_quarter_primeLog
    (p : Nat.Primes) (e : ℕ) :
    xiGammaEulerBoundaryHalfHeight p e =
      (1 / 2 : ℝ) * gammaSewnMobiusApertureCellMidHeight p e +
        (1 / 4 : ℝ) * Real.log (p : ℝ) := by
  unfold xiGammaEulerBoundaryHalfHeight gammaSewnMobiusApertureCellMidHeight
  ring

/-- The affine calibration coefficients are already uniquely forced by valuation depths zero and
one.  Thus the half-scaling and quarter-prime seam are not adjustable normalizations. -/
theorem xiGammaEulerBoundaryHalfHeight_affineCalibration_unique
    {a b : ℝ}
    (hzero : a * (0 + 1 / 2 : ℝ) + b = (0 + 1 : ℝ) / 2)
    (hone : a * (1 + 1 / 2 : ℝ) + b = (1 + 1 : ℝ) / 2) :
    a = 1 / 2 ∧ b = 1 / 4 := by
  constructor <;> norm_num at hzero hone ⊢ <;> linarith

/-- Real amplitude of the literal von Mangoldt--Gamma height boundary feature. -/
def xiGammaEulerBoundaryRealAmplitude
    (u : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  let n := xiGammaEulerValuationNat pe
  Real.sqrt
    (Real.log pe.1 / (n : ℝ) * Real.exp (-u * Real.log n))

theorem xiGammaEulerBoundaryRealAmplitude_pos
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    0 < xiGammaEulerBoundaryRealAmplitude u pe := by
  have hpLog : 0 < Real.log (pe.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  have hnNat : 0 < xiGammaEulerValuationNat pe := by
    unfold xiGammaEulerValuationNat
    exact Nat.pow_pos (Nat.Prime.pos pe.1.property)
  have hn : (0 : ℝ) < xiGammaEulerValuationNat pe := by
    exact_mod_cast hnNat
  unfold xiGammaEulerBoundaryRealAmplitude
  exact Real.sqrt_pos.2
    (mul_pos (div_pos hpLog hn) (Real.exp_pos _))

/-- At zero phase the existing complex Euler feature is exactly the real source amplitude. -/
theorem xiGammaEulerHeightBoundaryFeature_zero_eq_realAmplitude
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerHeightBoundaryFeature u 0 pe =
      (xiGammaEulerBoundaryRealAmplitude u pe : ℂ) := by
  simp [xiGammaEulerHeightBoundaryFeature,
    xiGammaEulerBoundaryRealAmplitude]

/-- Unique cellwise amplitude recovery from the Gamma-sewn Rees symbol to the literal Euler
boundary amplitude.  This is an identity of source coordinates, not a boundedness assertion. -/
def gammaSewnToXiGammaEulerBoundaryRecovery
    (u : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerBoundaryRealAmplitude u pe /
    gammaSewnMobiusApertureBoundaryAmplitude pe.1

theorem gammaSewnToXiGammaEulerBoundaryRecovery_mul_boundaryAmplitude
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    gammaSewnToXiGammaEulerBoundaryRecovery u pe *
        gammaSewnMobiusApertureBoundaryAmplitude pe.1 =
      xiGammaEulerBoundaryRealAmplitude u pe := by
  unfold gammaSewnToXiGammaEulerBoundaryRecovery
  exact div_mul_cancel₀ _
    (gammaSewnMobiusApertureBoundaryAmplitude_pos pe.1).ne'

/-- Gamma-sewn boundary exterior current after recovering the literal Euler amplitudes on its two
legs, while retaining the Gamma midpoint clock. -/
def gammaSewnRecoveredEulerAmplitudeExteriorCell
    (u : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  gammaSewnToXiGammaEulerBoundaryRecovery u i *
    gammaSewnToXiGammaEulerBoundaryRecovery u j *
      gammaSewnMobiusApertureBoundaryExteriorCell i j

/-- Recovery changes only the two amplitudes; it leaves the midpoint-height difference visible. -/
theorem gammaSewnRecoveredEulerAmplitudeExteriorCell_eq
    (u : ℝ) (i j : Nat.Primes × ℕ) :
    gammaSewnRecoveredEulerAmplitudeExteriorCell u i j =
      xiGammaEulerBoundaryRealAmplitude u i *
        xiGammaEulerBoundaryRealAmplitude u j *
          (gammaSewnMobiusApertureCellMidHeight i.1 i.2 -
            gammaSewnMobiusApertureCellMidHeight j.1 j.2) := by
  have hi := gammaSewnMobiusApertureBoundaryAmplitude_pos i.1
  have hj := gammaSewnMobiusApertureBoundaryAmplitude_pos j.1
  unfold gammaSewnRecoveredEulerAmplitudeExteriorCell
    gammaSewnToXiGammaEulerBoundaryRecovery
    gammaSewnMobiusApertureBoundaryExteriorCell
  field_simp [hi.ne', hj.ne']

/-- The forced prime-log exterior seam between two recovered Euler-amplitude cells. -/
def xiGammaEulerPrimeLogExteriorSeam
    (u : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerBoundaryRealAmplitude u i *
    xiGammaEulerBoundaryRealAmplitude u j *
      (Real.log (i.1 : ℝ) - Real.log (j.1 : ℝ))

/-- Literal real exterior phase current of the von Mangoldt--Gamma Euler boundary feature. -/
def xiGammaEulerBoundaryExteriorCell
    (u : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerBoundaryRealAmplitude u i *
    xiGammaEulerBoundaryRealAmplitude u j *
      (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
        xiGammaEulerBoundaryHalfHeight j.1 j.2)

/-- The source-forced calibrated Gamma-sewn current. -/
def gammaSewnEulerCalibratedBoundaryExteriorCell
    (u : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  (1 / 2 : ℝ) * gammaSewnRecoveredEulerAmplitudeExteriorCell u i j +
    (1 / 4 : ℝ) * xiGammaEulerPrimeLogExteriorSeam u i j

/-- **Exact Euler calibration theorem.**  Half of the recovered Gamma midpoint current plus the
quarter-prime-log seam is exactly the literal Euler boundary exterior current on arbitrary
prime-power cells. -/
theorem gammaSewnEulerCalibratedBoundaryExteriorCell_eq_eulerBoundaryExterior
    (u : ℝ) (i j : Nat.Primes × ℕ) :
    gammaSewnEulerCalibratedBoundaryExteriorCell u i j =
      xiGammaEulerBoundaryExteriorCell u i j := by
  rw [gammaSewnEulerCalibratedBoundaryExteriorCell,
    gammaSewnRecoveredEulerAmplitudeExteriorCell_eq]
  unfold xiGammaEulerPrimeLogExteriorSeam
    xiGammaEulerBoundaryExteriorCell
  rw [xiGammaEulerBoundaryHalfHeight_eq_half_midHeight_add_quarter_primeLog,
    xiGammaEulerBoundaryHalfHeight_eq_half_midHeight_add_quarter_primeLog]
  ring

/-- On one prime tower the seam vanishes, so the recovered Gamma current is exactly twice the
literal Euler current.  This is the sharp factor-two obstruction to uncalibrated transfer. -/
theorem two_mul_xiGammaEulerBoundaryExteriorCell_samePrime_eq_recoveredGamma
    (u : ℝ) (p : Nat.Primes) (e f : ℕ) :
    2 * xiGammaEulerBoundaryExteriorCell u (p, e) (p, f) =
      gammaSewnRecoveredEulerAmplitudeExteriorCell u (p, e) (p, f) := by
  have hcal := gammaSewnEulerCalibratedBoundaryExteriorCell_eq_eulerBoundaryExterior
    u (p, e) (p, f)
  unfold gammaSewnEulerCalibratedBoundaryExteriorCell
    xiGammaEulerPrimeLogExteriorSeam at hcal
  norm_num at hcal
  linarith

@[simp] theorem xiGammaEulerBoundaryExteriorCell_self
    (u : ℝ) (i : Nat.Primes × ℕ) :
    xiGammaEulerBoundaryExteriorCell u i i = 0 := by
  simp [xiGammaEulerBoundaryExteriorCell]

theorem xiGammaEulerBoundaryExteriorCell_swap
    (u : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerBoundaryExteriorCell u j i =
      -xiGammaEulerBoundaryExteriorCell u i j := by
  unfold xiGammaEulerBoundaryExteriorCell
  ring

/-- Phase velocity of the literal Euler boundary feature. -/
def xiGammaEulerBoundaryPhaseVelocity (pe : Nat.Primes × ℕ) : ℂ :=
  -(xiGammaEulerBoundaryHalfHeight pe.1 pe.2 : ℂ) * Complex.I

/-- Algebraic phase Wronskian of the literal Euler feature at zero phase. -/
def xiGammaEulerHeightBoundaryWronskianAtZero
    (u : ℝ) (i j : Nat.Primes × ℕ) : ℂ :=
  xiGammaEulerHeightBoundaryFeature u 0 i *
      (xiGammaEulerBoundaryPhaseVelocity j *
        xiGammaEulerHeightBoundaryFeature u 0 j) -
    (xiGammaEulerBoundaryPhaseVelocity i *
      xiGammaEulerHeightBoundaryFeature u 0 i) *
        xiGammaEulerHeightBoundaryFeature u 0 j

/-- The calibrated real current is exactly the coefficient of the literal complex phase
Wronskian.  This closes the cellwise safe-half-plane source-identification gate. -/
theorem xiGammaEulerHeightBoundaryWronskianAtZero_eq_I_mul_exterior
    (u : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerHeightBoundaryWronskianAtZero u i j =
      Complex.I * (xiGammaEulerBoundaryExteriorCell u i j : ℂ) := by
  rw [xiGammaEulerHeightBoundaryWronskianAtZero,
    xiGammaEulerHeightBoundaryFeature_zero_eq_realAmplitude,
    xiGammaEulerHeightBoundaryFeature_zero_eq_realAmplitude]
  unfold xiGammaEulerBoundaryPhaseVelocity
    xiGammaEulerBoundaryExteriorCell
  push_cast
  ring

end

end RHTower
