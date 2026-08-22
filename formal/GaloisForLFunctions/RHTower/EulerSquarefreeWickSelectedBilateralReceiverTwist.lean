import GaloisForLFunctions.RHTower.EulerSquarefreeWickPrimitiveCompletedInteraction
import GaloisForLFunctions.RHTower.XiSelectedBilateralPositiveSourceReceiver

/-!
# EWQ twisting of the Xi-selected bilateral receiver

The Xi-selected canonical bilateral receiver is an exact RH detector: its off-diagonal entries are
the forward and inverse Meyer prime characters, and positivity forces their common norm to be one.
This file tests whether the cofinally recurring EWQ quadratic interaction can create that missing
positivity by twisting both source orientations.

It cannot.  At every prime the EWQ coefficient is a real involution, so the twisted receiver is
unitarily congruent to the original receiver by the diagonal Pauli gauge `diag(1, χ)`.  Positivity
of the twisted and untwisted receivers is equivalent, hence each is still equivalent to critical-
line placement of the selected Xi divisor.  The result kills the direct character-twist route while
retaining a sharp positive survivor: EWQ twisting preserves any future fixed-star producer exactly.
-/

open Complex Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- The literal EWQ prime interaction coefficient, now used as a bilateral source gauge. -/
def eulerWickSelectedBilateralTwistCoefficient (p : Nat.Primes) : ℂ :=
  GaloisForLFunctions.RHTower.quadraticResidueProductPrimeCoefficient p

theorem eulerWickSelectedBilateralTwistCoefficient_sq (p : Nat.Primes) :
    eulerWickSelectedBilateralTwistCoefficient p ^ 2 = 1 := by
  exact GaloisForLFunctions.RHTower.quadraticResidueProductPrimeCoefficient_sq p

theorem eulerWickSelectedBilateralTwistCoefficient_eq_one_or_neg_one
    (p : Nat.Primes) :
    eulerWickSelectedBilateralTwistCoefficient p = 1 ∨
      eulerWickSelectedBilateralTwistCoefficient p = -1 := by
  exact (sq_eq_one_iff).mp (eulerWickSelectedBilateralTwistCoefficient_sq p)

@[simp] theorem star_eulerWickSelectedBilateralTwistCoefficient
    (p : Nat.Primes) :
    star (eulerWickSelectedBilateralTwistCoefficient p) =
      eulerWickSelectedBilateralTwistCoefficient p := by
  rcases eulerWickSelectedBilateralTwistCoefficient_eq_one_or_neg_one p with h | h <;>
    simp [h]

/-- Diagonal Pauli gauge implementing the EWQ twist on the two source orientations. -/
def eulerWickSelectedBilateralTwistGauge
    (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, eulerWickSelectedBilateralTwistCoefficient p]

/-- Receiver obtained by applying the same literal EWQ gauge to both bilateral legs. -/
def deningerMeyerXiPrimeGammaEulerWickTwistedReceiver
    (rho : XiDivisorSupport) (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  let D := eulerWickSelectedBilateralTwistGauge p
  Dᴴ * deningerMeyerXiPrimeGammaCanonicalBilateralReceiver rho p * D

/-- The EWQ gauge is Hermitian. -/
theorem eulerWickSelectedBilateralTwistGauge_isHermitian (p : Nat.Primes) :
    (eulerWickSelectedBilateralTwistGauge p).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickSelectedBilateralTwistGauge]

/-- The EWQ gauge is an involution. -/
theorem eulerWickSelectedBilateralTwistGauge_sq (p : Nat.Primes) :
    eulerWickSelectedBilateralTwistGauge p *
      eulerWickSelectedBilateralTwistGauge p = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickSelectedBilateralTwistGauge, Matrix.mul_apply]
  simpa [pow_two] using eulerWickSelectedBilateralTwistCoefficient_sq p

/-- Exact entry law: both literal source orientations acquire the same quadratic sign. -/
theorem deningerMeyerXiPrimeGammaEulerWickTwistedReceiver_eq
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    deningerMeyerXiPrimeGammaEulerWickTwistedReceiver rho p =
      let chi := deningerMeyerXiPrimeGammaCharacter rho p
      let eps := eulerWickSelectedBilateralTwistCoefficient p
      !![(1 : ℂ), eps * chi; eps * chi⁻¹, 1] := by
  rw [deningerMeyerXiPrimeGammaEulerWickTwistedReceiver]
  have hc2 := eulerWickSelectedBilateralTwistCoefficient_sq p
  ext i j
  fin_cases i <;> fin_cases j
  · simp [eulerWickSelectedBilateralTwistGauge,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver, Matrix.mul_apply]
  · simp [eulerWickSelectedBilateralTwistGauge,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver, Matrix.mul_apply]
    ring
  · simp [eulerWickSelectedBilateralTwistGauge,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver, Matrix.mul_apply]
  · simp [eulerWickSelectedBilateralTwistGauge,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver, Matrix.mul_apply]
    exact (show eulerWickSelectedBilateralTwistCoefficient p *
      eulerWickSelectedBilateralTwistCoefficient p = 1 by
        simpa only [pow_two] using hc2)

/-- Applying the same EWQ congruence twice recovers the original canonical receiver. -/
theorem eulerWickTwist_congr_twistedReceiver_eq_canonical
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    let D := eulerWickSelectedBilateralTwistGauge p
    Dᴴ * deningerMeyerXiPrimeGammaEulerWickTwistedReceiver rho p * D =
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver rho p := by
  dsimp only
  have hc2 := eulerWickSelectedBilateralTwistCoefficient_sq p
  ext i j
  fin_cases i <;> fin_cases j
  · simp [deningerMeyerXiPrimeGammaEulerWickTwistedReceiver,
      eulerWickSelectedBilateralTwistGauge,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver, Matrix.mul_apply]
  · simp [deningerMeyerXiPrimeGammaEulerWickTwistedReceiver,
      eulerWickSelectedBilateralTwistGauge,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver, Matrix.mul_apply]
    calc
      deningerMeyerXiPrimeGammaCharacter rho p *
          eulerWickSelectedBilateralTwistCoefficient p *
          eulerWickSelectedBilateralTwistCoefficient p =
          deningerMeyerXiPrimeGammaCharacter rho p *
            eulerWickSelectedBilateralTwistCoefficient p ^ 2 := by ring
      _ = deningerMeyerXiPrimeGammaCharacter rho p := by rw [hc2, mul_one]
  · simp [deningerMeyerXiPrimeGammaEulerWickTwistedReceiver,
      eulerWickSelectedBilateralTwistGauge,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver, Matrix.mul_apply]
    calc
      eulerWickSelectedBilateralTwistCoefficient p *
          (eulerWickSelectedBilateralTwistCoefficient p *
            (deningerMeyerXiPrimeGammaCharacter rho p)⁻¹) =
          eulerWickSelectedBilateralTwistCoefficient p ^ 2 *
            (deningerMeyerXiPrimeGammaCharacter rho p)⁻¹ := by ring
      _ = (deningerMeyerXiPrimeGammaCharacter rho p)⁻¹ := by rw [hc2, one_mul]
  · simp [deningerMeyerXiPrimeGammaEulerWickTwistedReceiver,
      eulerWickSelectedBilateralTwistGauge,
      deningerMeyerXiPrimeGammaCanonicalBilateralReceiver, Matrix.mul_apply]
    calc
      eulerWickSelectedBilateralTwistCoefficient p *
          (eulerWickSelectedBilateralTwistCoefficient p *
            eulerWickSelectedBilateralTwistCoefficient p) *
          eulerWickSelectedBilateralTwistCoefficient p =
          (eulerWickSelectedBilateralTwistCoefficient p ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hc2, one_pow]

/-- **Exact no-go.**  A quadratic EWQ sign twist preserves bilateral positivity but cannot create
it: twisted and untwisted receiver positivity are equivalent. -/
theorem eulerWickTwistedReceiver_posSemidef_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    (deningerMeyerXiPrimeGammaEulerWickTwistedReceiver rho p).PosSemidef ↔
      (deningerMeyerXiPrimeGammaCanonicalBilateralReceiver rho p).PosSemidef := by
  constructor
  · intro h
    rw [← eulerWickTwist_congr_twistedReceiver_eq_canonical rho p]
    exact h.conjTranspose_mul_mul_same _
  · intro h
    rw [deningerMeyerXiPrimeGammaEulerWickTwistedReceiver]
    exact h.conjTranspose_mul_mul_same _

/-- Twisted positivity remains exactly the critical-line condition on the selected divisor. -/
theorem eulerWickTwistedReceiver_posSemidef_iff_re_eq_half
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    (deningerMeyerXiPrimeGammaEulerWickTwistedReceiver rho p).PosSemidef ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [eulerWickTwistedReceiver_posSemidef_iff,
    ← XiSelectedBilateralPositiveSourceReceiverAt,
    xiSelectedBilateralPositiveSourceReceiverAt_iff_re_eq_half]

end

end RHTower
