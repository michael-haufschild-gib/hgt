import GaloisForLFunctions.RHTower.Deninger.DeningerMertensAdiabaticCorner
import GaloisForLFunctions.RHTower.XiMobiusSchurValuationIntertwiner

/-!
# The critical Möbius Fisher damping is a reflected Deninger WKB seam

At one prime, the half-slope Deninger coefficient

`κₚ = exp (-(log p) / 2) = p⁻¹ᐟ²`

is the positive square root of the unit-aperture prime disk node.  The
Möbius valuation damping and its unbounded inverse dressing are exactly

`dₚ = κₚ / (1 + κₚ²)`,

`dₚ⁻¹ = κₚ⁻¹ + κₚ`.

Thus the square root of the local squarefree Fisher variance is the
inverse trace of the two reflected WKB branches.  The forbidden
all-prime inverse recovery is not an unrelated loss of boundedness: it
is the reflection-symmetric WKB multiplier at arithmetic half-slope.

These are unconditional source-side identities.  They do not construct
the singular all-prime graph that would transport the critical Fisher
tangent to the Xi Hardy boundary.
-/

namespace RHTower

noncomputable section

/-- Squaring the positive half-slope WKB coefficient gives the
time-one reciprocal-prime coefficient. -/
theorem deningerSourceCurvedPoissonCoefficient_half_sq
    (p : Nat.Primes) :
    deningerSourceCurvedPoissonCoefficient p (1 / 2 : ℝ) 1 ^ (2 : ℕ) =
      deningerSourceCurvedPoissonCoefficient p 1 1 := by
  simp only [deningerSourceCurvedPoissonCoefficient]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The half-slope WKB coefficient is the positive square root of the
unit-aperture prime disk node. -/
theorem deningerSourceCurvedPoissonCoefficient_half_eq_sqrt_primeNode
    (p : Nat.Primes) :
    deningerSourceCurvedPoissonCoefficient p (1 / 2 : ℝ) 1 =
      Real.sqrt (xiTransversePrimeApertureDiskNode 1 p) := by
  have hsq := deningerSourceCurvedPoissonCoefficient_half_sq p
  have hq :
      deningerSourceCurvedPoissonCoefficient p 1 1 =
        xiTransversePrimeApertureDiskNode 1 p := by
    rw [deningerSourceCurvedPoissonCoefficient_one_eq_primeReciprocal_pow]
    simp [primeReciprocal, xiTransversePrimeApertureDiskNode_one_eq_inv]
  rw [hq] at hsq
  have hk0 :
      0 ≤ deningerSourceCurvedPoissonCoefficient p (1 / 2 : ℝ) 1 :=
    (deningerSourceCurvedPoissonCoefficient_pos p (1 / 2 : ℝ) 1).le
  calc
    deningerSourceCurvedPoissonCoefficient p (1 / 2 : ℝ) 1 =
        Real.sqrt
          (deningerSourceCurvedPoissonCoefficient p (1 / 2 : ℝ) 1 ^ (2 : ℕ)) := by
      symm
      exact Real.sqrt_sq hk0
    _ = Real.sqrt (xiTransversePrimeApertureDiskNode 1 p) := by
      rw [hsq]

/-- Möbius Fisher damping is the normalized positive half-slope WKB
branch. -/
theorem xiMobiusPrimeSchurValuationDamping_eq_deningerWKB
    (p : Nat.Primes) :
    xiMobiusPrimeSchurValuationDamping p =
      deningerSourceCurvedPoissonCoefficient p (1 / 2 : ℝ) 1 /
        (1 + deningerSourceCurvedPoissonCoefficient p 1 1) := by
  rw [xiMobiusPrimeSchurValuationDamping,
    ← deningerSourceCurvedPoissonCoefficient_half_eq_sqrt_primeNode]
  congr 1
  rw [deningerSourceCurvedPoissonCoefficient_one_eq_primeReciprocal_pow]
  simp [primeReciprocal, xiTransversePrimeApertureDiskNode_one_eq_inv]

/-- The inverse Möbius dressing is the trace of the two reflected WKB
branches at half-slope. -/
theorem xiMobiusPrimeSchurValuationRecovery_eq_reflectedDeningerWKB
    (p : Nat.Primes) :
    xiMobiusPrimeSchurValuationRecovery p =
      (deningerSourceCurvedPoissonCoefficient p (1 / 2 : ℝ) 1)⁻¹ +
        deningerSourceCurvedPoissonCoefficient p (1 / 2 : ℝ) 1 := by
  let k := deningerSourceCurvedPoissonCoefficient p (1 / 2 : ℝ) 1
  have hk : 0 < k :=
    deningerSourceCurvedPoissonCoefficient_pos p (1 / 2 : ℝ) 1
  have hkq : k = Real.sqrt (xiTransversePrimeApertureDiskNode 1 p) :=
    deningerSourceCurvedPoissonCoefficient_half_eq_sqrt_primeNode p
  have hksq : k ^ (2 : ℕ) = xiTransversePrimeApertureDiskNode 1 p := by
    rw [deningerSourceCurvedPoissonCoefficient_half_sq]
    rw [deningerSourceCurvedPoissonCoefficient_one_eq_primeReciprocal_pow]
    simp [primeReciprocal, xiTransversePrimeApertureDiskNode_one_eq_inv]
  rw [xiMobiusPrimeSchurValuationRecovery, ← hkq]
  rw [div_eq_iff hk.ne']
  rw [add_mul, inv_mul_cancel₀ hk.ne']
  nlinarith

/-- The reflected WKB branch has exact arithmetic action one half. -/
theorem deningerSourceCurvedPoissonCoefficient_half_wkbAction
    (p : Nat.Primes) :
    -deningerPrimeAdiabaticParameter p *
        Real.log
          (deningerSourceCurvedPoissonCoefficient p (1 / 2 : ℝ) 1) =
      1 / 2 := by
  simpa using
    deningerSourceCurvedPoissonCoefficient_wkbAction p (1 / 2 : ℝ) 1

/-- Damping and reflected WKB recovery are exact positive inverses. -/
theorem xiMobiusPrimeSchurValuationDamping_mul_recovery
    (p : Nat.Primes) :
    xiMobiusPrimeSchurValuationDamping p *
        xiMobiusPrimeSchurValuationRecovery p = 1 := by
  have hq := xiTransversePrimeApertureDiskNode_pos 1 p
  simp only [xiMobiusPrimeSchurValuationDamping,
    xiMobiusPrimeSchurValuationRecovery]
  field_simp [Real.sqrt_ne_zero'.mpr hq]

/-- The local squarefree Fisher variance is the inverse square of the
reflected half-slope WKB trace. -/
theorem xiMobiusPrimeSchurValuationRecovery_sq_mul_parityVariance
    (p : Nat.Primes) :
    xiMobiusPrimeSchurValuationRecovery p ^ (2 : ℕ) *
        dyadicSquarefreeParityVariance (primeSchurWeight 1 p) = 1 := by
  rw [← xiMobiusPrimeSchurValuationDamping_sq_eq_parityVariance]
  rw [← mul_pow]
  rw [mul_comm, xiMobiusPrimeSchurValuationDamping_mul_recovery]
  norm_num

end

end RHTower
