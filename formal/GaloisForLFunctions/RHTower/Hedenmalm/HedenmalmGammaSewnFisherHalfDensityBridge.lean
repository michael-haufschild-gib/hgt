import GaloisForLFunctions.RHTower.GammaSewnMobiusJuliaSourceTransport
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPrimeNormalSolderingCurvature

/-!
# Gamma-sewn source provenance of the Hedenmalm prime half-density

The canonical Gamma-sewn Möbius soft source has prime-grade mass `1 / (p log p)`.  Multiplication
by the square root of its source-generated Julia prime-log tangent gives exactly the Hedenmalm
half-density `p⁻¹ᐟ²`.  Positive damping produces the canonical Hilbert rigging
`p^{-(1+u)/2}` whose zero-damping boundary is Route N's non-Hilbert marked horizon.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Fisher half-transport of the actual Gamma-sewn Möbius soft source on prime grade zero. -/
def gammaSewnHedenmalmFisherHalfDensity (u : ℝ) (p : Nat.Primes) : ℝ :=
  Real.sqrt (Real.log (p.1 : ℝ)) *
    gammaSewnMobiusJuliaSoftHalfWeightSource u (p, 0)

/-- Exact damped prime-normal mass of the source-derived Fisher half-transport. -/
theorem gammaSewnHedenmalmFisherHalfDensity_sq (u : ℝ) (p : Nat.Primes) :
    gammaSewnHedenmalmFisherHalfDensity u p ^ 2 =
      Real.exp (-u * Real.log (p.1 : ℝ)) / (p.1 : ℝ) := by
  have hpLog : 0 < Real.log (p.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  rw [gammaSewnHedenmalmFisherHalfDensity, mul_pow,
    Real.sq_sqrt hpLog.le, gammaSewnMobiusJuliaSoftHalfWeightSource_sq]
  have hval : xiGammaEulerValuationNat (p, 0) = p.1 := by
    norm_num [xiGammaEulerValuationNat]
  rw [hval]
  field_simp [hpLog.ne', hp0.ne']

theorem gammaSewnHedenmalmFisherHalfDensity_pos (u : ℝ) (p : Nat.Primes) :
    0 < gammaSewnHedenmalmFisherHalfDensity u p := by
  rw [gammaSewnHedenmalmFisherHalfDensity]
  exact mul_pos (Real.sqrt_pos.2
    (Real.log_pos (by exact_mod_cast p.2.one_lt)))
      (gammaSewnMobiusJuliaSoftHalfWeightSource_pos u (p, 0))

/-- The Fisher half-transport is exactly the exponentially damped Hedenmalm half-density. -/
theorem gammaSewnHedenmalmFisherHalfDensity_eq (u : ℝ) (p : Nat.Primes) :
    gammaSewnHedenmalmFisherHalfDensity u p =
      Real.exp (-u * Real.log (p.1 : ℝ) / 2) * hedenmalmPrimeHalfDensity p.1 := by
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hsqrt : Real.sqrt (p.1 : ℝ) ^ 2 = (p.1 : ℝ) := Real.sq_sqrt hp0.le
  have hdensitySq : hedenmalmPrimeHalfDensity p.1 ^ 2 = 1 / (p.1 : ℝ) := by
    rw [hedenmalmPrimeHalfDensity, inv_pow, hsqrt]
    simp [div_eq_mul_inv]
  have hexpSq : Real.exp (-u * Real.log (p.1 : ℝ) / 2) ^ 2 =
      Real.exp (-u * Real.log (p.1 : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsquare : gammaSewnHedenmalmFisherHalfDensity u p ^ 2 =
      (Real.exp (-u * Real.log (p.1 : ℝ) / 2) *
        hedenmalmPrimeHalfDensity p.1) ^ 2 := by
    rw [gammaSewnHedenmalmFisherHalfDensity_sq, mul_pow, hexpSq, hdensitySq,
      div_eq_mul_inv]
    rw [one_div]
  have hleft := gammaSewnHedenmalmFisherHalfDensity_pos u p
  have hright : 0 < Real.exp (-u * Real.log (p.1 : ℝ) / 2) *
      hedenmalmPrimeHalfDensity p.1 := by
    apply mul_pos (Real.exp_pos _)
    rw [hedenmalmPrimeHalfDensity]
    exact inv_pos.mpr (Real.sqrt_pos.2 hp0)
  nlinarith

/-- **Literal Route-N source provenance.** At zero damping, the source-derived Fisher coordinate
is exactly `p⁻¹ᐟ²`, not an externally imposed diagonal weight. -/
theorem gammaSewnHedenmalmFisherHalfDensity_zero (p : Nat.Primes) :
    gammaSewnHedenmalmFisherHalfDensity 0 p = hedenmalmPrimeHalfDensity p.1 := by
  rw [gammaSewnHedenmalmFisherHalfDensity_eq]
  simp

/-- Marked two-orientation Fisher source at damping `u`. -/
def gammaSewnHedenmalmDampedMarkedCharacter
    (u : ℝ) (p : Nat.Primes) (z : ℂ) : ℂ × ℂ :=
  let c : ℂ := (gammaSewnHedenmalmFisherHalfDensity u p : ℝ)
  let a : ℂ := ((Real.log (p.1 : ℝ) / 2 : ℝ) : ℂ)
  (c * Complex.exp (z * (Complex.I * a)),
    c * Complex.exp (z * (-Complex.I * a)))

theorem gammaSewnHedenmalmDampedMarkedCharacter_zero
    (p : Nat.Primes) (z : ℂ) :
    gammaSewnHedenmalmDampedMarkedCharacter 0 p z =
      hedenmalmMarkedPrimeHalfCharacter p.1 z := by
  rw [gammaSewnHedenmalmDampedMarkedCharacter,
    hedenmalmMarkedPrimeHalfCharacter,
    gammaSewnHedenmalmFisherHalfDensity_zero]

/-- Exact radial energy of the damped source-derived marked character. -/
theorem gammaSewnHedenmalmDampedMarkedCharacter_energy_eq_cosh
    (u : ℝ) (p : Nat.Primes) (z : ℂ) :
    hedenmalmMarkedPrimeEnergy
        (gammaSewnHedenmalmDampedMarkedCharacter u p z) =
      Real.exp (-u * Real.log (p.1 : ℝ)) *
        (2 / (p.1 : ℝ) * Real.cosh (z.im * Real.log (p.1 : ℝ))) := by
  have hshape :
      hedenmalmMarkedPrimeEnergy
          (gammaSewnHedenmalmDampedMarkedCharacter u p z) =
        gammaSewnHedenmalmFisherHalfDensity u p ^ 2 *
            Real.exp (-(z.im * Real.log (p.1 : ℝ))) +
          gammaSewnHedenmalmFisherHalfDensity u p ^ 2 *
            Real.exp (z.im * Real.log (p.1 : ℝ)) := by
    simp only [hedenmalmMarkedPrimeEnergy,
      gammaSewnHedenmalmDampedMarkedCharacter, norm_mul, Complex.norm_real,
      Complex.norm_exp, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
      zero_mul, one_mul, zero_sub, neg_re, neg_im, Real.norm_eq_abs]
    rw [abs_of_pos (gammaSewnHedenmalmFisherHalfDensity_pos u p)]
    congr 1 <;> ring_nf
    · rw [← Real.exp_nat_mul]
      congr 1
      ring_nf
    · rw [← Real.exp_nat_mul]
      congr 1
      ring_nf
  rw [hshape, gammaSewnHedenmalmFisherHalfDensity_sq, Real.cosh_eq]
  ring

/-- Dirichlet-power decomposition of one damped marked source energy. -/
theorem gammaSewnHedenmalmDampedMarkedCharacter_energy_eq_rpow
    (u : ℝ) (p : Nat.Primes) (z : ℂ) :
    hedenmalmMarkedPrimeEnergy
        (gammaSewnHedenmalmDampedMarkedCharacter u p z) =
      (p.1 : ℝ) ^ (-1 - u + z.im) + (p.1 : ℝ) ^ (-1 - u - z.im) := by
  rw [gammaSewnHedenmalmDampedMarkedCharacter_energy_eq_cosh,
    Real.cosh_eq]
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hinv : ((p.1 : ℝ))⁻¹ = Real.exp (-Real.log (p.1 : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log hp0]
  rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0,
    div_eq_mul_inv, hinv]
  rw [show -u * Real.log (p.1 : ℝ) =
      (-u) * Real.log (p.1 : ℝ) by ring]
  ring_nf
  apply congrArg₂ (· + ·)
  · rw [← Real.exp_add, ← Real.exp_add]
    congr 1
  · rw [← Real.exp_add, ← Real.exp_add]
    congr 1

/-- Hilbert admission of the source-derived damped marked horizon. -/
def GammaSewnHedenmalmDampedMarkedSummable (u : ℝ) (z : ℂ) : Prop :=
  Summable (fun p : Nat.Primes =>
    hedenmalmMarkedPrimeEnergy
      (gammaSewnHedenmalmDampedMarkedCharacter u p z))

/-- **Sharp source rigging horizon.** The actual Gamma-sewn Fisher half-density admits the marked
spectral character exactly when positive damping exceeds radial displacement. -/
theorem gammaSewnHedenmalmDampedMarkedSummable_iff
    (u : ℝ) (z : ℂ) :
    GammaSewnHedenmalmDampedMarkedSummable u z ↔ |z.im| < u := by
  rw [GammaSewnHedenmalmDampedMarkedSummable]
  have hrewrite : (fun p : Nat.Primes =>
      hedenmalmMarkedPrimeEnergy
        (gammaSewnHedenmalmDampedMarkedCharacter u p z)) =
      fun p : Nat.Primes =>
        (p.1 : ℝ) ^ (-1 - u + z.im) + (p.1 : ℝ) ^ (-1 - u - z.im) := by
    funext p
    exact gammaSewnHedenmalmDampedMarkedCharacter_energy_eq_rpow u p z
  rw [hrewrite]
  constructor
  · intro hsum
    have hplus : Summable (fun p : Nat.Primes => (p.1 : ℝ) ^ (-1 - u + z.im)) :=
      Summable.of_nonneg_of_le (fun p => by positivity)
        (fun p => le_add_of_nonneg_right (by positivity)) hsum
    have hminus : Summable (fun p : Nat.Primes => (p.1 : ℝ) ^ (-1 - u - z.im)) :=
      Summable.of_nonneg_of_le (fun p => by positivity)
        (fun p => le_add_of_nonneg_left (by positivity)) hsum
    have hp := Nat.Primes.summable_rpow.mp hplus
    have hm := Nat.Primes.summable_rpow.mp hminus
    rw [abs_lt]
    constructor <;> linarith
  · intro hu
    rw [abs_lt] at hu
    exact (Nat.Primes.summable_rpow.mpr (by linarith)).add
      (Nat.Primes.summable_rpow.mpr (by linarith))

end

end RHTower
