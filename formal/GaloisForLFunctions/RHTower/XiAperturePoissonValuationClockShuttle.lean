import GaloisForLFunctions.RHTower.XiTransversePrimeSourceProjectiveTangent

/-!
# The Xi aperture--Poisson valuation-clock shuttle

At prime `p` and valuation depth `e`, the actual transverse Xi source is the Brownian--Laplace
primitive sampled at rate `(e+1) log p`.  Its aperture derivative is the exponential at that rate.
Multiplying by the aperture gives exactly the normalized half-line spectral density of the Poisson
response.  Thus a Poisson scale shuttle is the difference of two Euler-aperture derivatives of the
actual source primitive, not an analogy imposed after the fact.

The two densities have one exact spectral switch.  Above it the source shuttle is strictly
negative, so every sufficiently deep valuation layer and every sufficiently large prime lies in
the same response orientation.  This module formalizes the pointwise source bridge and threshold;
completion of the multiplier into the full Xi quadratic response remains open.
-/

namespace RHTower

noncomputable section

/-- The actual valuation-`e` logarithmic clock at prime `p`. -/
def xiPrimeValuationLaplaceRate (e : ℕ) (p : Nat.Primes) : ℝ :=
  ((e + 1 : ℕ) : ℝ) * Real.log (p : ℝ)

theorem xiPrimeValuationLaplaceRate_pos (e : ℕ) (p : Nat.Primes) :
    0 < xiPrimeValuationLaplaceRate e p := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  exact mul_pos (by positivity) (Real.log_pos hp)

/-- Canonical real-aperture continuation of the normalized prime-power Xi source primitive. -/
def xiTransversePrimePowerContinuousLaplacePrimitive
    (a : ℝ) (e : ℕ) (p : Nat.Primes) : ℝ :=
  (1 - Real.exp (-a * xiPrimeValuationLaplaceRate e p)) /
    xiPrimeValuationLaplaceRate e p

/-- At every integral aperture, the real continuation is exactly the existing Brownian--Laplace
sample of the normalized actual Xi transverse prime-power source. -/
theorem xiTransversePrimePowerContinuousLaplacePrimitive_natCast
    (a e : ℕ) (p : Nat.Primes) :
    (xiTransversePrimePowerContinuousLaplacePrimitive (a : ℝ) e p : ℂ) =
      xiTransversePrimePowerBrownianLaplaceSample a e p := by
  have hr := xiPrimeValuationLaplaceRate_pos e p
  rw [xiTransversePrimePowerBrownianLaplaceSample]
  change (xiTransversePrimePowerContinuousLaplacePrimitive (a : ℝ) e p : ℂ) =
    ∫ t : ℝ in 0..(a : ℝ),
      Complex.exp (-((xiPrimeValuationLaplaceRate e p : ℝ) : ℂ) * t)
  rw [intervalIntegral_cexp_neg_rate hr]
  unfold xiTransversePrimePowerContinuousLaplacePrimitive
  push_cast
  congr 2
  ring_nf

/-- Differentiating the actual source primitive exposes its valuation-clock exponential. -/
theorem hasDerivAt_xiTransversePrimePowerContinuousLaplacePrimitive
    (a : ℝ) (e : ℕ) (p : Nat.Primes) :
    HasDerivAt
      (fun u : ℝ => xiTransversePrimePowerContinuousLaplacePrimitive u e p)
      (Real.exp (-a * xiPrimeValuationLaplaceRate e p)) a := by
  let r := xiPrimeValuationLaplaceRate e p
  have hr : 0 < r := xiPrimeValuationLaplaceRate_pos e p
  have harg : HasDerivAt (fun u : ℝ => -u * r) (-r) a := by
    simpa using (hasDerivAt_id a).neg.mul_const r
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u * r))
      (-r * Real.exp (-a * r)) a := by
    simpa [mul_comm] using (Real.hasDerivAt_exp (-a * r)).comp a harg
  have hnum : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u * r))
      (r * Real.exp (-a * r)) a := by
    convert (hasDerivAt_const a (1 : ℝ)).sub hexp using 1
    all_goals ring_nf
  have hquot := hnum.div_const r
  simpa [xiTransversePrimePowerContinuousLaplacePrimitive, r, hr.ne'] using hquot

/-- The normalized half-line spectral density of the Poisson response. -/
def poissonSpectralHalfDensity (a t : ℝ) : ℝ :=
  a * Real.exp (-a * t)

/-- The signed spectral weight transported between two Poisson resolutions. -/
def poissonSpectralScaleShuttle (a b t : ℝ) : ℝ :=
  poissonSpectralHalfDensity b t - poissonSpectralHalfDensity a t

/-- At every actual valuation clock, the Poisson density is the aperture Euler derivative of the
normalized Xi transverse source primitive. -/
theorem poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate_eq_sourceEulerDerivative
    (a : ℝ) (e : ℕ) (p : Nat.Primes) :
    poissonSpectralHalfDensity a (xiPrimeValuationLaplaceRate e p) =
      a * deriv
        (fun u : ℝ => xiTransversePrimePowerContinuousLaplacePrimitive u e p) a := by
  rw [(hasDerivAt_xiTransversePrimePowerContinuousLaplacePrimitive a e p).deriv]
  rfl

/-- The signed Poisson shuttle is exactly the difference of two source Euler derivatives. -/
theorem poissonSpectralScaleShuttle_xiPrimeValuationLaplaceRate_eq_sourceEulerDerivative
    (a b : ℝ) (e : ℕ) (p : Nat.Primes) :
    poissonSpectralScaleShuttle a b (xiPrimeValuationLaplaceRate e p) =
      b * deriv
          (fun u : ℝ => xiTransversePrimePowerContinuousLaplacePrimitive u e p) b -
        a * deriv
          (fun u : ℝ => xiTransversePrimePowerContinuousLaplacePrimitive u e p) a := by
  rw [(hasDerivAt_xiTransversePrimePowerContinuousLaplacePrimitive b e p).deriv,
    (hasDerivAt_xiTransversePrimePowerContinuousLaplacePrimitive a e p).deriv]
  rfl

/-- The unique frequency at which two Poisson spectral densities agree. -/
def poissonSpectralScaleSwitch (a b : ℝ) : ℝ :=
  Real.log (b / a) / (b - a)

theorem poissonSpectralScaleSwitch_pos
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < poissonSpectralScaleSwitch a b := by
  have hratio : 1 < b / a := by
    rw [lt_div_iff₀ ha]
    simpa using hab
  exact div_pos (Real.log_pos hratio) (sub_pos.mpr hab)

private theorem poissonSpectralHalfDensity_eq_exp
    {a : ℝ} (ha : 0 < a) (t : ℝ) :
    poissonSpectralHalfDensity a t = Real.exp (Real.log a - a * t) := by
  unfold poissonSpectralHalfDensity
  calc
    a * Real.exp (-a * t) = Real.exp (Real.log a) * Real.exp (-a * t) := by
      rw [Real.exp_log ha]
    _ = Real.exp (Real.log a + -a * t) := (Real.exp_add _ _).symm
    _ = Real.exp (Real.log a - a * t) := by
      congr 1
      ring_nf

/-- The scale shuttle is positive precisely below its unique spectral switch. -/
theorem poissonSpectralScaleShuttle_pos_iff
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < poissonSpectralScaleShuttle a b t ↔
      t < poissonSpectralScaleSwitch a b := by
  have hb : 0 < b := ha.trans hab
  rw [poissonSpectralScaleShuttle, sub_pos,
    poissonSpectralHalfDensity_eq_exp ha,
    poissonSpectralHalfDensity_eq_exp hb,
    Real.exp_lt_exp, poissonSpectralScaleSwitch,
    lt_div_iff₀ (sub_pos.mpr hab), Real.log_div hb.ne' ha.ne']
  constructor <;> intro h <;> nlinarith

/-- The scale shuttle vanishes precisely at its unique spectral switch. -/
theorem poissonSpectralScaleShuttle_eq_zero_iff
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) :
    poissonSpectralScaleShuttle a b t = 0 ↔
      t = poissonSpectralScaleSwitch a b := by
  have hb : 0 < b := ha.trans hab
  rw [poissonSpectralScaleShuttle, sub_eq_zero,
    poissonSpectralHalfDensity_eq_exp hb,
    poissonSpectralHalfDensity_eq_exp ha,
    Real.exp_injective.eq_iff, poissonSpectralScaleSwitch,
    eq_div_iff (sub_pos.mpr hab).ne', Real.log_div hb.ne' ha.ne']
  constructor <;> intro h <;> nlinarith

/-- The scale shuttle is negative precisely above its unique spectral switch. -/
theorem poissonSpectralScaleShuttle_neg_iff
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) :
    poissonSpectralScaleShuttle a b t < 0 ↔
      poissonSpectralScaleSwitch a b < t := by
  have hb : 0 < b := ha.trans hab
  rw [poissonSpectralScaleShuttle, sub_neg,
    poissonSpectralHalfDensity_eq_exp hb,
    poissonSpectralHalfDensity_eq_exp ha,
    Real.exp_lt_exp, poissonSpectralScaleSwitch,
    div_lt_iff₀ (sub_pos.mpr hab), Real.log_div hb.ne' ha.ne']
  constructor <;> intro h <;> nlinarith

/-- At an actual prime-valuation clock, lying above the switch is exactly strict negative source
shuttle orientation. -/
theorem poissonSpectralScaleShuttle_xiPrimeValuationLaplaceRate_neg_iff
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (e : ℕ) (p : Nat.Primes) :
    poissonSpectralScaleShuttle a b (xiPrimeValuationLaplaceRate e p) < 0 ↔
      poissonSpectralScaleSwitch a b < xiPrimeValuationLaplaceRate e p :=
  poissonSpectralScaleShuttle_neg_iff ha hab

end

end RHTower
