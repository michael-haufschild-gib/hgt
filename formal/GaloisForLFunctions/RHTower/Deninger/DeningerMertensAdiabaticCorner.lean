import GaloisForLFunctions.RHTower.ArithmeticLogClockFiniteJetSaturation
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticTimeDistribution
import GaloisForLFunctions.RHTower.FriableAuxiliary
import GaloisForLFunctions.RHTower.PrimeFirstTraceExponentialFlatGraphFracture

/-!
# The Deninger--Mertens adiabatic corner

For a prime `p`, the reciprocal logarithm `εₚ = 1 / log p` is the arithmetic
adiabatic parameter.  Horizontal Euler displacement `h` and positive
prime-orbit Fourier depth `e` produce the coefficient

`exp (-h e / εₚ) = p⁻ʰᵉ`.

Finite `h / εₚ` is the Tate-normalized Poisson front face, `h = 1` is the
reciprocal-prime Hardy coordinate, derivatives at `h = 0` are the full
prime-log clock, and fixed positive `h` is exponentially flat as `p → ∞`.
The rescaled logarithm retains the exact action `h e`.

The statements are source-side identities.  They do not construct a positive
completion of the co-Poisson zero-evaluation quotient.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Reciprocal prime-log scale, the arithmetic adiabatic parameter. -/
def deningerPrimeAdiabaticParameter (p : Nat.Primes) : ℝ :=
  (Real.log (p : ℕ))⁻¹

theorem deningerPrimeAdiabaticParameter_pos (p : Nat.Primes) :
    0 < deningerPrimeAdiabaticParameter p := by
  exact inv_pos.mpr (Real.log_pos (by exact_mod_cast p.2.one_lt))

theorem deningerPrimeAdiabaticParameter_mul_log (p : Nat.Primes) :
    deningerPrimeAdiabaticParameter p * Real.log (p : ℕ) = 1 := by
  rw [deningerPrimeAdiabaticParameter]
  exact inv_mul_cancel₀
    (Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast p.2.pos)
      (by exact_mod_cast p.2.ne_one))

/-- Source-curved Poisson damping at horizontal displacement `h` and
positive prime-orbit Fourier depth `e`. -/
def deningerSourceCurvedPoissonCoefficient
    (p : Nat.Primes) (h : ℝ) (e : ℕ) : ℝ :=
  Real.exp (-(h * (e : ℝ) * Real.log (p : ℕ)))

theorem deningerSourceCurvedPoissonCoefficient_pos
    (p : Nat.Primes) (h : ℝ) (e : ℕ) :
    0 < deningerSourceCurvedPoissonCoefficient p h e :=
  Real.exp_pos _

/-- The coefficient is the exact two-scale kernel `exp (-h e / εₚ)`. -/
theorem deningerSourceCurvedPoissonCoefficient_eq_adiabatic
    (p : Nat.Primes) (h : ℝ) (e : ℕ) :
    deningerSourceCurvedPoissonCoefficient p h e =
      Real.exp (-(h * (e : ℝ)) / deningerPrimeAdiabaticParameter p) := by
  simp only [deningerSourceCurvedPoissonCoefficient,
    deningerPrimeAdiabaticParameter, div_eq_mul_inv, inv_inv]
  ring_nf

/-- Finite blow-up coordinate `τ` removes all prime dependence. -/
theorem deningerSourceCurvedPoissonCoefficient_frontFace
    (p : Nat.Primes) (τ : ℝ) (e : ℕ) :
    deningerSourceCurvedPoissonCoefficient p
        (τ * deningerPrimeAdiabaticParameter p) e =
      Real.exp (-(τ * (e : ℝ))) := by
  rw [deningerSourceCurvedPoissonCoefficient_eq_adiabatic]
  have hε : deningerPrimeAdiabaticParameter p ≠ 0 :=
    ne_of_gt (deningerPrimeAdiabaticParameter_pos p)
  congr 1
  field_simp [hε]

/-- Common Tate time `r` is the finite front-face coordinate `τ = 2πr`. -/
theorem deningerSourceCurvedPoissonCoefficient_commonTateTime
    (p : Nat.Primes) (r : ℝ) (e : ℕ) :
    deningerSourceCurvedPoissonCoefficient p
        (2 * Real.pi * r * deningerPrimeAdiabaticParameter p) e =
      Real.exp (-(2 * Real.pi * r * (e : ℝ))) := by
  simpa [mul_assoc] using
    deningerSourceCurvedPoissonCoefficient_frontFace p
      (2 * Real.pi * r) e

/-- Positive depth `e+1` is damped by horizontal displacement times
Deninger's `(e+1) log p` prime-power orbit time. -/
theorem deningerSourceCurvedPoissonCoefficient_succ_eq_orbitTime
    (p : Nat.Primes) (h : ℝ) (e : ℕ) :
    deningerSourceCurvedPoissonCoefficient p h (e + 1) =
      Real.exp
        (-h * deningerPrimePowerTime
          (deningerEulerPrimePowerIndex (p, e))) := by
  rw [deningerPrimePowerTime_euler]
  simp only [deningerSourceCurvedPoissonCoefficient]
  congr 1
  push_cast
  ring

/-- At arithmetic time one the Poisson coefficient is the reciprocal-prime
Hardy monomial. -/
theorem deningerSourceCurvedPoissonCoefficient_one_eq_primeReciprocal_pow
    (p : Nat.Primes) (e : ℕ) :
    deningerSourceCurvedPoissonCoefficient p 1 e =
      primeReciprocal p ^ e := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  rw [deningerSourceCurvedPoissonCoefficient, primeReciprocal]
  calc
    Real.exp (-(1 * (e : ℝ) * Real.log (p : ℕ))) =
        Real.exp ((e : ℝ) * (-Real.log (p : ℕ))) := by ring_nf
    _ = Real.exp (-Real.log (p : ℕ)) ^ e := Real.exp_nat_mul _ e
    _ = ((p : ℝ)⁻¹) ^ e := by rw [Real.exp_neg, Real.exp_log hp]

/-- The same arithmetic time-one coefficient is the literal coordinate of
the completed reciprocal-prime Hardy kernel. -/
theorem deningerSourceCurvedPoissonCoefficient_one_eq_primeHardyKernel
    (p : Nat.Primes) (e : ℕ) :
    deningerSourceCurvedPoissonCoefficient p 1 e =
      primeHardyKernel p e := by
  rw [deningerSourceCurvedPoissonCoefficient_one_eq_primeReciprocal_pow]
  rfl

/-- Complexified source-curved Poisson coefficient, used to expose its
complete horizontal boundary jet. -/
def deningerSourceCurvedPoissonCoefficientComplex
    (p : Nat.Primes) (e : ℕ) (h : ℂ) : ℂ :=
  Complex.exp
    (-(h * ((e : ℂ) * (Real.log (p : ℕ) : ℂ))))

/-- Every horizontal boundary derivative is the corresponding power of the
prime-log clock. -/
theorem iteratedDeriv_deningerSourceCurvedPoissonCoefficientComplex_zero
    (p : Nat.Primes) (e k : ℕ) :
    iteratedDeriv k
        (deningerSourceCurvedPoissonCoefficientComplex p e) 0 =
      (-((e : ℂ) * (Real.log (p : ℕ) : ℂ))) ^ k := by
  change iteratedDeriv k
      (fun h : ℂ =>
        Complex.exp
          (-(h * ((e : ℂ) * (Real.log (p : ℕ) : ℂ))))) 0 = _
  rw [GaloisForLFunctions.iteratedDeriv_exp_neg_mul_log]
  simp

/-- The exponential associated-graded action survives exactly after
rescaling the logarithm by `εₚ`. -/
theorem deningerSourceCurvedPoissonCoefficient_wkbAction
    (p : Nat.Primes) (h : ℝ) (e : ℕ) :
    -deningerPrimeAdiabaticParameter p *
        Real.log (deningerSourceCurvedPoissonCoefficient p h e) =
      h * (e : ℝ) := by
  rw [deningerSourceCurvedPoissonCoefficient, Real.log_exp,
    deningerPrimeAdiabaticParameter]
  have hlog : Real.log (p : ℕ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast p.2.pos)
      (by exact_mod_cast p.2.ne_one)
  field_simp [hlog]

/-- At every fixed positive displacement and positive depth, the
source-curved coefficient is flat beyond every prime-log algebraic order. -/
theorem tendsto_log_pow_mul_deningerSourceCurvedPoissonCoefficient_zero
    (N : ℕ) {h : ℝ} (hh : 0 < h) {e : ℕ} (he : 0 < e) :
    Tendsto
      (fun n =>
        Real.log ((nthPrimePoint n).1 : ℝ) ^ N *
          deningerSourceCurvedPoissonCoefficient
            (nthPrimePoint n) h e)
      atTop (𝓝 0) := by
  let γ : ℝ := h * (e : ℝ)
  have hγ : 0 < γ := mul_pos hh (by exact_mod_cast he)
  have hscale :
      Tendsto
        (fun n => γ * Real.log ((nthPrimePoint n).1 : ℝ))
        atTop atTop :=
    tendsto_log_nthPrimePoint_atTop.const_mul_atTop hγ
  have hflat :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).comp hscale
  have hscaled :
      Tendsto
        (fun n =>
          γ⁻¹ ^ N *
            ((γ * Real.log ((nthPrimePoint n).1 : ℝ)) ^ N *
              Real.exp
                (-(γ * Real.log ((nthPrimePoint n).1 : ℝ)))))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      hflat.const_mul (γ⁻¹ ^ N)
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hfun :
      (fun n =>
        Real.log ((nthPrimePoint n).1 : ℝ) ^ N *
          deningerSourceCurvedPoissonCoefficient
            (nthPrimePoint n) h e) =
      (fun n =>
        γ⁻¹ ^ N *
          ((γ * Real.log ((nthPrimePoint n).1 : ℝ)) ^ N *
            Real.exp
              (-(γ * Real.log ((nthPrimePoint n).1 : ℝ))))) := by
    funext n
    simp only [deningerSourceCurvedPoissonCoefficient, γ]
    have hγ0' : h * (e : ℝ) ≠ 0 := by simpa [γ] using hγ0
    have hcoeff :
        Real.log ((nthPrimePoint n).1 : ℝ) ^ N =
          (h * (e : ℝ))⁻¹ ^ N *
            (h * (e : ℝ) *
              Real.log ((nthPrimePoint n).1 : ℝ)) ^ N := by
      calc
        Real.log ((nthPrimePoint n).1 : ℝ) ^ N =
            1 * Real.log ((nthPrimePoint n).1 : ℝ) ^ N := by rw [one_mul]
        _ = (((h * (e : ℝ))⁻¹ * (h * (e : ℝ))) ^ N) *
            Real.log ((nthPrimePoint n).1 : ℝ) ^ N := by
              rw [inv_mul_cancel₀ hγ0', one_pow, one_mul]
        _ = (h * (e : ℝ))⁻¹ ^ N * (h * (e : ℝ)) ^ N *
            Real.log ((nthPrimePoint n).1 : ℝ) ^ N := by
              rw [mul_pow]
        _ = (h * (e : ℝ))⁻¹ ^ N *
            (h * (e : ℝ) * Real.log ((nthPrimePoint n).1 : ℝ)) ^ N := by
              rw [mul_pow]
              ring
    rw [hcoeff]
    ring
  rw [hfun]
  exact hscaled

end

end RHTower
