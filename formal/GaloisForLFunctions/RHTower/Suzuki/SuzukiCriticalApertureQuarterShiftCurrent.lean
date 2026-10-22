import GaloisForLFunctions.RHTower.VonMangoldtGammaConormalEulerBoundary

/-!
# Critical aperture quarter-shift current

The uniquely renormalized Gamma--Euler boundary is not an `ell^(2 : ℕ)` vector at critical inverse
displacement `-1/2`.  Nevertheless, its source pairing with the cubically normalized true-aperture
innovation has an exact geometric depth law.  One valuation step multiplies the conjugated critical
Gamma boundary by

`exp(-(log p)/4) * exp(i*t*log p/2)`

and multiplies the innovation by the square of its aperture disk node.  Their product therefore has
ratio of norm strictly below one for every positive aperture.  This file proves the actual-source
atom recursion, summability in valuation depth, and its exact resolvent sum.  No standalone
critical boundary Hilbert vector, Xi zero, or RH premise is used.
-/

namespace RHTower

noncomputable section

open scoped ComplexConjugate

/-- Quarter-shift multiplier of one critical Gamma--Euler valuation step. -/
def suzukiCriticalGammaDepthRatio (t : ℝ) (p : Nat.Primes) : ℂ :=
  (Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) : ℂ) *
    Complex.exp ((((t * Real.log (p : ℝ) / 2 : ℝ) : ℂ) * Complex.I))

/-- Full depth ratio after adjoining the true-aperture innovation multiplier. -/
def suzukiCriticalApertureDepthRatio
    (h a t : ℝ) (p : Nat.Primes) : ℂ :=
  suzukiCriticalGammaDepthRatio t p *
    (xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ (2 : ℕ) : ℂ)

/-- Actual critical Gamma-boundary/true-aperture-innovation source atom. -/
def suzukiCriticalApertureBoundaryAtom
    (h a t : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  star (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, e)) *
    (xiMobiusCubicNormalizedInnovationFeature h a (p, e) : ℂ)

private theorem innovation_succ (h a : ℝ) (p : Nat.Primes) (e : ℕ) :
    xiMobiusCubicNormalizedInnovationFeature h a (p, e + 1) =
      xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ (2 : ℕ) *
        xiMobiusCubicNormalizedInnovationFeature h a (p, e) := by
  simp only [xiMobiusCubicNormalizedInnovationFeature,
    xiMobiusContinuousApertureDyadicInnovationFeature,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeature]
  rw [pow_succ]
  ring

private theorem criticalDensity_eq (p : Nat.Primes) (e : ℕ) :
    Real.log (p : ℝ) / (xiGammaEulerValuationNat (p, e) : ℝ) *
        Real.exp ((1 / 2 : ℝ) *
          Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) =
      Real.log (p : ℝ) *
        Real.exp (-(((e : ℝ) + 1) * Real.log (p : ℝ)) / 2) := by
  have hn : (0 : ℝ) < (xiGammaEulerValuationNat (p, e) : ℝ) := by
    exact_mod_cast Nat.pow_pos p.prop.pos
  have hlog : Real.log (xiGammaEulerValuationNat (p, e) : ℝ) =
      ((e : ℝ) + 1) * Real.log (p : ℝ) := by
    rw [xiGammaEulerValuationNat]
    push_cast
    rw [Real.log_pow]
    norm_num
  rw [hlog]
  have hinv : (xiGammaEulerValuationNat (p, e) : ℝ)⁻¹ =
      Real.exp (-Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log hn]
  rw [div_eq_mul_inv, hinv, hlog, mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem criticalAmplitude_succ (p : Nat.Primes) (e : ℕ) :
    Real.sqrt
        (Real.log (p : ℝ) /
            (xiGammaEulerValuationNat (p, e + 1) : ℝ) *
          Real.exp ((1 / 2 : ℝ) *
            Real.log (xiGammaEulerValuationNat (p, e + 1) : ℝ))) =
      Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) *
        Real.sqrt
          (Real.log (p : ℝ) /
              (xiGammaEulerValuationNat (p, e) : ℝ) *
            Real.exp ((1 / 2 : ℝ) *
              Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) := by
  rw [criticalDensity_eq, criticalDensity_eq]
  have hshift :
      -((((e + 1 : ℕ) : ℝ) + 1) * Real.log (p : ℝ)) / 2 =
        (-(1 / 2 : ℝ) * Real.log (p : ℝ)) +
          (-(((e : ℝ) + 1) * Real.log (p : ℝ)) / 2) := by
    push_cast
    ring
  rw [hshift, Real.exp_add]
  rw [show Real.log (p : ℝ) *
      (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) *
        Real.exp (-((↑e + 1) * Real.log (p : ℝ)) / 2)) =
      Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) *
        (Real.log (p : ℝ) *
          Real.exp (-((↑e + 1) * Real.log (p : ℝ)) / 2)) by ring]
  rw [Real.sqrt_mul (Real.exp_nonneg _)]
  have hsqrt :
      Real.sqrt (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ))) =
        Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) := by
    rw [Real.sqrt_eq_iff_eq_sq (Real.exp_nonneg _) (Real.exp_nonneg _)]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hsqrt]

private theorem log_valuation_succ (p : Nat.Primes) (e : ℕ) :
    Real.log (xiGammaEulerValuationNat (p, e + 1) : ℝ) =
      Real.log (p : ℝ) +
        Real.log (xiGammaEulerValuationNat (p, e) : ℝ) := by
  rw [xiGammaEulerValuationNat, xiGammaEulerValuationNat]
  push_cast
  rw [Real.log_pow, Real.log_pow]
  push_cast
  ring

private theorem criticalPhaseStar_succ (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    star (Complex.exp
        (-(((t * Real.log (xiGammaEulerValuationNat (p, e + 1) : ℝ) / 2 : ℝ) : ℂ) *
          Complex.I))) =
      Complex.exp ((((t * Real.log (p : ℝ) / 2 : ℝ) : ℂ) * Complex.I)) *
        star (Complex.exp
          (-(((t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ) / 2 : ℝ) : ℂ) *
            Complex.I))) := by
  change conj (Complex.exp
      (-(((t * Real.log (xiGammaEulerValuationNat (p, e + 1) : ℝ) / 2 : ℝ) : ℂ) *
        Complex.I))) =
    Complex.exp ((((t * Real.log (p : ℝ) / 2 : ℝ) : ℂ) * Complex.I)) *
      conj (Complex.exp
        (-(((t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ) / 2 : ℝ) : ℂ) *
          Complex.I)))
  rw [← Complex.exp_conj, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [log_valuation_succ, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem criticalGamma_succ (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    star (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, e + 1)) =
      suzukiCriticalGammaDepthRatio t p *
        star (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, e)) := by
  simp only [xiGammaEulerHeightBoundaryFeature]
  simp only [show -(-1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [criticalAmplitude_succ, star_mul, star_mul, criticalPhaseStar_succ]
  unfold suzukiCriticalGammaDepthRatio
  have hstar (x : ℝ) : star (x : ℂ) = (x : ℂ) := by
    exact Complex.conj_ofReal x
  rw [hstar, hstar]
  push_cast
  ring

/-- **Critical quarter-shift law.** One valuation step multiplies the actual paired source atom by
the fixed Gamma quarter-shift times the true-aperture disk square. -/
theorem suzukiCriticalApertureBoundaryAtom_succ
    (h a t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalApertureBoundaryAtom h a t p (e + 1) =
      suzukiCriticalApertureDepthRatio h a t p *
        suzukiCriticalApertureBoundaryAtom h a t p e := by
  rw [suzukiCriticalApertureBoundaryAtom,
    suzukiCriticalApertureBoundaryAtom, criticalGamma_succ,
    innovation_succ, suzukiCriticalApertureDepthRatio]
  push_cast
  ring

/-- Positive aperture makes the quarter-shift depth ratio strictly contractive. -/
theorem norm_suzukiCriticalApertureDepthRatio_lt_one
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    ‖suzukiCriticalApertureDepthRatio h a t p‖ < 1 := by
  have hL : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hg0 : 0 < Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) := Real.exp_pos _
  have hg1 : Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hra : 0 < (h / 2) * a := mul_pos (half_pos hh) ha
  have hr0 := xiMobiusContinuousApertureDiskNode_pos ((h / 2) * a) p
  have hr1 := xiMobiusContinuousApertureDiskNode_lt_one hra p
  rw [suzukiCriticalApertureDepthRatio, suzukiCriticalGammaDepthRatio,
    norm_mul, norm_mul]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg0,
    Complex.norm_exp_ofReal_mul_I]
  norm_num
  have hg1' : Real.exp (-(1 / 4 * Real.log (p : ℝ))) < 1 := by
    rw [show -(1 / 4 * Real.log (p : ℝ)) =
      -(1 / 4 : ℝ) * Real.log (p : ℝ) by ring]
    exact hg1
  have hrsq : xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ (2 : ℕ) < 1 := by
    nlinarith
  exact mul_lt_one_of_nonneg_of_lt_one_left (Real.exp_nonneg _) hg1' hrsq.le

/-- Every critical paired atom is its depth-zero value times one fixed ratio power. -/
theorem suzukiCriticalApertureBoundaryAtom_eq_base_mul_ratio_pow
    (h a t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalApertureBoundaryAtom h a t p e =
      suzukiCriticalApertureBoundaryAtom h a t p 0 *
        suzukiCriticalApertureDepthRatio h a t p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [suzukiCriticalApertureBoundaryAtom_succ, ih, pow_succ]
      ring

/-- Critical Gamma boundary paired with true-aperture innovation is summable in valuation depth. -/
theorem summable_suzukiCriticalApertureBoundaryAtom
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    Summable (suzukiCriticalApertureBoundaryAtom h a t p) := by
  have hratio := norm_suzukiCriticalApertureDepthRatio_lt_one hh ha t p
  refine ((summable_geometric_of_norm_lt_one hratio).mul_left
    (suzukiCriticalApertureBoundaryAtom h a t p 0)).congr ?_
  intro e
  exact (suzukiCriticalApertureBoundaryAtom_eq_base_mul_ratio_pow h a t p e).symm

/-- **Exact critical depth resolvent.** The distributional boundary/innovation pairing completes
before any Hilbert square is formed. -/
theorem tsum_suzukiCriticalApertureBoundaryAtom_eq_resolvent
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    (∑' e : ℕ, suzukiCriticalApertureBoundaryAtom h a t p e) =
      suzukiCriticalApertureBoundaryAtom h a t p 0 *
        (1 - suzukiCriticalApertureDepthRatio h a t p)⁻¹ := by
  rw [show (∑' e : ℕ, suzukiCriticalApertureBoundaryAtom h a t p e) =
      ∑' e : ℕ, suzukiCriticalApertureBoundaryAtom h a t p 0 *
        suzukiCriticalApertureDepthRatio h a t p ^ e by
      apply tsum_congr
      exact suzukiCriticalApertureBoundaryAtom_eq_base_mul_ratio_pow h a t p]
  rw [tsum_mul_left]
  rw [tsum_geometric_of_norm_lt_one
    (norm_suzukiCriticalApertureDepthRatio_lt_one hh ha t p)]

end

end RHTower
