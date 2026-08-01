import GaloisForLFunctions.RHTower.MobiusGammaCoPoissonPrimePowerBoundary
import GaloisForLFunctions.RHTower.PrimitiveFibreModularRenormalizationLaw

/-!
# Route E divided-log current: depth-zero reduction

Route E uses the divided-log prime-power coefficient

`(1 / (e + 1)) * p ^ (-(e + 1) / 2)`,

not the undivided von Mangoldt current.  This file compares that coefficient
exactly with the conditional Gamma valuation atom.

The comparison has two different regimes.  At depth zero its gauge is
`1 / (1 - p⁻¹)`, uniformly between one and two.  At positive depth the gauge
contains the exponentially growing factor `p ^ (e / 2) / (e + 1)`.  Thus the
beyond-finite-Rees depth singularity lives only in the higher-prime-power
sector; the literal zero/one-prime Route E seam is the uniformly bounded
depth-zero face.

No source estimate, zero hypothesis, or RH assumption occurs here.
-/

namespace RHTower

noncomputable section

/-- Half-density realization of the Route E divided-log coefficient at
valuation depth `e + 1`. -/
def routeEDividedLogHalfDensityAtom (r : ℝ) (e : ℕ) : ℝ :=
  r ^ (e + 1) / (e + 1 : ℝ)

/-- Exact gauge from the conditional Gamma valuation atom to the Route E
divided-log half-density atom. -/
def routeEDividedLogGammaGauge (r : ℝ) (e : ℕ) : ℝ :=
  (r⁻¹) ^ e / ((e + 1 : ℝ) * (1 - r ^ 2))

/-- Dividing the primitive current by its logarithmic weight and exponent
grade gives exactly the Route E half-density atom. -/
theorem routeEDividedLogHalfDensityAtom_eq_criticalCurrent_div
    {ell r : ℝ} (hell : ell ≠ 0) (e : ℕ) :
    routeEDividedLogHalfDensityAtom r e =
      primitiveFibreCriticalCurrent ell r e /
        ((e + 1 : ℝ) * ell) := by
  rw [routeEDividedLogHalfDensityAtom, primitiveFibreCriticalCurrent]
  field_simp [hell]

/-- Exact Gamma-to-Route-E factorization at every valuation depth. -/
theorem routeEDividedLogHalfDensityAtom_eq_gauge_mul_gamma
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (e : ℕ) :
    routeEDividedLogHalfDensityAtom r e =
      routeEDividedLogGammaGauge r e *
        primitiveFibreGammaAtom r e := by
  have hr : r ≠ 0 := hr0.ne'
  have hsub : 1 - r ^ 2 ≠ 0 := by nlinarith
  have he : (e + 1 : ℝ) ≠ 0 := by positivity
  simp only [routeEDividedLogHalfDensityAtom,
    routeEDividedLogGammaGauge, primitiveFibreGammaAtom]
  field_simp [hr, hsub, he]
  have hpow : (r⁻¹) ^ e * (r ^ 2) ^ e = r ^ e := by
    rw [← mul_pow]
    congr 1
    field_simp [hr]
  rw [pow_succ]
  calc
    r ^ e * r = r * r ^ e := by ring
    _ = r * ((r⁻¹) ^ e * (r ^ 2) ^ e) := by rw [hpow]
    _ = r * (1 / r) ^ e * (r ^ 2) ^ e := by
      rw [inv_eq_one_div]
      ring

/-- On a rational-prime fibre, the Route E atom is literally the critical
von Mangoldt atom divided by `log(p^(e+1))`. -/
theorem routeEDividedLogHalfDensityAtom_prime
    (p : Nat.Primes) (e : ℕ) :
    routeEDividedLogHalfDensityAtom (criticalPrimeTowerRadius p) e =
      criticalMellinAtomWeight ((p : ℕ) ^ (e + 1)) /
        ((e + 1 : ℝ) * Real.log (p : ℝ)) := by
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  rw [routeEDividedLogHalfDensityAtom,
    criticalMellinAtomWeight_prime_pow p.property (by omega)]
  field_simp [hlog]

/-- The Route E divided-log atom has no prime-scale amplification at depth
zero: it is exactly the critical square-root radius. -/
theorem routeEDividedLogHalfDensityAtom_zero (r : ℝ) :
    routeEDividedLogHalfDensityAtom r 0 = r := by
  simp [routeEDividedLogHalfDensityAtom]

/-- At depth zero the Gamma recovery gauge loses every exponential depth
factor and is just the local Euler normalization. -/
theorem routeEDividedLogGammaGauge_zero (r : ℝ) :
    routeEDividedLogGammaGauge r 0 = 1 / (1 - r ^ 2) := by
  simp [routeEDividedLogGammaGauge]

/-- On every rational-prime fibre, the hard depth-zero Route E gauge is
uniformly bounded. -/
theorem routeEDividedLogGammaGauge_prime_zero_mem_Icc
    (p : Nat.Primes) :
    routeEDividedLogGammaGauge (criticalPrimeTowerRadius p) 0 ∈
      Set.Icc (1 : ℝ) 2 := by
  have hrsq :
      criticalPrimeTowerRadius (p : ℕ) ^ 2 ≤ 1 / 2 :=
    criticalPrimeTowerRadius_sq_le_half p.property.two_le
  have hrsq0 :
      0 ≤ criticalPrimeTowerRadius (p : ℕ) ^ 2 := sq_nonneg _
  have hden :
      0 < 1 - criticalPrimeTowerRadius (p : ℕ) ^ 2 := by
    nlinarith
  rw [Set.mem_Icc, routeEDividedLogGammaGauge_zero]
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith
  · rw [div_le_iff₀ hden]
    nlinarith

/-- Exact local certificate: all depth singularity is absent on the
zero/one-prime face retained by Route E. -/
theorem routeEDividedLog_depthZero_reduction
    (p : Nat.Primes) :
    routeEDividedLogHalfDensityAtom (criticalPrimeTowerRadius p) 0 =
        criticalPrimeTowerRadius p ∧
      routeEDividedLogGammaGauge (criticalPrimeTowerRadius p) 0 ∈
        Set.Icc (1 : ℝ) 2 :=
  ⟨routeEDividedLogHalfDensityAtom_zero _,
    routeEDividedLogGammaGauge_prime_zero_mem_Icc p⟩

end

end RHTower
