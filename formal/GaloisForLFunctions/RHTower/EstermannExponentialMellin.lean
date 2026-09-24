import GaloisForLFunctions.RHTower.ExponentialMellinPerron
import GaloisForLFunctions.RHTower.EstermannDivisorSeries
import GaloisForLFunctions.RHTower.EstermannGrowth

/-!
# The exponentially smoothed twisted divisor sum

Applying the exponentially smoothed Perron inversion to Estermann's zeta function gives the exact
starting identity

```text
∑_{N ≥ 1} d(N) e(aN/q) e^{-N x} = (1/2π) ∫_ℝ x^{-(c+it)} Γ(c+it) D(c+it, a/q) dt     (c > 1).
```

The vertical integral converges absolutely on every line, because the Gamma factor decays like
`e^{-π|t|/2}` while `D` grows only polynomially on the closed strip.  This is the identity whose
contour is moved across `Re s = 1`, where the double pole of `D` supplies the main term.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- The divisor series converges absolutely right of the abscissa. -/
theorem summable_divisorCount_rpow {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) * (n : ℝ) ^ (-c)) := by
  have hg : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-c)) := by
    have h : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ c) := summable_shiftedPSeries hc
    refine h.congr (fun n => ?_)
    rw [Real.rpow_neg (by positivity), one_div]
  have hprod := hg.hasSum.mul hg.hasSum
    (hg.mul_of_nonneg hg (fun n => Real.rpow_nonneg (by positivity) _)
      (fun n => Real.rpow_nonneg (by positivity) _))
  have hC : HasSum (fun p : ℕ × ℕ =>
      ((((((p.1 + 1) * (p.2 + 1) : ℕ) : ℝ)) ^ (-c) : ℝ) : ℂ))
      (((∑' n : ℕ, (((n + 1 : ℕ) : ℝ)) ^ (-c)) * (∑' n : ℕ, (((n + 1 : ℕ) : ℝ)) ^ (-c)) : ℝ) : ℂ) := by
    rw [Complex.hasSum_ofReal]
    refine hprod.congr_fun (fun p => ?_)
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
  have hD := hasSum_divisorCount (F := fun N : ℕ => (((((N : ℝ)) ^ (-c) : ℝ)) : ℂ)) hC
  have hreal : Summable (fun n : ℕ => (n.divisors.card : ℝ) * (n : ℝ) ^ (-c)) := by
    rw [← Complex.summable_ofReal]
    refine hD.summable.congr (fun n => ?_)
    push_cast
    ring
  exact hreal

theorem norm_estermannCoeff {q : ℕ} [NeZero q] (a : ZMod q) (n : ℕ) :
    ‖estermannCoeff q a n‖ = (n.divisors.card : ℝ) := by
  rw [estermannCoeff, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one,
    Complex.norm_natCast]

theorem estermannCoeff_zero {q : ℕ} [NeZero q] (a : ZMod q) : estermannCoeff q a 0 = 0 := by
  simp [estermannCoeff]

/-- **The exponentially smoothed twisted divisor sum as a vertical integral.** -/
theorem estermann_exponential_mellin (q : ℕ) [NeZero q] (a : ZMod q) {c : ℝ} (hc : 1 < c)
    {x : ℝ} (hx : 0 < x) :
    mellinInv c (fun s => Complex.Gamma s * estermannZeta q a s) x
      = ∑' N : ℕ, estermannCoeff q a N * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)) := by
  have hsum : Summable (fun n : ℕ => ‖estermannCoeff q a n‖ * (n : ℝ) ^ (-c)) := by
    refine (summable_divisorCount_rpow hc).congr (fun n => ?_)
    rw [norm_estermannCoeff]
  have hbase := mellinInv_gamma_mul_LSeries_eq_tsum_exp (a := estermannCoeff q a)
    (by linarith : (0 : ℝ) < c) (estermannCoeff_zero a) hsum hx
  rw [← hbase, mellinInv, mellinInv]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
  have hL : LSeries (estermannCoeff q a) ((c : ℂ) + (t : ℂ) * I)
      = estermannZeta q a ((c : ℂ) + (t : ℂ) * I) :=
    LSeries_estermannCoeff a (by rw [hre]; exact hc)
  simp only [hL]

end

end RHTower
