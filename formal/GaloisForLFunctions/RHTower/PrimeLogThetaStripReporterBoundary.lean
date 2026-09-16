import GaloisForLFunctions.RHTower.PrimeLogThetaStripWronskianCubicJet

/-!
# Sharp source-reporter boundary for the literal prime-log theta transform

The finite theta transform has literal prime coefficient

```text
2 log(p)^2 / sqrt(p) * exp(-i w log(p)).
```

This file determines its source-Hilbert status at the relevant boundary.  On the lower
imaginary ray `w = -i t`, `t > 0`, this coefficient is exactly `t⁻¹` times the existing
critical-Laplace evaluation vector, hence is an honest source `ℓ²` reporter.  On every real
coordinate, its squared norm is `4 log(p)^4 / p`; prime-reciprocal divergence therefore proves
that it is not a source `ℓ²` vector.

Thus ordinary source-vector evaluation has a sharp boundary at the real theta axis.  This does
not rule out the required `Graph(cl A_*)` construction: it identifies why that construction must
be genuinely graph-relative and cannot be replaced by an ordinary bounded source reporter at the
axis containing the critical-line Xi coordinates.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

private theorem not_summable_primeLogFourth_div :
    ¬ Summable (fun p : Nat.Primes => Real.log (p : ℝ) ^ 4 / (p : ℝ)) := by
  intro hsum
  let a : ℝ := Real.log 2
  have ha_pos : 0 < a := by
    dsimp [a]
    exact Real.log_pos (by norm_num)
  have ha_pow_ne : a ^ 4 ≠ 0 := pow_ne_zero 4 ha_pos.ne'
  have hscaled : Summable (fun p : Nat.Primes => (a ^ 4)⁻¹ *
      (Real.log (p : ℝ) ^ 4 / (p : ℝ))) := hsum.mul_left _
  apply Nat.Primes.not_summable_one_div
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hscaled
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hlog : a ≤ Real.log (p : ℝ) := by
    dsimp [a]
    exact Real.log_le_log (by norm_num) hp2
  have hpow : a ^ 4 ≤ Real.log (p : ℝ) ^ 4 := by gcongr
  calc
    1 / (p : ℝ) = (a ^ 4)⁻¹ * (a ^ 4 / (p : ℝ)) := by
      field_simp [ha_pow_ne]
    _ ≤ (a ^ 4)⁻¹ * (Real.log (p : ℝ) ^ 4 / (p : ℝ)) := by
      gcongr

/-- Literal theta evaluation coefficient on the real theta axis. -/
def primeLogThetaStripRealAxisReporter (x : ℝ) (p : Nat.Primes) : ℂ :=
  primeLogThetaStripCoefficient p *
    Complex.exp (-I * (x : ℂ) * (Real.log (p : ℝ) : ℂ))

/-- Exact squared coefficient mass on the real theta axis. -/
theorem norm_sq_primeLogThetaStripRealAxisReporter
    (x : ℝ) (p : Nat.Primes) :
    ‖primeLogThetaStripRealAxisReporter x p‖ ^ 2 =
      4 * Real.log (p : ℝ) ^ 4 / (p : ℝ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hcoeff_pos : 0 < 2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) := by
    positivity
  have hsqrt : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  unfold primeLogThetaStripRealAxisReporter primeLogThetaStripCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcoeff_pos,
    Complex.norm_exp]
  have hre : (-I * (x : ℂ) * (Real.log (p : ℝ) : ℂ)).re = 0 := by
    have hleft : (-I * (x : ℂ)).re = 0 := by
      rw [Complex.mul_re]
      norm_num
    have hright : (Real.log (p : ℝ) : ℂ).im = 0 := by rfl
    rw [Complex.mul_re, hleft, hright]
    ring
  rw [hre, Real.exp_zero, mul_one]
  field_simp [hsqrt]
  rw [Real.sq_sqrt hp.le]
  ring

/-- Real-axis literal theta evaluation coefficients are not square-summable over primes. -/
theorem not_summable_norm_sq_primeLogThetaStripRealAxisReporter (x : ℝ) :
    ¬ Summable (fun p : Nat.Primes => ‖primeLogThetaStripRealAxisReporter x p‖ ^ 2) := by
  intro hsum
  apply not_summable_primeLogFourth_div
  have hfour : Summable (fun p : Nat.Primes =>
      4 * (Real.log (p : ℝ) ^ 4 / (p : ℝ))) :=
    hsum.congr (fun p =>
      (norm_sq_primeLogThetaStripRealAxisReporter x p).trans (by ring))
  exact (summable_mul_left_iff (by norm_num : (4 : ℝ) ≠ 0)).mp hfour

/-- There is no real-axis literal theta point-evaluation vector in the completed source Hilbert
space. -/
theorem not_memℓp_primeLogThetaStripRealAxisReporter (x : ℝ) :
    ¬ Memℓp (primeLogThetaStripRealAxisReporter x) 2 := by
  intro hmem
  apply not_summable_norm_sq_primeLogThetaStripRealAxisReporter x
  have hsum := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp hmem
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsum

/-- No vector of the completed source Hilbert space represents literal real-axis theta
evaluation coefficientwise. -/
theorem no_sourceReporter_primeLogThetaStripRealAxis (x : ℝ) :
    ¬ ∃ v : primeLogCriticalSourceL2,
      ∀ p : Nat.Primes, (v : Nat.Primes → ℂ) p =
        primeLogThetaStripRealAxisReporter x p := by
  rintro ⟨v, hv⟩
  apply not_memℓp_primeLogThetaStripRealAxisReporter x
  have heq : v = primeLogThetaStripRealAxisReporter x := by
    funext p
    exact hv p
  rw [← heq]
  exact v.2

/-- Canonical lower-half-strip source reporter for literal theta evaluation at `w = -i t`. -/
def primeLogThetaStripLowerReporter (t : ℝ) (ht : 0 < t) : primeLogCriticalSourceL2 :=
  (t : ℂ)⁻¹ • primeLogCriticalEvaluationVector t ht

/-- The canonical lower-half-strip reporter is exactly the literal theta coefficient at
`w = -i t`, not a reweighted replacement. -/
theorem primeLogThetaStripLowerReporter_apply
    (t : ℝ) (ht : 0 < t) (p : Nat.Primes) :
    (primeLogThetaStripLowerReporter t ht : Nat.Primes → ℂ) p =
      primeLogThetaStripCoefficient p *
        Complex.exp (-I * (-I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)) := by
  change (t : ℂ)⁻¹ * primeLogCriticalLaplaceFeatureC p t = _
  rw [primeLogCriticalLaplaceFeatureC, primeLogCriticalLaplaceFeature]
  have harg : -I * (-I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ) =
      (-(Real.log (p : ℝ) * t) : ℝ) := by
    push_cast
    calc
      -I * (-I * (t : ℂ)) * Complex.log (p : ℂ) =
          ((-I) * (-I)) * (t : ℂ) * Complex.log (p : ℂ) := by ring
      _ = (-1 : ℂ) * (t : ℂ) * Complex.log (p : ℂ) := by
        rw [show (-I : ℂ) * (-I) = -1 by norm_num]
      _ = -(Complex.log (p : ℂ) * (t : ℂ)) := by ring
  rw [harg]
  rw [show Complex.exp ((-(Real.log (p : ℝ) * t) : ℝ) : ℂ) =
      (Real.exp (-(Real.log (p : ℝ) * t)) : ℂ) by
    rw [Complex.ofReal_exp]]
  unfold primeLogThetaStripCoefficient
  push_cast
  field_simp [ne_of_gt ht]

end

end RHTower
