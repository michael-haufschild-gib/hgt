import GaloisForLFunctions.RHTower.ProlateGaussianTrial
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Gaussian trial profile beats the half separation threshold

The shifted Rayleigh integrand of the Gaussian trial profile is positive on the concentration
scale `|x| ≤ c^{-1/2}`, still nonnegative up to `|x| ≤ 2^{-1/2}`, and exponentially small in the
remaining edge layer.  Adding the three contributions shows the total integral is positive once the
bandwidth is large, i.e.

```text
∫_{-1}^{1} (L_c v)(x) v(x) dx  >  -(c²/2) ∫_{-1}^{1} v(x)² dx,      v(x) = exp(-c x²/2).
```
-/

noncomputable section

open Real MeasureTheory intervalIntegral Set

namespace RHTower

/-- On the concentration scale the shifted integrand is bounded below by `c²/(4e)`. -/
theorem gaussianTrialIntegrand_ge_center {c : ℝ} (hc : 400 ≤ c) {x : ℝ} (hx : x ^ (2 : ℕ) ≤ 1 / c) :
    c ^ (2 : ℕ) / 4 * Real.exp (-1) ≤ gaussianTrialIntegrand c x := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hx0 : (0 : ℝ) ≤ x ^ (2 : ℕ) := sq_nonneg x
  have hcx : c * x ^ (2 : ℕ) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hx hc0.le
    rwa [mul_one_div, div_self hc0.ne'] at this
  have hquart : c ^ (2 : ℕ) * x ^ (4 : ℕ) ≤ 1 := by
    have hsq : (x ^ (2 : ℕ)) ^ (2 : ℕ) ≤ (1 / c) ^ (2 : ℕ) := by nlinarith
    have : c ^ (2 : ℕ) * (x ^ (2 : ℕ)) ^ (2 : ℕ) ≤ c ^ (2 : ℕ) * (1 / c) ^ (2 : ℕ) := by nlinarith [sq_nonneg c]
    calc c ^ (2 : ℕ) * x ^ (4 : ℕ) = c ^ (2 : ℕ) * (x ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ c ^ (2 : ℕ) * (1 / c) ^ (2 : ℕ) := this
      _ = 1 := by field_simp
  have hP : c ^ (2 : ℕ) / 4 ≤ c ^ (2 : ℕ) / 2 - c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ) := by
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hc0.le) hx0]
  have hP0 : (0 : ℝ) ≤ c ^ (2 : ℕ) / 4 := by positivity
  have hexp : Real.exp (-1) ≤ Real.exp (-(c * x ^ (2 : ℕ))) := Real.exp_le_exp.mpr (by linarith)
  rw [gaussianTrialIntegrand]
  calc c ^ (2 : ℕ) / 4 * Real.exp (-1)
      ≤ (c ^ (2 : ℕ) / 2 - c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ)) * Real.exp (-1) :=
        mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
    _ ≤ (c ^ (2 : ℕ) / 2 - c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ)) * Real.exp (-(c * x ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hexp (le_trans hP0 hP)

/-- Inside the half-width annulus the shifted integrand stays nonnegative. -/
theorem gaussianTrialIntegrand_nonneg_annulus {c : ℝ} (hc : 400 ≤ c) {x : ℝ}
    (hx : x ^ (2 : ℕ) ≤ 1 / 2) : 0 ≤ gaussianTrialIntegrand c x := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hx0 : (0 : ℝ) ≤ x ^ (2 : ℕ) := sq_nonneg x
  have hquart : c ^ (2 : ℕ) * x ^ (4 : ℕ) ≤ c ^ (2 : ℕ) / 4 := by
    have hsq : (x ^ (2 : ℕ)) ^ (2 : ℕ) ≤ (1 / 2 : ℝ) ^ (2 : ℕ) := by nlinarith
    calc c ^ (2 : ℕ) * x ^ (4 : ℕ) = c ^ (2 : ℕ) * (x ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ c ^ (2 : ℕ) * (1 / 2 : ℝ) ^ (2 : ℕ) := by nlinarith [sq_nonneg c]
      _ = c ^ (2 : ℕ) / 4 := by ring
  have hP : (0 : ℝ) ≤ c ^ (2 : ℕ) / 2 - c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ) := by
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hc0.le) hx0]
  rw [gaussianTrialIntegrand]
  exact mul_nonneg hP (Real.exp_pos _).le

/-- In the edge layer the shifted integrand is bounded below by an exponentially small amount. -/
theorem gaussianTrialIntegrand_ge_edge {c : ℝ} (hc : 400 ≤ c) {x : ℝ}
    (hx1 : 1 / 2 ≤ x ^ (2 : ℕ)) (hx2 : x ^ (2 : ℕ) ≤ 1) :
    -((c + c ^ (2 : ℕ)) * Real.exp (-(c / 2))) ≤ gaussianTrialIntegrand c x := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hx0 : (0 : ℝ) ≤ x ^ (2 : ℕ) := sq_nonneg x
  set P : ℝ := c ^ (2 : ℕ) / 2 - c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ) with hPdef
  have hquart : c ^ (2 : ℕ) * x ^ (4 : ℕ) ≤ c ^ (2 : ℕ) := by
    have : (x ^ (2 : ℕ)) ^ (2 : ℕ) ≤ 1 := by nlinarith
    calc c ^ (2 : ℕ) * x ^ (4 : ℕ) = c ^ (2 : ℕ) * (x ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ c ^ (2 : ℕ) * 1 := by nlinarith [sq_nonneg c]
      _ = c ^ (2 : ℕ) := by ring
  have hPlow : -(c + c ^ (2 : ℕ)) ≤ P := by
    rw [hPdef]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hc0.le) hx0, sq_nonneg c]
  have hexpsmall : Real.exp (-(c * x ^ (2 : ℕ))) ≤ Real.exp (-(c / 2)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hexppos : (0 : ℝ) < Real.exp (-(c * x ^ (2 : ℕ))) := Real.exp_pos _
  have hconstnn : (0 : ℝ) ≤ (c + c ^ (2 : ℕ)) * Real.exp (-(c / 2)) := by positivity
  rw [gaussianTrialIntegrand, ← hPdef]
  by_cases hP0 : 0 ≤ P
  · exact le_trans (by linarith) (mul_nonneg hP0 hexppos.le)
  · replace hP0 : P < 0 := not_le.mp hP0
    calc -((c + c ^ (2 : ℕ)) * Real.exp (-(c / 2)))
        = -(c + c ^ (2 : ℕ)) * Real.exp (-(c / 2)) := by ring
      _ ≤ P * Real.exp (-(c / 2)) := mul_le_mul_of_nonneg_right hPlow (Real.exp_pos _).le
      _ ≤ P * Real.exp (-(c * x ^ (2 : ℕ))) := by
          have := mul_le_mul_of_nonpos_left hexpsmall hP0.le
          linarith [this]

/-- Exponential domination of the edge defect by the concentrated core. -/
theorem edge_defect_lt_core {c : ℝ} (hc : 400 ≤ c) :
    2 * ((c + c ^ (2 : ℕ)) * Real.exp (-(c / 2))) < c / (2 * Real.exp 1) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hquarter : c / 4 + 1 ≤ Real.exp (c / 4) := by
    have := Real.add_one_le_exp (c / 4)
    linarith
  have hhalf : (c / 4 + 1) ^ (2 : ℕ) ≤ Real.exp (c / 2) := by
    have hexp : Real.exp (c / 4) ^ (2 : ℕ) = Real.exp (c / 2) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.exp_pos (c / 4)]
  have he1 : Real.exp 1 < 3 := by
    exact Real.exp_one_lt_three
  have he1pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hE : (0 : ℝ) < Real.exp (c / 2) := Real.exp_pos _
  have hE1 : (0 : ℝ) < 2 * Real.exp 1 := by positivity
  have hkey : 2 * (c + c ^ (2 : ℕ)) * (2 * Real.exp 1) < c * Real.exp (c / 2) := by
    have hstep1 : 2 * (c + c ^ (2 : ℕ)) * (2 * Real.exp 1) < 12 * (c + c ^ (2 : ℕ)) := by nlinarith
    have hstep2 : 12 * (c + c ^ (2 : ℕ)) ≤ c * (c / 4 + 1) ^ (2 : ℕ) := by nlinarith
    have hstep3 : c * (c / 4 + 1) ^ (2 : ℕ) ≤ c * Real.exp (c / 2) := by nlinarith
    linarith
  rw [lt_div_iff₀ hE1]
  have hA : 2 * ((c + c ^ (2 : ℕ)) * Real.exp (-(c / 2))) * (2 * Real.exp 1)
      = 2 * (c + c ^ (2 : ℕ)) * (2 * Real.exp 1) / Real.exp (c / 2) := by
    rw [Real.exp_neg]
    field_simp
  rw [hA, div_lt_iff₀ hE]
  linarith [hkey]

/-- **The Gaussian trial profile is a strict witness.**  Its shifted Rayleigh integral is positive
at every large bandwidth. -/
theorem integral_gaussianTrialIntegrand_pos {c : ℝ} (hc : 400 ≤ c) :
    0 < ∫ x in (-1 : ℝ)..1, gaussianTrialIntegrand c x := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hcont : Continuous (gaussianTrialIntegrand c) := continuous_gaussianTrialIntegrand c
  have hint : ∀ u v : ℝ, IntervalIntegrable (gaussianTrialIntegrand c) volume u v :=
    fun u v => hcont.intervalIntegrable u v
  set r0 : ℝ := 1 / Real.sqrt 2 with hr0def
  set r1 : ℝ := 1 / Real.sqrt c with hr1def
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hr0pos : (0 : ℝ) < r0 := by rw [hr0def]; positivity
  have hr1pos : (0 : ℝ) < r1 := by rw [hr1def]; positivity
  have hr0sq : r0 ^ (2 : ℕ) = 1 / 2 := by
    rw [hr0def, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hr1sq : r1 ^ (2 : ℕ) = 1 / c := by
    rw [hr1def, div_pow, one_pow, Real.sq_sqrt hc0.le]
  have hr0lt1 : r0 < 1 := by nlinarith [hr0sq, hr0pos]
  have hr1ler0 : r1 ≤ r0 := by
    rw [hr1def, hr0def]
    exact one_div_le_one_div_of_le hs2 (Real.sqrt_le_sqrt (by linarith))
  -- the three pointwise regimes
  have hcenter : ∀ x ∈ Set.Icc (-r1) r1, c ^ (2 : ℕ) / 4 * Real.exp (-1) ≤ gaussianTrialIntegrand c x := by
    intro x hx
    refine gaussianTrialIntegrand_ge_center hc ?_
    rw [← hr1sq]
    nlinarith [hx.1, hx.2, hr1pos]
  have hann : ∀ x : ℝ, -r0 ≤ x → x ≤ r0 → 0 ≤ gaussianTrialIntegrand c x := by
    intro x h1 h2
    refine gaussianTrialIntegrand_nonneg_annulus hc ?_
    rw [← hr0sq]
    nlinarith [hr0pos]
  have hedge : ∀ x : ℝ, r0 ≤ |x| → |x| ≤ 1 →
      -((c + c ^ (2 : ℕ)) * Real.exp (-(c / 2))) ≤ gaussianTrialIntegrand c x := by
    intro x h1 h2
    refine gaussianTrialIntegrand_ge_edge hc ?_ ?_
    · rw [← hr0sq, ← sq_abs x]
      nlinarith [hr0pos, abs_nonneg x]
    · rw [← sq_abs x]
      nlinarith [abs_nonneg x]
  set K : ℝ := (c + c ^ (2 : ℕ)) * Real.exp (-(c / 2)) with hKdef
  have hKnn : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  -- the five pieces
  have hI1 : -K ≤ ∫ x in (-1 : ℝ)..(-r0), gaussianTrialIntegrand c x := by
    have hle : (-1 : ℝ) ≤ -r0 := by linarith
    have hmono := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_const (c := -K)) (hint (-1) (-r0)) ?_
    · have hconst : (∫ _x in (-1 : ℝ)..(-r0), (-K : ℝ)) = (-r0 - (-1)) * (-K) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      rw [hconst] at hmono
      nlinarith [hmono, hKnn, hr0pos, hr0lt1]
    · intro x hx
      refine hedge x ?_ ?_
      · rw [abs_of_nonpos (by linarith [hx.2, hr0pos] : x ≤ 0)]
        linarith [hx.2]
      · rw [abs_of_nonpos (by linarith [hx.2, hr0pos] : x ≤ 0)]
        linarith [hx.1]
  have hI5 : -K ≤ ∫ x in (r0 : ℝ)..1, gaussianTrialIntegrand c x := by
    have hle : (r0 : ℝ) ≤ 1 := hr0lt1.le
    have hmono := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_const (c := -K)) (hint r0 1) ?_
    · have hconst : (∫ _x in (r0 : ℝ)..1, (-K : ℝ)) = (1 - r0) * (-K) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      rw [hconst] at hmono
      nlinarith [hmono, hKnn, hr0pos, hr0lt1]
    · intro x hx
      refine hedge x ?_ ?_
      · rw [abs_of_nonneg (by linarith [hx.1, hr0pos] : (0:ℝ) ≤ x)]
        linarith [hx.1]
      · rw [abs_of_nonneg (by linarith [hx.1, hr0pos] : (0:ℝ) ≤ x)]
        linarith [hx.2]
  have hI2 : (0 : ℝ) ≤ ∫ x in (-r0 : ℝ)..(-r1), gaussianTrialIntegrand c x := by
    refine intervalIntegral.integral_nonneg (by linarith) ?_
    intro x hx
    exact hann x hx.1 (by linarith [hx.2, hr1ler0])
  have hI4 : (0 : ℝ) ≤ ∫ x in (r1 : ℝ)..r0, gaussianTrialIntegrand c x := by
    refine intervalIntegral.integral_nonneg hr1ler0 ?_
    intro x hx
    exact hann x (by linarith [hx.1, hr1pos, hr0pos]) hx.2
  have hI3 : 2 * r1 * (c ^ (2 : ℕ) / 4 * Real.exp (-1))
      ≤ ∫ x in (-r1 : ℝ)..r1, gaussianTrialIntegrand c x := by
    have hle : (-r1 : ℝ) ≤ r1 := by linarith
    have hmono := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_const (c := c ^ (2 : ℕ) / 4 * Real.exp (-1))) (hint (-r1) r1) hcenter
    have hconst : (∫ _x in (-r1 : ℝ)..r1, (c ^ (2 : ℕ) / 4 * Real.exp (-1) : ℝ))
        = (r1 - (-r1)) * (c ^ (2 : ℕ) / 4 * Real.exp (-1)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [hconst] at hmono
    calc 2 * r1 * (c ^ (2 : ℕ) / 4 * Real.exp (-1))
        = (r1 - (-r1)) * (c ^ (2 : ℕ) / 4 * Real.exp (-1)) := by ring
      _ ≤ _ := hmono
  -- gluing
  have hsplit : (∫ x in (-1 : ℝ)..1, gaussianTrialIntegrand c x)
      = (∫ x in (-1 : ℝ)..(-r0), gaussianTrialIntegrand c x)
        + (∫ x in (-r0 : ℝ)..(-r1), gaussianTrialIntegrand c x)
        + (∫ x in (-r1 : ℝ)..r1, gaussianTrialIntegrand c x)
        + (∫ x in (r1 : ℝ)..r0, gaussianTrialIntegrand c x)
        + (∫ x in (r0 : ℝ)..1, gaussianTrialIntegrand c x) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint (-1) (-r0)) (hint (-r0) (-r1)),
      intervalIntegral.integral_add_adjacent_intervals
        ((hint (-1) (-r0)).trans (hint (-r0) (-r1))) (hint (-r1) r1),
      intervalIntegral.integral_add_adjacent_intervals
        (((hint (-1) (-r0)).trans (hint (-r0) (-r1))).trans (hint (-r1) r1)) (hint r1 r0),
      intervalIntegral.integral_add_adjacent_intervals
        ((((hint (-1) (-r0)).trans (hint (-r0) (-r1))).trans (hint (-r1) r1)).trans (hint r1 r0))
        (hint r0 1)]
  -- the core beats the edge defect
  have hr1lower : 1 / c ≤ r1 := by
    have hsqge1 : (1 : ℝ) ≤ Real.sqrt c := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsqle : Real.sqrt c ≤ c := by
      have hmul := Real.mul_self_sqrt hc0.le
      nlinarith [hsqge1, hsc]
    rw [hr1def]
    exact one_div_le_one_div_of_le hsc hsqle
  have hcore : c / (2 * Real.exp 1) ≤ 2 * r1 * (c ^ (2 : ℕ) / 4 * Real.exp (-1)) := by
    have hexpinv : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
    have hbase : 2 * (1 / c) * (c ^ (2 : ℕ) / 4 * Real.exp (-1)) = c / (2 * Real.exp 1) := by
      rw [hexpinv]
      field_simp
      ring
    have hstep : 2 * (1 / c) * (c ^ (2 : ℕ) / 4 * Real.exp (-1))
        ≤ 2 * r1 * (c ^ (2 : ℕ) / 4 * Real.exp (-1)) := by
      have hnn : (0 : ℝ) ≤ c ^ (2 : ℕ) / 4 * Real.exp (-1) := by positivity
      nlinarith [hr1lower, hnn]
    linarith [hbase, hstep]
  have hdefect := edge_defect_lt_core hc
  rw [hsplit]
  nlinarith [hI1, hI2, hI3, hI4, hI5, hcore, hdefect]

/-- **The Gaussian Rayleigh quotient is above the half threshold.**  For every large bandwidth the
prolate action of the Gaussian trial profile pairs against the profile strictly above
`-(c²/2)` times its squared mass. -/
theorem prolate_gaussian_rayleigh_gt {c : ℝ} (hc : 400 ≤ c) :
    -(c ^ (2 : ℕ) / 2) * (∫ x in (-1 : ℝ)..1, gaussianTrial c x * gaussianTrial c x)
      < ∫ x in (-1 : ℝ)..1, prolateSLAction c (gaussianTrial c) x * gaussianTrial c x := by
  have hv : Continuous (gaussianTrial c) := continuous_gaussianTrial c
  have hL : Continuous fun x : ℝ => prolateSLAction c (gaussianTrial c) x * gaussianTrial c x := by
    have hLc : Continuous fun x : ℝ => prolateSLAction c (gaussianTrial c) x := by
      have := prolateSLAction_gaussianTrial c
      have hfun : (fun x : ℝ => prolateSLAction c (gaussianTrial c) x)
          = fun x : ℝ => (-c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ)) * gaussianTrial c x :=
        funext (prolateSLAction_gaussianTrial c)
      rw [hfun]
      exact (by fun_prop : Continuous fun x : ℝ => (-c + 3 * c * x ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (4 : ℕ))).mul hv
    exact hLc.mul hv
  have hsq : Continuous fun x : ℝ => gaussianTrial c x * gaussianTrial c x := hv.mul hv
  have hadd : (∫ x in (-1 : ℝ)..1, prolateSLAction c (gaussianTrial c) x * gaussianTrial c x)
      + (∫ x in (-1 : ℝ)..1, c ^ (2 : ℕ) / 2 * (gaussianTrial c x * gaussianTrial c x))
      = ∫ x in (-1 : ℝ)..1, gaussianTrialIntegrand c x := by
    rw [← intervalIntegral.integral_add (hL.intervalIntegrable _ _)
      ((hsq.const_mul (c ^ (2 : ℕ) / 2)).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun x _ => prolate_gaussian_rayleigh_integrand c x
  have hconstmul : (∫ x in (-1 : ℝ)..1, c ^ (2 : ℕ) / 2 * (gaussianTrial c x * gaussianTrial c x))
      = c ^ (2 : ℕ) / 2 * ∫ x in (-1 : ℝ)..1, gaussianTrial c x * gaussianTrial c x :=
    intervalIntegral.integral_const_mul _ _
  have hpos := integral_gaussianTrialIntegrand_pos hc
  rw [hconstmul] at hadd
  linarith [hadd, hpos]

end RHTower
