import GaloisForLFunctions.RHTower.Sieve.SqrtLogDecayIntegral

/-!
# The prime counting function with a square-root-logarithmic error term

Partial summation turns `θ` into `π`:

```text
π(x) = θ(x)/log x + ∫_2^x θ(t)/(t log²t) dt,
```

and the main term reassembles into the logarithmic integral,

```text
2/log 2 + ∫_2^x dt/log t = x/log x + ∫_2^x dt/log²t .
```

Writing `θ(t) = t(1 + f(t))` the two error contributions are `x f(x)/log x`, which is smaller than
`θ(x) − x` itself, and `∫_2^x f(t)/log²t dt`, which the split at `√x` bounds by
`x·exp(−(c/2)√(log x))`.  So `π` inherits the error term of `θ`, with the exponent unchanged and
the constant halved.
-/

namespace RHTower.Sieve

open Filter Topology Asymptotics MeasureTheory Set

/-- `1/log²t ≤ 3` on `[2,∞)`. -/
theorem inv_log_sq_le_three {t : ℝ} (ht : 2 ≤ t) : (Real.log t ^ 2)⁻¹ ≤ 3 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hmono : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hge : (1 : ℝ) / 3 ≤ Real.log t ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < Real.log t ^ 2 := by linarith
  have hinv : (0 : ℝ) < (Real.log t ^ 2)⁻¹ := inv_pos.mpr hpos
  have hcancel : (Real.log t ^ 2)⁻¹ * Real.log t ^ 2 = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  nlinarith [mul_nonneg hinv.le (show (0 : ℝ) ≤ Real.log t ^ 2 - 1 / 3 by linarith)]

/-- The weight `1/log²t` is continuous on `[2,x]`. -/
theorem continuousOn_inv_log_sq {x : ℝ} :
    ContinuousOn (fun t : ℝ => (Real.log t ^ 2)⁻¹) (Set.Icc 2 x) := by
  refine ContinuousOn.inv₀ (ContinuousOn.pow (Real.continuousOn_log.mono ?_) 2) ?_
  · intro t ht
    have : (2 : ℝ) ≤ t := ht.1
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  · intro t ht
    have h2 : (2 : ℝ) ≤ t := ht.1
    have hpos : (0 : ℝ) < Real.log t ^ 2 := by
      have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hmono : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) h2
      nlinarith
    exact ne_of_gt hpos

/-- **The prime number theorem for `π` with a square-root-logarithmic error term.**  The
comparison function is the logarithmic integral `∫_2^x dt/log t`. -/
theorem primeCounting_sub_logIntegral_isBigO :
    ∃ c > 0, (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in Set.Icc 2 x, (Real.log t)⁻¹)
      =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨f, -, f_int, hf'⟩ := chebyshev_asymptotic''
  obtain ⟨c, hc0, hθ⟩ := chebyshevTheta_sub_id_isBigO
  rw [Asymptotics.isBigO_iff] at hθ
  obtain ⟨K, hK⟩ := hθ
  -- the relative error of `θ` decays
  have hfbd : ∀ᶠ t : ℝ in atTop, |f t| ≤ |K| * Real.exp (-c * Real.sqrt (Real.log t)) := by
    filter_upwards [hK, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have hgn : ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖
        = t * Real.exp (-c * Real.sqrt (Real.log t)) := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hgn, hf' t ht0] at ht
    have habs : |t + t * f t - t| = t * |f t| := by
      rw [show t + t * f t - t = t * f t by ring, abs_mul, abs_of_pos ht0]
    rw [habs] at ht
    have htE : (0 : ℝ) ≤ t * Real.exp (-c * Real.sqrt (Real.log t)) := by positivity
    have hgap : (0 : ℝ) ≤ (|K| - K) * (t * Real.exp (-c * Real.sqrt (Real.log t))) :=
      mul_nonneg (by linarith [le_abs_self K]) htE
    have hstep : t * |f t| ≤ t * (|K| * Real.exp (-c * Real.sqrt (Real.log t))) := by
      nlinarith [ht, hgap]
    exact le_of_mul_le_mul_left hstep ht0
  -- the integrand of the error integral
  have hFint : ∀ y : ℝ, 2 ≤ y →
      IntegrableOn (fun t : ℝ => f t * (Real.log t ^ 2)⁻¹) (Set.Icc 2 y) :=
    fun y hy => (f_int y hy).mul_continuousOn continuousOn_inv_log_sq isCompact_Icc
  have hFbd : ∀ᶠ t : ℝ in atTop,
      |f t * (Real.log t ^ 2)⁻¹| ≤ (3 * |K|) * Real.exp (-c * Real.sqrt (Real.log t)) := by
    filter_upwards [hfbd, eventually_ge_atTop (2 : ℝ)] with t ht ht2
    have hpos : (0 : ℝ) < Real.log t ^ 2 := by
      have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hmono : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
      nlinarith
    have hinv : (0 : ℝ) < (Real.log t ^ 2)⁻¹ := inv_pos.mpr hpos
    rw [abs_mul, abs_of_pos hinv]
    have h3 := inv_log_sq_le_three ht2
    have hE : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log t)) := Real.exp_pos _
    nlinarith [abs_nonneg (f t), abs_nonneg K, ht]
  obtain ⟨C, hC0, hCbd⟩ :=
    exists_bound_setIntegral_sqrt_log_decay hc0 (by positivity : (0 : ℝ) ≤ 3 * |K|) hFint hFbd
  -- the partial-summation identity
  have key : ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in Set.Icc 2 x, (Real.log t)⁻¹
        = (Real.log 2)⁻¹ * 2 + (Real.log x)⁻¹ * (x * f x)
          + ∫ t in Set.Icc 2 x, f t * (Real.log t ^ 2)⁻¹ := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hI1 : IntegrableOn (fun t : ℝ => (Real.log t ^ 2)⁻¹) (Set.Icc 2 x) :=
      continuousOn_inv_log_sq.integrableOn_Icc
    have hsplit : ∫ t in Set.Icc 2 x, Chebyshev.theta t * (t * Real.log t ^ 2)⁻¹
        = (∫ t in Set.Icc 2 x, (Real.log t ^ 2)⁻¹)
          + ∫ t in Set.Icc 2 x, f t * (Real.log t ^ 2)⁻¹ := by
      rw [← MeasureTheory.integral_add hI1 (hFint x hx)]
      refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
      have ht2 : (2 : ℝ) ≤ t := ht.1
      have htne : (t : ℝ) ≠ 0 := by positivity
      have hlogne : Real.log t ≠ 0 := by
        have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        have hmono : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
        exact ne_of_gt (by linarith)
      rw [hf' t (by linarith)]
      field_simp
    have hpi := pi_asymp_aux x hx
    have hexp : (Real.log x)⁻¹ * (x + x * f x)
        = (Real.log x)⁻¹ * x + (Real.log x)⁻¹ * (x * f x) := by ring
    rw [hpi, hsplit, hf' x hx0, hexp]
    linarith [integral_log_inv'' 2 x le_rfl hx]
  refine ⟨c / 2, by linarith, Asymptotics.IsBigO.of_bound (3 + |K| + C) ?_⟩
  filter_upwards [key, hCbd, sqrt_mul_log_le_shape (show (0 : ℝ) < c / 2 by linarith), hfbd,
    eventually_ge_atTop (3 : ℝ)] with x hkey hCx hshape hfx hx3
  have hx0 : (0 : ℝ) < x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsxge : (1 : ℝ) ≤ Real.sqrt x := by nlinarith
  have hbig : (1 : ℝ) ≤ 2 * Real.sqrt x * Real.log x := by nlinarith
  set E : ℝ := Real.exp (-(c / 2) * Real.sqrt (Real.log x)) with hE
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hone : (1 : ℝ) ≤ x * E := by linarith [hshape, hbig]
  have hgn : ‖x * E‖ = x * E := by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  -- the three contributions
  have hconst : |(Real.log 2)⁻¹ * 2| ≤ 3 * (x * E) := by
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hpos : (0 : ℝ) < (Real.log 2)⁻¹ := inv_pos.mpr (by linarith)
    have hcancel : (Real.log 2)⁻¹ * Real.log 2 = 1 := inv_mul_cancel₀ (by linarith)
    have hle : (Real.log 2)⁻¹ ≤ 3 / 2 := by
      nlinarith [mul_nonneg hpos.le (show (0 : ℝ) ≤ Real.log 2 - 2 / 3 by linarith)]
    rw [abs_of_pos (by linarith)]
    nlinarith
  have hmain : |(Real.log x)⁻¹ * (x * f x)| ≤ |K| * (x * E) := by
    have hlinv : (0 : ℝ) < (Real.log x)⁻¹ := inv_pos.mpr (by linarith)
    have hlinv1 : (Real.log x)⁻¹ ≤ 1 := by
      have hcancel : (Real.log x)⁻¹ * Real.log x = 1 := inv_mul_cancel₀ (by linarith)
      nlinarith [mul_nonneg hlinv.le (show (0 : ℝ) ≤ Real.log x - 1 by linarith)]
    have hexpmono : Real.exp (-c * Real.sqrt (Real.log x)) ≤ E := by
      refine Real.exp_le_exp.mpr ?_
      have : (0 : ℝ) ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
      nlinarith
    have hA0 : (0 : ℝ) ≤ x * |f x| := mul_nonneg hx0.le (abs_nonneg _)
    have hstep : x * |f x| ≤ |K| * (x * E) := by
      have h1 : x * |f x| ≤ x * (|K| * Real.exp (-c * Real.sqrt (Real.log x))) :=
        mul_le_mul_of_nonneg_left hfx hx0.le
      have h2 : x * (|K| * Real.exp (-c * Real.sqrt (Real.log x))) ≤ x * (|K| * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpmono (abs_nonneg K)) hx0.le
      have h3 : x * (|K| * E) = |K| * (x * E) := by ring
      linarith
    rw [abs_mul, abs_of_pos hlinv, abs_mul, abs_of_pos hx0]
    calc (Real.log x)⁻¹ * (x * |f x|) ≤ 1 * (x * |f x|) :=
          mul_le_mul_of_nonneg_right hlinv1 hA0
      _ = x * |f x| := one_mul _
      _ ≤ |K| * (x * E) := hstep
  rw [hgn, Real.norm_eq_abs, hkey]
  have htri1 := abs_add_le ((Real.log 2)⁻¹ * 2 + (Real.log x)⁻¹ * (x * f x))
    (∫ t in Set.Icc 2 x, f t * (Real.log t ^ 2)⁻¹)
  have htri2 := abs_add_le ((Real.log 2)⁻¹ * 2) ((Real.log x)⁻¹ * (x * f x))
  have hCle : |∫ t in Set.Icc 2 x, f t * (Real.log t ^ 2)⁻¹| ≤ C * (x * E) := hCx
  have hexpand : (3 + |K| + C) * (x * E) = 3 * (x * E) + |K| * (x * E) + C * (x * E) := by ring
  linarith [htri1, htri2, hconst, hmain, hCle, hexpand]

end RHTower.Sieve
