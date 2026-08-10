import GaloisForLFunctions.RHTower.DeningerAbelTonelli

/-!
# All weighted moments of the pullback derivative are finite

The weighted derivative satisfies `u H_h'(u) = h'(log u)`, and the source bound at exponent `r + 2`
turns that into `u^{r+1} |H_h'(u)| ≤ C min(u^{2r+2}, u^{-2})`.  So every weighted moment

`∫_0^∞ u^{r+1} |H_h'(u)| du`

is finite, by the same two-branch comparison as the first: bounded near the origin, inverse-square
at infinity.  These are the second factors of the higher-moment estimates `(11)`.

* `deningerExpWeight_le_pow` : the exponential weight beats both powers.
* `deningerLogPullDeriv_weightedPow_norm_le` : the two-sided bound at every order.
* `deningerHigherMoment_integrable` : **every weighted moment is finite.**
-/

namespace RHTower

open SchwartzMap MeasureTheory

noncomputable section

/-- The exponential weight dominates both powers. -/
theorem deningerExpWeight_le_pow (k : ℕ) {y : ℝ} (hy : 0 < y) :
    Real.exp (-((k : ℝ) * |Real.log y|)) ≤ y ^ k ∧
      Real.exp (-((k : ℝ) * |Real.log y|)) ≤ 1 / y ^ k := by
  have hlog : Real.exp (Real.log y) = y := Real.exp_log hy
  have hpow : Real.exp ((k : ℝ) * Real.log y) = y ^ k := by
    rw [Real.exp_nat_mul, hlog]
  have hpowneg : Real.exp (-((k : ℝ) * Real.log y)) = 1 / y ^ k := by
    rw [Real.exp_neg, hpow, one_div]
  constructor
  · refine le_trans (Real.exp_le_exp.mpr ?_) (le_of_eq hpow)
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [neg_abs_le (Real.log y), abs_nonneg (Real.log y)]
  · refine le_trans (Real.exp_le_exp.mpr ?_) (le_of_eq hpowneg)
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [le_abs_self (Real.log y)]

/-- **The two-sided bound for the `r`-th weighted derivative.** -/
theorem deningerLogPullDeriv_weightedPow_norm_le {h : 𝓢(ℝ, ℂ)}
    (hh : h ∈ DeningerExpSchwartz) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y →
      y ^ (r + 1) * ‖deningerLogPullDeriv h y‖ ≤ C * y ^ (2 * r + 2) ∧
      y ^ (r + 1) * ‖deningerLogPullDeriv h y‖ ≤ C / y ^ 2 := by
  obtain ⟨C, hCnn, hC⟩ := deningerExpSchwartz_deriv_norm_le hh ((r : ℝ) + 2)
  refine ⟨C, hCnn, fun y hy => ?_⟩
  have hcancel : y * ‖deningerLogPullDeriv h y‖ = ‖deriv (h : ℝ → ℂ) (Real.log y)‖ := by
    rw [deningerLogPullDeriv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hy]
    field_simp
  have hbase : ‖deriv (h : ℝ → ℂ) (Real.log y)‖
      ≤ C * Real.exp (-(((r : ℝ) + 2) * |Real.log y|)) := by
    have hval := hC (Real.log y)
    have hepos : (0 : ℝ) < Real.exp (((r : ℝ) + 2) * |Real.log y|) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hepos]
    calc ‖deriv (h : ℝ → ℂ) (Real.log y)‖ * Real.exp (((r : ℝ) + 2) * |Real.log y|)
        = Real.exp (((r : ℝ) + 2) * |Real.log y|) * ‖deriv (h : ℝ → ℂ) (Real.log y)‖ := by ring
      _ ≤ C := hval
  have hcast : ((r + 2 : ℕ) : ℝ) = (r : ℝ) + 2 := by push_cast; ring
  obtain ⟨hup, hdown⟩ := deningerExpWeight_le_pow (r + 2) hy
  rw [hcast] at hup hdown
  have hsplit : y ^ (r + 1) * ‖deningerLogPullDeriv h y‖
      = y ^ r * (y * ‖deningerLogPullDeriv h y‖) := by
    rw [pow_succ]
    ring
  rw [hsplit, hcancel]
  have hyr : (0 : ℝ) ≤ y ^ r := pow_nonneg hy.le r
  constructor
  · have hstep : y ^ r * ‖deriv (h : ℝ → ℂ) (Real.log y)‖
        ≤ y ^ r * (C * y ^ (r + 2)) := by
      refine mul_le_mul_of_nonneg_left (le_trans hbase ?_) hyr
      exact mul_le_mul_of_nonneg_left hup hCnn
    refine le_trans hstep (le_of_eq ?_)
    rw [show 2 * r + 2 = r + (r + 2) by ring, pow_add]
    ring
  · have hstep : y ^ r * ‖deriv (h : ℝ → ℂ) (Real.log y)‖
        ≤ y ^ r * (C * (1 / y ^ (r + 2))) := by
      refine mul_le_mul_of_nonneg_left (le_trans hbase ?_) hyr
      exact mul_le_mul_of_nonneg_left hdown hCnn
    refine le_trans hstep (le_of_eq ?_)
    rw [pow_add]
    field_simp

/-- The integrand of the `r`-th weighted moment. -/
def deningerHigherMomentFun (h : 𝓢(ℝ, ℂ)) (r : ℕ) (u : ℝ) : ℝ :=
  u ^ (r + 1) * ‖deningerLogPullDeriv h u‖

theorem deningerHigherMomentFun_nonneg (h : 𝓢(ℝ, ℂ)) (r : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ deningerHigherMomentFun h r u :=
  mul_nonneg (pow_nonneg hu _) (norm_nonneg _)

theorem deningerHigherMoment_continuousOn (h : 𝓢(ℝ, ℂ)) (r : ℕ) :
    ContinuousOn (deningerHigherMomentFun h r) (Set.Ioi 0) := by
  refine ContinuousOn.mul (continuousOn_pow _) ?_
  exact ContinuousOn.norm (deningerLogPullDeriv_continuousOn h)

/-- **Every weighted moment of the pullback derivative is finite.** -/
theorem deningerHigherMoment_integrable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (r : ℕ) : IntegrableOn (deningerHigherMomentFun h r) (Set.Ioi 0) := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPullDeriv_weightedPow_norm_le hh r
  have hnear : IntegrableOn (deningerHigherMomentFun h r) (Set.Ioc 0 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => C) (Set.Ioc 0 1) := by
      refine integrableOn_const ?_
      simp
    refine Integrable.mono' hconst
      (((deningerHigherMoment_continuousOn h r).mono
        Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hu1 : u ≤ 1 := hu.2
    rw [Real.norm_of_nonneg (deningerHigherMomentFun_nonneg h r hu0.le)]
    refine le_trans ((hC u hu0).1) ?_
    have hle : u ^ (2 * r + 2) ≤ 1 := pow_le_one₀ hu0.le hu1
    nlinarith
  have hfar : IntegrableOn (deningerHigherMomentFun h r) (Set.Ioi 1) := by
    have hmaj : IntegrableOn (fun u : ℝ => C * u ^ (-2 : ℝ)) (Set.Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff (by norm_num)).mpr (by norm_num)).const_mul C
    refine Integrable.mono' hmaj
      (((deningerHigherMoment_continuousOn h r).mono
        (Set.Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
    rw [Real.norm_of_nonneg (deningerHigherMomentFun_nonneg h r hu0.le)]
    refine le_trans ((hC u hu0).2) (le_of_eq ?_)
    rw [Real.rpow_neg hu0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, ← div_eq_mul_inv]
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hunion]
  exact hnear.union hfar

end

end RHTower
