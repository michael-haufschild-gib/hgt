import GaloisForLFunctions.RHTower.XiOrderedPrimeApproximationNumbers

/-!
# Logarithmic singular-value law for the ordered Xi reciprocal operator

The actual ordered Xi ordinates remain within bounded distance of their smooth Riemann--von
Mangoldt quantiles.  Their quotient therefore tends to one, and the exact approximation-number
formula inherits the model asymptotic `log (n + 1) / (π (n + 1))`.
-/

open Filter

namespace RHTower

noncomputable section

theorem tendsto_routeKRVMQuantile_div_xiOrderedPositiveOrdinate :
    Tendsto (fun n : ℕ =>
      routeKRVMQuantile n / xiOrderedPositiveOrdinate n)
      atTop (nhds 1) := by
  obtain ⟨D, _hD, hdist⟩ :=
    exists_eventually_abs_xiOrderedPositiveOrdinate_sub_routeKRVMQuantile_le
  have hmajor : Tendsto (fun n : ℕ =>
      D / xiOrderedPositiveOrdinate n) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      tendsto_xiOrderedPositiveOrdinate_atTop
  have hsmall : Tendsto (fun n : ℕ =>
      (routeKRVMQuantile n - xiOrderedPositiveOrdinate n) /
        xiOrderedPositiveOrdinate n) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hmajor
    filter_upwards [hdist] with n hn
    have hgamma0 := xiOrderedPositiveOrdinate_pos n
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hgamma0]
    rw [abs_sub_comm] at hn
    exact div_le_div_of_nonneg_right hn hgamma0.le
  have hsum := (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
  have hfinal : Tendsto (fun n : ℕ =>
      routeKRVMQuantile n / xiOrderedPositiveOrdinate n)
      atTop (nhds ((1 : ℝ) + 0)) := by
    apply hsum.congr'
    filter_upwards [] with n
    have hgamma0 := xiOrderedPositiveOrdinate_pos n
    field_simp [hgamma0.ne']
    ring
  simpa using hfinal

theorem tendsto_xiOrderedSignedApproxNumber_div_routeKRVMSignedApproxNumber :
    Tendsto (fun n : ℕ =>
      xiOrderedSignedApproxNumber n / routeKRVMSignedApproxNumber n)
      atTop (nhds 1) := by
  have hratio :=
    tendsto_routeKRVMQuantile_div_xiOrderedPositiveOrdinate.comp
      tendsto_nat_half_atTop
  apply hratio.congr'
  filter_upwards [] with n
  have hgamma0 := xiOrderedPositiveOrdinate_pos (n / 2)
  have ht0 := routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile (n / 2))
  rw [xiOrderedSignedApproxNumber, routeKRVMSignedApproxNumber]
  simp only [Function.comp_apply]
  field_simp [hgamma0.ne', ht0.ne']

/-- Exact logarithmic approximation-number law for the actual reciprocal-Xi diagonal. -/
theorem tendsto_xiOrderedSignedPrimeOperator_approxNumber_div_model :
    Tendsto (fun n : ℕ => approxNumber xiOrderedSignedPrimeOperator n /
      (Real.log ((n : ℝ) + 1) / (Real.pi * ((n : ℝ) + 1))))
      atTop (nhds 1) := by
  have hproduct :=
    tendsto_xiOrderedSignedApproxNumber_div_routeKRVMSignedApproxNumber.mul
      tendsto_routeKRVMSignedApproxNumber_div_model
  simpa only [one_mul] using hproduct.congr' (by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hmodel0 : Real.log ((n : ℝ) + 1) /
        (Real.pi * ((n : ℝ) + 1)) ≠ 0 := by
      have hlog : 0 < Real.log ((n : ℝ) + 1) := by
        apply Real.log_pos
        exact_mod_cast Nat.succ_lt_succ (Nat.zero_lt_of_lt hn)
      positivity
    have hrvm0 : routeKRVMSignedApproxNumber n ≠ 0 :=
      ne_of_gt (routeKRVMSignedApproxNumber_pos n)
    rw [xiOrderedSignedPrimeOperator_approxNumber]
    field_simp [hmodel0, hrvm0])

end

end RHTower
