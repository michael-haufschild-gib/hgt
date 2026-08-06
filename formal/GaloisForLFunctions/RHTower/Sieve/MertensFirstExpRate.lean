import GaloisForLFunctions.RHTower.Sieve.MertensThetaErrorIntegral

/-!
# Mertens' first theorem with an exponential error term

Splitting `θ(t)/t² = 1/t + (θ(t) − t)/t²` in the summation-by-parts identity separates the
logarithm from a convergent integral:

```text
mertensA ⌊x⌋ = 1 + (θ(x) − x)/x + log x − log 2 + ∫_{(2,x]} (θ(t) − t)/t² dt .
```

The last integral converges as `x → ∞`, so

```text
mertensA ⌊x⌋ − log x − c₁ = (θ(x) − x)/x − ∫_{(x,∞)} (θ(t) − t)/t² dt ,
      c₁ = 1 − log 2 + ∫_{(2,∞)} (θ(t) − t)/t² dt ,
```

and both remaining terms are `O(exp(−(c/2)√(log x)))` — the first because `θ` is, the second by the
explicit antiderivative of the tail weight.
-/

namespace RHTower.Sieve

open Filter Topology Asymptotics MeasureTheory Set

/-- Splitting the Abel integral into the logarithm and the error density. -/
theorem setIntegral_theta_div_sq {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in Set.Ioc 2 x, Chebyshev.theta t / t ^ 2
      = (Real.log x - Real.log 2) + ∫ t in Set.Ioc 2 x, thetaErrorDensity t := by
  have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 2 x) := by
    have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc (2 : ℝ) x) := by
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      intro t ht
      have : (2 : ℝ) ≤ t := ht.1
      linarith
    exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hden := integrableOn_thetaErrorDensity_Ioc (a := (2 : ℝ)) (b := x) (by norm_num)
  have hsum : ∫ t in Set.Ioc 2 x, Chebyshev.theta t / t ^ 2
      = (∫ t in Set.Ioc 2 x, (t : ℝ)⁻¹) + ∫ t in Set.Ioc 2 x, thetaErrorDensity t := by
    rw [← MeasureTheory.integral_add hinv hden]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : (0 : ℝ) < t := by have := ht.1; linarith
    unfold thetaErrorDensity
    field_simp
    ring
  have hlog : ∫ t in Set.Ioc 2 x, (t : ℝ)⁻¹ = Real.log x - Real.log 2 := by
    rw [← intervalIntegral.integral_of_le hx, integral_inv_of_pos (by norm_num) (by linarith),
      Real.log_div (by linarith) (by norm_num)]
  rw [hsum, hlog]

/-- The tail of the error integral is below the halved shape. -/
theorem abs_setIntegral_thetaErrorDensity_Ioi_le {c K x : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hx : 1 < x) (hint : IntegrableOn thetaErrorDensity (Set.Ioi x))
    (hbd : ∀ t : ℝ, x < t →
      |Chebyshev.theta t - t| ≤ K * t * Real.exp (-c * Real.sqrt (Real.log t))) :
    |∫ t in Set.Ioi x, thetaErrorDensity t|
      ≤ K * (4 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
  have hmaj : IntegrableOn
      (fun t : ℝ => K * (Real.exp (-c * Real.sqrt (Real.log t)) / t)) (Set.Ioi x) :=
    (integrableOn_expSqrtLog_div_Ioi hc hx).const_mul K
  have hptwise : ∀ t ∈ Set.Ioi x,
      |thetaErrorDensity t| ≤ K * (Real.exp (-c * Real.sqrt (Real.log t)) / t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans (by linarith) ht
    have hsq : (0 : ℝ) < t ^ 2 := by positivity
    have habs : |thetaErrorDensity t| = |Chebyshev.theta t - t| / t ^ 2 := by
      unfold thetaErrorDensity
      rw [abs_div, abs_of_pos hsq]
    rw [habs, div_le_iff₀ hsq]
    have hstep : K * (Real.exp (-c * Real.sqrt (Real.log t)) / t) * t ^ 2
        = K * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
      field_simp
    rw [hstep]
    exact hbd t ht
  have hstep1 : |∫ t in Set.Ioi x, thetaErrorDensity t|
      ≤ ∫ t in Set.Ioi x, |thetaErrorDensity t| := by
    simpa [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi x))
        thetaErrorDensity
  have hstep2 : ∫ t in Set.Ioi x, |thetaErrorDensity t|
      ≤ ∫ t in Set.Ioi x, K * (Real.exp (-c * Real.sqrt (Real.log t)) / t) :=
    setIntegral_mono_on hint.abs hmaj measurableSet_Ioi hptwise
  have hstep3 : ∫ t in Set.Ioi x, K * (Real.exp (-c * Real.sqrt (Real.log t)) / t)
      = K * sqrtLogTail c x := by
    rw [MeasureTheory.integral_const_mul, integral_expSqrtLog_div_Ioi hc hx]
  have hstep4 : K * sqrtLogTail c x
      ≤ K * (4 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    have := mul_le_mul_of_nonneg_left (sqrtLogTail_le (c := c) (t := x) hc) hK
    calc K * sqrtLogTail c x
        ≤ K * (4 / c ^ 2 * Real.exp (-(c / 2) * Real.sqrt (Real.log x))) := this
      _ = K * (4 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by ring
  linarith [hstep1, hstep2, hstep3 ▸ hstep2, hstep4]

/-- **Mertens' first theorem with an exponential error term.** -/
theorem exists_mertensA_sub_log_exp_rate :
    ∃ (c₁ B c : ℝ), 0 < c ∧ 0 ≤ B ∧ ∀ᶠ x : ℝ in atTop,
      |mertensA ⌊x⌋₊ - Real.log x - c₁| ≤ B * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc0, hbigO⟩ := chebyshevTheta_sub_id_isBigO
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨K, hKev⟩ := hbigO
  rw [eventually_atTop] at hKev
  obtain ⟨T₀, hT₀⟩ := hKev
  set T : ℝ := max T₀ 2 with hTdef
  have hT2 : (2 : ℝ) ≤ T := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ |K| := abs_nonneg K
  have hbdT : ∀ t : ℝ, T < t →
      |Chebyshev.theta t - t| ≤ |K| * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans (by linarith) ht
    have h := hT₀ t (le_trans (le_max_left _ _) ht.le)
    have hgn : ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖
        = t * Real.exp (-c * Real.sqrt (Real.log t)) := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hgn] at h
    have hE : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log t)) := Real.exp_pos _
    nlinarith [le_abs_self K, h, mul_pos ht0 hE]
  have hInt : IntegrableOn thetaErrorDensity (Set.Ioi 2) :=
    integrableOn_thetaErrorDensity_Ioi hc0 hT2 hbdT
  refine ⟨1 - Real.log 2 + ∫ t in Set.Ioi (2 : ℝ), thetaErrorDensity t,
    |K| + |K| * (4 / c ^ 2), c / 2, by linarith, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop T, eventually_ge_atTop (2 : ℝ)] with x hxT hx2
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  -- split the error integral at `x`
  have hIoc : IntegrableOn thetaErrorDensity (Set.Ioc 2 x) :=
    hInt.mono_set Set.Ioc_subset_Ioi_self
  have hIoi : IntegrableOn thetaErrorDensity (Set.Ioi x) :=
    hInt.mono_set (Set.Ioi_subset_Ioi (by linarith))
  have hdisj : Disjoint (Set.Ioc (2 : ℝ) x) (Set.Ioi x) :=
    Set.disjoint_left.mpr fun t ht ht' => absurd ht' (not_lt.mpr ht.2)
  have hsplit : ∫ t in Set.Ioi (2 : ℝ), thetaErrorDensity t
      = (∫ t in Set.Ioc 2 x, thetaErrorDensity t) + ∫ t in Set.Ioi x, thetaErrorDensity t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx2, setIntegral_union hdisj measurableSet_Ioi hIoc hIoi]
  -- the identity
  have hid : mertensA ⌊x⌋₊ - Real.log x
        - (1 - Real.log 2 + ∫ t in Set.Ioi (2 : ℝ), thetaErrorDensity t)
      = (Chebyshev.theta x - x) / x - ∫ t in Set.Ioi x, thetaErrorDensity t := by
    rw [mertensA_eq_theta_div_add_setIntegral hx2, setIntegral_theta_div_sq hx2, hsplit]
    have hdiv : Chebyshev.theta x / x = 1 + (Chebyshev.theta x - x) / x := by
      field_simp
      ring
    rw [hdiv]
    ring
  rw [hid]
  -- the two bounds
  have hb1 : |(Chebyshev.theta x - x) / x|
      ≤ |K| * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    have hb := hbdT x hxT
    have hE : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log x)) := Real.exp_pos _
    have hmono : Real.exp (-c * Real.sqrt (Real.log x))
        ≤ Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
      refine Real.exp_le_exp.mpr ?_
      have : (0 : ℝ) ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
      nlinarith
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    have hstep : |K| * x * Real.exp (-c * Real.sqrt (Real.log x))
        ≤ |K| * x * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_left hmono (mul_nonneg hK0 hx0.le)
    have hring : |K| * x * Real.exp (-(c / 2) * Real.sqrt (Real.log x))
        = |K| * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * x := by ring
    linarith [hb, hstep, hring]
  have hb2 : |∫ t in Set.Ioi x, thetaErrorDensity t|
      ≤ |K| * (4 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) :=
    abs_setIntegral_thetaErrorDensity_Ioi_le hc0 hK0 hx1 hIoi
      (fun t ht => hbdT t (lt_trans hxT ht))
  have htri := abs_sub ((Chebyshev.theta x - x) / x) (∫ t in Set.Ioi x, thetaErrorDensity t)
  have hexpand : (|K| + |K| * (4 / c ^ 2)) * Real.exp (-(c / 2) * Real.sqrt (Real.log x))
      = |K| * Real.exp (-(c / 2) * Real.sqrt (Real.log x))
        + |K| * (4 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by ring
  linarith [htri, hb1, hb2, hexpand]

end RHTower.Sieve
