import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicCausalKernelIsAPositiveProbabilityDensity

/-!
# Exact normalization of the logarithmic renewal mass

Two Laplace bounds squeeze the cumulative causal kernel. At x = exp(-u),
the scales exp(u - sqrt(u)) and exp(u + sqrt(u)) have the same factor
normalization while suppressing the respective endpoint and tail errors.
-/

open MeasureTheory Set Filter Topology
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

theorem logarithmicRenewalMass_nonneg (x : ℝ) : 0 ≤ logarithmicRenewalMass x :=
  integral_nonneg logarithmicCausalKernel_nonneg

theorem logarithmicRenewalMass_le_one (x : ℝ) : logarithmicRenewalMass x ≤ 1 := by
  calc
    _ ≤ ∫ y : ℝ, logarithmicCausalKernel y :=
      setIntegral_le_integral logarithmicCausalKernel_mass_one.1
        (Eventually.of_forall logarithmicCausalKernel_nonneg)
    _ = 1 := logarithmicCausalKernel_mass_one.2

/-- A Laplace weight below its endpoint value bounds the cumulative causal mass. -/
theorem logarithmicRenewalMass_laplace_upper {s x : ℝ} (hs : 0 < s) :
    logarithmicRenewalMass x ≤ Real.exp (s * x) / logReferenceFactor s := by
  have hL := logarithmicCausalKernel_laplace hs
  have hi : IntegrableOn logarithmicCausalKernel (Ioc (0 : ℝ) x) :=
    logarithmicCausalKernel_mass_one.1.integrableOn
  have hsub : Ioc (0 : ℝ) x ⊆ Ioi (0 : ℝ) := fun y hy => hy.1
  have hw : Real.exp (-s * x) * logarithmicRenewalMass x ≤ (logReferenceFactor s)⁻¹ := by
    calc
      _ = ∫ y in Ioc (0 : ℝ) x, Real.exp (-s * x) * logarithmicCausalKernel y :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ y in Ioc (0 : ℝ) x, Real.exp (-s * y) * logarithmicCausalKernel y := by
        apply setIntegral_mono_on (hi.const_mul _) (hL.1.mono_set hsub) measurableSet_Ioc
        intro y hy
        apply mul_le_mul_of_nonneg_right _ (logarithmicCausalKernel_nonneg y)
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hy.2 hs.le
        linarith only [h]
      _ ≤ ∫ y in Ioi (0 : ℝ), Real.exp (-s * y) * logarithmicCausalKernel y := by
        apply setIntegral_mono_set hL.1
        · exact Eventually.of_forall fun y =>
            mul_nonneg (Real.exp_pos _).le (logarithmicCausalKernel_nonneg y)
        · exact Eventually.of_forall hsub
      _ = _ := hL.2
  calc
    logarithmicRenewalMass x = Real.exp (s * x) *
        (Real.exp (-s * x) * logarithmicRenewalMass x) := by
      rw [← mul_assoc, ← Real.exp_add]
      have he : s * x + -s * x = 0 := by ring
      rw [he, Real.exp_zero, one_mul]
    _ ≤ Real.exp (s * x) * (logReferenceFactor s)⁻¹ :=
      mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ = _ := by simp only [div_eq_mul_inv]

/-- A second Laplace scale controls the discarded tail of the cumulative mass. -/
theorem logarithmicRenewalMass_laplace_lower {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    (logReferenceFactor s)⁻¹ - Real.exp (-s * x / 2) / logReferenceFactor (s / 2) ≤
      logarithmicRenewalMass x := by
  have hL := logarithmicCausalKernel_laplace hs
  have hh := logarithmicCausalKernel_laplace (show 0 < s / 2 by linarith only [hs])
  have hsub : Ioc (0 : ℝ) x ⊆ Ioi (0 : ℝ) := fun y hy => hy.1
  have htailSub : Ioi x ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_le_of_lt hx hy
  have hsplit : (∫ y in Ioi (0 : ℝ), Real.exp (-s * y) * logarithmicCausalKernel y) =
      (∫ y in Ioc (0 : ℝ) x, Real.exp (-s * y) * logarithmicCausalKernel y) +
        ∫ y in Ioi x, Real.exp (-s * y) * logarithmicCausalKernel y := by
    rw [← Ioc_union_Ioi_eq_Ioi hx]
    apply setIntegral_union _ measurableSet_Ioi (hL.1.mono_set hsub) (hL.1.mono_set htailSub)
    exact disjoint_left.mpr fun y hy hyt => (not_lt_of_ge hy.2) hyt
  have hlow : (∫ y in Ioc (0 : ℝ) x, Real.exp (-s * y) * logarithmicCausalKernel y) ≤
      logarithmicRenewalMass x := by
    apply setIntegral_mono_on (hL.1.mono_set hsub)
      logarithmicCausalKernel_mass_one.1.integrableOn measurableSet_Ioc
    intro y hy
    have he : Real.exp (-s * y) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hs.le hy.1.le)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (logarithmicCausalKernel_nonneg y)
  have htail : (∫ y in Ioi x, Real.exp (-s * y) * logarithmicCausalKernel y) ≤
      Real.exp (-s * x / 2) / logReferenceFactor (s / 2) := by
    calc
      _ ≤ ∫ y in Ioi x, Real.exp (-s * x / 2) *
          (Real.exp (-(s / 2) * y) * logarithmicCausalKernel y) := by
        apply setIntegral_mono_on (hL.1.mono_set htailSub)
          ((hh.1.mono_set htailSub).const_mul _) measurableSet_Ioi
        intro y hy
        have he : Real.exp (-s * y) = Real.exp (-s * y / 2) * Real.exp (-(s / 2) * y) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [he, mul_assoc]
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (Real.exp_pos _).le (logarithmicCausalKernel_nonneg y))
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left (show x ≤ y from hy.le) hs.le
        linarith only [h]
      _ = Real.exp (-s * x / 2) *
          ∫ y in Ioi x, Real.exp (-(s / 2) * y) * logarithmicCausalKernel y := integral_const_mul _ _
      _ ≤ Real.exp (-s * x / 2) * (logReferenceFactor (s / 2))⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [← hh.2]
        apply setIntegral_mono_set hh.1
        · exact Eventually.of_forall fun y =>
            mul_nonneg (Real.exp_pos _).le (logarithmicCausalKernel_nonneg y)
        · exact Eventually.of_forall htailSub
      _ = _ := by simp only [div_eq_mul_inv]
  rw [hL.2] at hsplit
  linarith only [hlow, htail, hsplit]

private theorem tendsto_sqrt_div_self :
    Tendsto (fun u : ℝ => Real.sqrt u / u) atTop (nhds 0) := by
  simpa only [Real.sqrt_div_self, Function.comp_def] using!
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop

private theorem tendsto_logarithmicDrift_div (c d : ℝ) :
    Tendsto (fun u : ℝ => (u + c * Real.sqrt u + d) / u) atTop (nhds 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add
    (tendsto_sqrt_div_self.const_mul c)).add (tendsto_inv_atTop_zero.const_mul d)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  field_simp [hu.ne']

private theorem tendsto_logarithmicDrift_atTop (c d : ℝ) :
    Tendsto (fun u : ℝ => u + c * Real.sqrt u + d) atTop atTop := by
  have he : ∀ᶠ u : ℝ in atTop, (1 : ℝ) / 2 < (u + c * Real.sqrt u + d) / u :=
    (tendsto_logarithmicDrift_div c d).eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [he, eventually_ge_atTop (max (1 : ℝ) (2 * B))] with u hu hB
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hB)
  have hBu : 2 * B ≤ u := (le_max_right _ _).trans hB
  have h := (lt_div_iff₀ hu0).mp hu
  linarith only [h, hBu]

/-- Drifts smaller than the logarithmic scale preserve the exact factor normalization. -/
theorem tendsto_sqrt_div_logReferenceFactor_drift (c d : ℝ) :
    Tendsto (fun u : ℝ => Real.sqrt u / logReferenceFactor (Real.exp (u + c * Real.sqrt u + d)))
      atTop (nhds 1) := by
  have hd := tendsto_logarithmicDrift_atTop c d
  have he := Real.tendsto_exp_atTop.comp hd
  have hK := tendsto_logReferenceFactor_div_sqrt_log.comp he
  simp only [Function.comp_def, Real.log_exp] at hK
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_logarithmicDrift_div c d)
  simp only [Real.sqrt_one] at hr
  have hratio : Tendsto (fun u : ℝ => Real.sqrt (u + c * Real.sqrt u + d) / Real.sqrt u)
      atTop (nhds 1) := by
    apply hr.congr'
    filter_upwards [hd.eventually (eventually_gt_atTop (0 : ℝ))] with u hu
    exact Real.sqrt_div hu.le u
  have hprod := hK.mul hratio
  simp only [mul_one] at hprod
  have hnorm : Tendsto (fun u : ℝ =>
      logReferenceFactor (Real.exp (u + c * Real.sqrt u + d)) / Real.sqrt u) atTop (nhds 1) := by
    apply hprod.congr'
    filter_upwards [hd.eventually (eventually_gt_atTop (0 : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with u hd0 hu
    have hn := (Real.sqrt_pos.mpr hd0).ne'
    field_simp [hn, (Real.sqrt_pos.mpr hu).ne']
  have hInv := hnorm.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_one, inv_div] using hInv

/-- Two drifting Laplace scales squeeze the renewal mass to its exact logarithmic normalization. -/
theorem tendsto_logarithmicRenewalMass_exp_normalized :
    Tendsto (fun u : ℝ => logarithmicRenewalMass (Real.exp (-u)) * Real.sqrt u)
      atTop (nhds 1) := by
  have hKm : Tendsto (fun u : ℝ => Real.sqrt u / logReferenceFactor (Real.exp (u - Real.sqrt u)))
      atTop (nhds 1) := by
    simpa only [neg_one_mul, add_zero, ← sub_eq_add_neg] using
      tendsto_sqrt_div_logReferenceFactor_drift (-1) 0
  have hKp : Tendsto (fun u : ℝ => Real.sqrt u / logReferenceFactor (Real.exp (u + Real.sqrt u)))
      atTop (nhds 1) := by
    simpa only [one_mul, add_zero] using tendsto_sqrt_div_logReferenceFactor_drift 1 0
  have hKh : Tendsto (fun u : ℝ => Real.sqrt u / logReferenceFactor (Real.exp (u + Real.sqrt u) / 2))
      atTop (nhds 1) := by
    simpa only [one_mul, ← sub_eq_add_neg, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
      tendsto_sqrt_div_logReferenceFactor_drift 1 (-Real.log 2)
  have hexpm := Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop
  have hupper : Tendsto (fun u : ℝ => Real.exp (Real.exp (-Real.sqrt u)) *
      (Real.sqrt u / logReferenceFactor (Real.exp (u - Real.sqrt u)))) atTop (nhds 1) := by
    have h := (Real.continuous_exp.continuousAt.tendsto.comp hexpm).mul hKm
    simpa only [Real.exp_zero, one_mul] using! h
  have htail : Tendsto (fun u : ℝ => Real.exp (-Real.exp (Real.sqrt u) / 2)) atTop (nhds 0) := by
    have h := (Real.tendsto_exp_atTop.comp Real.tendsto_sqrt_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 2)
    simpa only [Function.comp_def, neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp h
  have hlower : Tendsto (fun u : ℝ => Real.sqrt u / logReferenceFactor (Real.exp (u + Real.sqrt u)) -
      Real.exp (-Real.exp (Real.sqrt u) / 2) *
        (Real.sqrt u / logReferenceFactor (Real.exp (u + Real.sqrt u) / 2))) atTop (nhds 1) := by
    simpa only [zero_mul, sub_zero] using! hKp.sub (htail.mul hKh)
  have hleUpper (u : ℝ) : logarithmicRenewalMass (Real.exp (-u)) * Real.sqrt u ≤
      Real.exp (Real.exp (-Real.sqrt u)) *
        (Real.sqrt u / logReferenceFactor (Real.exp (u - Real.sqrt u))) := by
    have h := mul_le_mul_of_nonneg_right
      (logarithmicRenewalMass_laplace_upper (x := Real.exp (-u)) (Real.exp_pos (u - Real.sqrt u)))
      (Real.sqrt_nonneg u)
    have he : Real.exp (u - Real.sqrt u) * Real.exp (-u) = Real.exp (-Real.sqrt u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at h
    calc
      _ ≤ (Real.exp (Real.exp (-Real.sqrt u)) /
          logReferenceFactor (Real.exp (u - Real.sqrt u))) * Real.sqrt u := h
      _ = _ := by ring
  have hleLower (u : ℝ) : Real.sqrt u / logReferenceFactor (Real.exp (u + Real.sqrt u)) -
      Real.exp (-Real.exp (Real.sqrt u) / 2) *
        (Real.sqrt u / logReferenceFactor (Real.exp (u + Real.sqrt u) / 2)) ≤
          logarithmicRenewalMass (Real.exp (-u)) * Real.sqrt u := by
    have h := mul_le_mul_of_nonneg_right
      (logarithmicRenewalMass_laplace_lower (Real.exp_pos (u + Real.sqrt u)) (Real.exp_pos (-u)).le)
      (Real.sqrt_nonneg u)
    have he : -Real.exp (u + Real.sqrt u) * Real.exp (-u) / 2 = -Real.exp (Real.sqrt u) / 2 := by
      rw [neg_mul, ← Real.exp_add]
      congr 2
      ring
    rw [he] at h
    calc
      _ = ((logReferenceFactor (Real.exp (u + Real.sqrt u)))⁻¹ -
          Real.exp (-Real.exp (Real.sqrt u) / 2) /
            logReferenceFactor (Real.exp (u + Real.sqrt u) / 2)) * Real.sqrt u := by ring
      _ ≤ _ := h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper hleLower hleUpper

/-- The actual cumulative causal kernel fixes the boundary scale, with constant exactly one. -/
theorem tendsto_logarithmicRenewalMass_normalized :
    Tendsto (fun x : ℝ => logarithmicRenewalMass x * Real.sqrt (Real.log (1 / x)))
      (𝓝[>] (0 : ℝ)) (nhds 1) := by
  have hu : Tendsto (fun x : ℝ => -Real.log x) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h := tendsto_logarithmicRenewalMass_exp_normalized.comp hu
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change (0 : ℝ) < x at hx
  simp only [Function.comp_def, neg_neg, Real.exp_log hx, one_div, Real.log_inv]

#print axioms logarithmicRenewalMass_laplace_upper
#print axioms logarithmicRenewalMass_laplace_lower
#print axioms tendsto_sqrt_div_logReferenceFactor_drift
#print axioms tendsto_logarithmicRenewalMass_normalized

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
