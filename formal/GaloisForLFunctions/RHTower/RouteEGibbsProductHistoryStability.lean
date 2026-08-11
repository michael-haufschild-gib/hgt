import GaloisForLFunctions.RHTower.RouteEGibbsProductStability

/-!
# Route E all-order product-history Gibbs stability

Equality of products for two physical histories forces their sums to agree up to a quadratic
aperture error.  The proof uses the exact integral remainder of `log (1+u)` and retains the sharp
factor `1/2` on each history.
-/

namespace RHTower

open scoped BigOperators Interval

noncomputable section

/-- Exact logarithmic linearization remainder on a symmetric subunit interval. -/
theorem routeE_abs_log_one_add_sub_self_le
    (u h : ℝ) (hh : 0 ≤ h) (hh1 : h < 1) (hu : |u| ≤ h) :
    |Real.log (1 + u) - u| ≤ u ^ 2 / (2 * (1 - h)) := by
  let F : ℝ → ℝ := fun t => t - Real.log (1 + t)
  let dF : ℝ → ℝ := fun t => t / (1 + t)
  have hone : 0 < 1 - h := sub_pos.mpr hh1
  have habs_on : ∀ t ∈ Set.uIcc 0 u, |t| ≤ h := by
    intro t ht
    rcases le_total 0 u with hu0 | hu0
    · rw [Set.uIcc_of_le hu0] at ht
      rw [abs_of_nonneg ht.1]
      exact ht.2.trans (le_trans (le_abs_self u) hu)
    · rw [Set.uIcc_of_ge hu0] at ht
      have ht0 : t ≤ 0 := ht.2
      rw [abs_of_nonpos ht0]
      have hneg : -t ≤ -u := neg_le_neg ht.1
      exact hneg.trans (le_trans (neg_le_abs u) hu)
  have hdenom : ∀ t ∈ Set.uIcc 0 u, 0 < 1 + t := by
    intro t ht
    have htLower := neg_le_of_abs_le (habs_on t ht)
    linarith
  have hderiv : ∀ t ∈ Set.uIcc 0 u, HasDerivAt F (dF t) t := by
    intro t ht
    have harg : 1 + t ≠ 0 := ne_of_gt (hdenom t ht)
    have hinner : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa only [Pi.add_apply, id_eq, zero_add] using
        (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
    have hlog := (Real.hasDerivAt_log harg).comp t hinner
    dsimp only [F, dF]
    have hvalue : 1 - (1 + t)⁻¹ = t / (1 + t) := by
      field_simp [harg]
      ring
    exact ((hasDerivAt_id t).sub hlog).congr_deriv hvalue
  have hdFcont : ContinuousOn dF (Set.uIcc 0 u) := by
    apply ContinuousOn.div continuousOn_id (continuousOn_const.add continuousOn_id)
    intro t ht
    exact ne_of_gt (hdenom t ht)
  have hfund : (∫ t in 0..u, dF t) = F u - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hdFcont.intervalIntegrable
  have hfund' : (∫ t in 0..u, dF t) = u - Real.log (1 + u) := by
    simpa [F] using hfund
  have hlogpos : 0 ≤ u - Real.log (1 + u) := by
    have harg : 0 < 1 + u := by
      have := neg_le_of_abs_le hu
      linarith
    linarith [Real.log_le_sub_one_of_pos harg]
  rw [abs_sub_comm, abs_of_nonneg hlogpos]
  rw [← hfund']
  rcases le_total 0 u with hu0 | hu0
  · have hdFint : IntervalIntegrable dF MeasureTheory.volume 0 u :=
      hdFcont.intervalIntegrable
    let g : ℝ → ℝ := fun t => t / (1 - h)
    have hgcont : Continuous g := by
      dsimp [g]
      fun_prop
    have hpoint : ∀ t ∈ Set.Icc 0 u, dF t ≤ g t := by
      intro t ht
      have htU : t ∈ Set.uIcc 0 u := by simpa [Set.uIcc_of_le hu0] using ht
      have hden := hdenom t htU
      have hbase : 1 - h ≤ 1 + t := by
        have htLower := neg_le_of_abs_le (habs_on t htU)
        linarith
      dsimp [dF, g]
      have htNonneg : 0 ≤ t := ht.1
      have hinv : (1 + t)⁻¹ ≤ (1 - h)⁻¹ :=
        by simpa only [one_div] using one_div_le_one_div_of_le hone hbase
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv htNonneg
    calc
      (∫ t in 0..u, dF t) ≤ ∫ t in 0..u, g t :=
        intervalIntegral.integral_mono_on hu0 hdFint
          (hgcont.intervalIntegrable 0 u) hpoint
      _ = u ^ 2 / (2 * (1 - h)) := by
        dsimp [g]
        rw [intervalIntegral.integral_div, integral_id]
        field_simp [ne_of_gt hone]
        ring
  · have hu0' : u ≤ 0 := hu0
    have hdFint : IntervalIntegrable dF MeasureTheory.volume u 0 := by
      have hdFcont' : ContinuousOn dF (Set.uIcc u 0) := by
        simpa [Set.uIcc_comm] using hdFcont
      exact hdFcont'.intervalIntegrable
    let g : ℝ → ℝ := fun t => -t / (1 - h)
    have hgcont : Continuous g := by
      dsimp [g]
      fun_prop
    have hpoint : ∀ t ∈ Set.Icc u 0, -dF t ≤ g t := by
      intro t ht
      have htU : t ∈ Set.uIcc 0 u := by simpa [Set.uIcc_of_ge hu0'] using ht
      have hden := hdenom t htU
      have hbase : 1 - h ≤ 1 + t := by
        have htLower := neg_le_of_abs_le (habs_on t htU)
        linarith
      dsimp [dF, g]
      have htNonneg : 0 ≤ -t := neg_nonneg.mpr ht.2
      have hinv : (1 + t)⁻¹ ≤ (1 - h)⁻¹ :=
        by simpa only [one_div] using one_div_le_one_div_of_le hone hbase
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv htNonneg
    rw [intervalIntegral.integral_symm]
    rw [← intervalIntegral.integral_neg]
    calc
      (∫ t in u..0, -dF t) ≤ ∫ t in u..0, g t :=
        intervalIntegral.integral_mono_on hu0' hdFint.neg
          (hgcont.intervalIntegrable u 0) hpoint
      _ = u ^ 2 / (2 * (1 - h)) := by
        dsimp [g]
        rw [intervalIntegral.integral_div, intervalIntegral.integral_neg, integral_id]
        field_simp [ne_of_gt hone]
        ring

end

end RHTower
