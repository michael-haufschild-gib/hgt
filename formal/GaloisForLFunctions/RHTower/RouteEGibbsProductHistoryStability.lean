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
    |Real.log (1 + u) - u| ≤ u ^ (2 : ℕ) / (2 * (1 - h)) := by
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
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have hlog := (Real.hasDerivAt_log harg).comp t hinner
    dsimp only [F, dF]
    have hvalue : 1 - (1 + t)⁻¹ * 1 = t / (1 + t) := by
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
      _ = u ^ (2 : ℕ) / (2 * (1 - h)) := by
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
      _ = u ^ (2 : ℕ) / (2 * (1 - h)) := by
        dsimp [g]
        rw [intervalIntegral.integral_div, intervalIntegral.integral_neg, integral_id]
        field_simp [ne_of_gt hone]
        ring

private theorem routeE_abs_physicalLogRemainder_le
    (X H A : ℝ) (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X) (hA : |A| ≤ H) :
    |Real.log (1 + A / X) - A / X| ≤ H ^ (2 : ℕ) / (2 * X * (X - H)) := by
  have hratio : 0 ≤ H / X := div_nonneg hH hX.le
  have hratioOne : H / X < 1 := (div_lt_one hX).2 hHX
  have hu : |A / X| ≤ H / X := by
    rw [abs_div, abs_of_pos hX]
    exact div_le_div_of_nonneg_right hA hX.le
  have hraw := routeE_abs_log_one_add_sub_self_le
    (A / X) (H / X) hratio hratioOne hu
  have hsq : (A / X) ^ (2 : ℕ) ≤ (H / X) ^ (2 : ℕ) := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hratio).2 hu
  have hden : 0 < 2 * (1 - H / X) := mul_pos (by norm_num) (sub_pos.mpr hratioOne)
  calc
    |Real.log (1 + A / X) - A / X| ≤
        (A / X) ^ (2 : ℕ) / (2 * (1 - H / X)) := hraw
    _ ≤ (H / X) ^ (2 : ℕ) / (2 * (1 - H / X)) :=
      div_le_div_of_nonneg_right hsq hden.le
    _ = H ^ (2 : ℕ) / (2 * X * (X - H)) := by
      field_simp [ne_of_gt hX, ne_of_gt (sub_pos.mpr hHX)]

/-- **All-order product-history sum stability.**  Equal products inside one common aperture force
the two one-body sums to differ by at most `m H²/(X-H)`, where `m` is replica cardinality. -/
theorem routeEProductHistory_sum_stability
    {R : Type*} [Fintype R]
    (X H : ℝ) (n n' : R → ℝ)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (hn : ∀ r, n r ∈ Set.Icc (X - H) (X + H))
    (hn' : ∀ r, n' r ∈ Set.Icc (X - H) (X + H))
    (hprod : ∏ r, n r = ∏ r, n' r) :
    |(∑ r, n r) - ∑ r, n' r| ≤
      (Fintype.card R : ℝ) * H ^ (2 : ℕ) / (X - H) := by
  classical
  let A : R → ℝ := fun r => n r - X
  let B : R → ℝ := fun r => n' r - X
  let q : ℝ := H ^ (2 : ℕ) / (2 * X * (X - H))
  let eA : R → ℝ := fun r => Real.log (1 + A r / X) - A r / X
  let eB : R → ℝ := fun r => Real.log (1 + B r / X) - B r / X
  have hXH : 0 < X - H := sub_pos.mpr hHX
  have hA : ∀ r, |A r| ≤ H := by
    intro r
    exact abs_le.mpr ⟨by dsimp [A]; linarith [(hn r).1], by dsimp [A]; linarith [(hn r).2]⟩
  have hB : ∀ r, |B r| ≤ H := by
    intro r
    exact abs_le.mpr ⟨by dsimp [B]; linarith [(hn' r).1], by dsimp [B]; linarith [(hn' r).2]⟩
  have hnpos : ∀ r, 0 < n r := fun r => lt_of_lt_of_le hXH (hn r).1
  have hnpos' : ∀ r, 0 < n' r := fun r => lt_of_lt_of_le hXH (hn' r).1
  have hnormalizedPos : ∀ r, 0 < 1 + A r / X := by
    intro r
    rw [show 1 + A r / X = n r / X by
      dsimp [A]
      field_simp [ne_of_gt hX]
      ring]
    exact div_pos (hnpos r) hX
  have hnormalizedPos' : ∀ r, 0 < 1 + B r / X := by
    intro r
    rw [show 1 + B r / X = n' r / X by
      dsimp [B]
      field_simp [ne_of_gt hX]
      ring]
    exact div_pos (hnpos' r) hX
  have hlogA : ∀ r, Real.log (n r) = Real.log X + Real.log (1 + A r / X) := by
    intro r
    have hfactor : n r = X * (1 + A r / X) := by
      dsimp [A]
      field_simp [ne_of_gt hX]
      ring
    rw [hfactor, Real.log_mul (ne_of_gt hX) (ne_of_gt (hnormalizedPos r))]
  have hlogB : ∀ r, Real.log (n' r) = Real.log X + Real.log (1 + B r / X) := by
    intro r
    have hfactor : n' r = X * (1 + B r / X) := by
      dsimp [B]
      field_simp [ne_of_gt hX]
      ring
    rw [hfactor, Real.log_mul (ne_of_gt hX) (ne_of_gt (hnormalizedPos' r))]
  have hsumLog : ∑ r, Real.log (n r) = ∑ r, Real.log (n' r) := by
    rw [← Real.log_prod (fun r _hr => ne_of_gt (hnpos r)),
      ← Real.log_prod (fun r _hr => ne_of_gt (hnpos' r)), hprod]
  have hnormalizedLog :
      ∑ r, Real.log (1 + A r / X) = ∑ r, Real.log (1 + B r / X) := by
    simp_rw [hlogA] at hsumLog
    simp_rw [hlogB] at hsumLog
    simp only [Finset.sum_add_distrib] at hsumLog
    linarith
  have heA : ∀ r, |eA r| ≤ q := fun r => by
    exact routeE_abs_physicalLogRemainder_le X H (A r) hX hH hHX (hA r)
  have heB : ∀ r, |eB r| ≤ q := fun r => by
    exact routeE_abs_physicalLogRemainder_le X H (B r) hX hH hHX (hB r)
  have heASum : |∑ r, eA r| ≤ (Fintype.card R : ℝ) * q := by
    calc
      |∑ r, eA r| ≤ ∑ r, |eA r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : R, q := Finset.sum_le_sum fun r _hr => heA r
      _ = (Fintype.card R : ℝ) * q := by simp
  have heBSum : |∑ r, eB r| ≤ (Fintype.card R : ℝ) * q := by
    calc
      |∑ r, eB r| ≤ ∑ r, |eB r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : R, q := Finset.sum_le_sum fun r _hr => heB r
      _ = (Fintype.card R : ℝ) * q := by simp
  have herrorIdentity :
      (∑ r, A r / X) - ∑ r, B r / X = (∑ r, eB r) - ∑ r, eA r := by
    have h := hnormalizedLog
    have heAeq : ∀ r, Real.log (1 + A r / X) = A r / X + eA r := by
      intro r
      dsimp [eA]
      ring
    have heBeq : ∀ r, Real.log (1 + B r / X) = B r / X + eB r := by
      intro r
      dsimp [eB]
      ring
    simp_rw [heAeq] at h
    simp_rw [heBeq] at h
    simp only [Finset.sum_add_distrib] at h
    linarith
  have hnormalizedBound :
      |(∑ r, A r / X) - ∑ r, B r / X| ≤
        2 * (Fintype.card R : ℝ) * q := by
    rw [herrorIdentity]
    calc
      |(∑ r, eB r) - ∑ r, eA r| ≤ |∑ r, eB r| + |∑ r, eA r| := abs_sub _ _
      _ ≤ (Fintype.card R : ℝ) * q + (Fintype.card R : ℝ) * q :=
        add_le_add heBSum heASum
      _ = 2 * (Fintype.card R : ℝ) * q := by ring
  have hoffsetNormalized :
      ((∑ r, A r) - ∑ r, B r) / X =
        (∑ r, A r / X) - ∑ r, B r / X := by
    rw [← Finset.sum_div, ← Finset.sum_div]
    ring
  have hoffset : |(∑ r, A r) - ∑ r, B r| ≤
      (Fintype.card R : ℝ) * H ^ (2 : ℕ) / (X - H) := by
    rw [← hoffsetNormalized] at hnormalizedBound
    rw [abs_div, abs_of_pos hX] at hnormalizedBound
    calc
      |(∑ r, A r) - ∑ r, B r| ≤
          2 * (Fintype.card R : ℝ) * q * X :=
        (div_le_iff₀ hX).mp hnormalizedBound
      _ = (Fintype.card R : ℝ) * H ^ (2 : ℕ) / (X - H) := by
        dsimp [q]
        field_simp [ne_of_gt hX, ne_of_gt hXH]
  convert hoffset using 1
  dsimp [A, B]
  simp_rw [Finset.sum_sub_distrib]
  ring

/-- Product Gibbs weight of a finite physical history. -/
def routeEProductHistoryGibbsWeight
    {R : Type*} [Fintype R] (X : ℝ) (n : R → ℝ) : ℝ :=
  ∏ r, Real.exp (-n r / X)

theorem routeEProductHistoryGibbsWeight_eq_exp_sum
    {R : Type*} [Fintype R] (X : ℝ) (n : R → ℝ) :
    routeEProductHistoryGibbsWeight X n =
      Real.exp (-(∑ r, n r) / X) := by
  unfold routeEProductHistoryGibbsWeight
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- Logarithmic product-Gibbs distortion inside one product cell. -/
theorem routeEProductHistory_abs_log_gibbs_ratio_le
    {R : Type*} [Fintype R]
    (X H : ℝ) (n n' : R → ℝ)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (hn : ∀ r, n r ∈ Set.Icc (X - H) (X + H))
    (hn' : ∀ r, n' r ∈ Set.Icc (X - H) (X + H))
    (hprod : ∏ r, n r = ∏ r, n' r) :
    |Real.log (routeEProductHistoryGibbsWeight X n /
        routeEProductHistoryGibbsWeight X n')| ≤
      (Fintype.card R : ℝ) * H ^ (2 : ℕ) / (X * (X - H)) := by
  have hsum := routeEProductHistory_sum_stability X H n n' hX hH hHX hn hn' hprod
  rw [routeEProductHistoryGibbsWeight_eq_exp_sum,
    routeEProductHistoryGibbsWeight_eq_exp_sum,
    Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp]
  rw [show (-(∑ r, n r) / X - -(∑ r, n' r) / X) =
      -((∑ r, n r) - ∑ r, n' r) / X by ring]
  rw [abs_div, abs_neg, abs_of_pos hX]
  calc
    |(∑ r, n r) - ∑ r, n' r| / X ≤
        ((Fintype.card R : ℝ) * H ^ (2 : ℕ) / (X - H)) / X :=
      div_le_div_of_nonneg_right hsum hX.le
    _ = (Fintype.card R : ℝ) * H ^ (2 : ℕ) / (X * (X - H)) := by
      field_simp [ne_of_gt hX, ne_of_gt (sub_pos.mpr hHX)]

end

end RHTower
