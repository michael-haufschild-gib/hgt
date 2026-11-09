import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SignedZetaTailDeletion
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SignedFiniteSpectrum

/-!
# Absolute local width detection by complex deletion

Complex convolution deletes a cofinite spectrum with bounded total variation.
A polynomial in translation then isolates any retained growing mode. The
contradiction uses absolute norms throughout, without positive averaging.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Absolute log-square windows detect every zeta depth by signed deletion. -/
theorem zeta_re_le_of_abs_logSquare_windows_signed {α K : ℝ} (hα : 0 ≤ α)
    (hwindow : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ zetaLogSquareRadius * Real.log (T + 2) ^ 2 →
      |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re| ≤ K * Real.exp (α * u)) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + α := by
  classical
  intro ρ hρ
  by_contra hρle
  have hρdeep : 1 / 2 + α < ρ.re := lt_of_not_ge hρle
  let z₀ : ℂ := ρ - 1 / 2
  let c : ℂ → ℂ := evenCoeff zetaZeroConfig (boxSpline 1 3)
  let D : ℝ := 1 / 2 + |α|
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hc : Summable fun z => ‖c z‖ := summable_norm_evenCoeff_spline temperedConfig_zetaZeroConfig
  have hw : ∀ z, c z ≠ 0 → |(z - (α : ℂ)).re| ≤ D :=
    fun z hz => configuration_shifted_exponent_bound α hz
  have hc₀ : c z₀ ≠ 0 := evenCoeff_spline_sees hρ (by linarith only [hρdeep, hα])
  obtain ⟨M, S, hkeep, hdelete⟩ := exists_signed_zeta_deletion_tail α (z₀ - (α : ℂ))
  let d : ℂ → ℂ := fun z => c z * ∏' n, signedDeletionFactor
    (zetaDeletionDepth α (n + M)) (zetaSignedDeletionShift (n + M)) (z - (α : ℂ))
  have hdout : ∀ z ∉ S, d z = 0 := by
    intro z hz
    by_cases hcz : c z = 0
    · simp only [d, hcz, zero_mul]
    change c z * _ = 0
    rw [hdelete z hz hcz, mul_zero]
  have hd₀ : d z₀ ≠ 0 := mul_ne_zero hc₀ hkeep
  have hz₀S : z₀ ∈ S := by_contra fun hn => hd₀ (hdout z₀ hn)
  obtain ⟨B, η, hB, hη, hlarge⟩ := finite_spectrum_dense_norm S d hz₀S hd₀
  let A : ℝ := ∑' z, ‖c z‖
  let V : ℝ := Real.exp (∑' n, 3 / 2 *
    (zetaSignedDeletionShift (n + M) * zetaDeletionDepth α (n + M)) ^ 2)
  have hV : 0 < V := Real.exp_pos _
  have hgap : 0 < z₀.re - α := by
    dsimp only [z₀]
    simp only [Complex.sub_re]
    norm_num
    linarith only [hρdeep]
  have hleak : Tendsto (fun T : ℝ => 2 * A * Real.exp (D * B - T)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (2 * A * Real.exp (D * B))
    simpa only [mul_zero, sub_eq_add_neg, Real.exp_add, mul_assoc] using ht
  have hgrowth : Tendsto (fun T : ℝ => η * Real.exp ((z₀.re - α) * T)) atTop atTop := by
    simpa only [Function.comp_def, id_eq] using
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hgap)).const_mul_atTop hη
  let C : ℝ := max 1 (max (D + 1) (2 * B / zetaLogSquareRadius))
  let W : ℝ := max D (max 3 (max (Real.exp 12) (Real.exp C)))
  have hlate : ∀ᶠ T : ℝ in atTop, W ≤ T ∧
      2 * A * Real.exp (D * B - T) ≤ 1 ∧
      V * (|K| + 1) * Real.exp (α * B) < η * Real.exp ((z₀.re - α) * T) := by
    filter_upwards [eventually_ge_atTop W,
      hleak.eventually_le_const (by norm_num : (0 : ℝ) < 1),
      hgrowth.eventually_gt_atTop (V * (|K| + 1) * Real.exp (α * B))] with T hW hE hG
    exact ⟨hW, hE, hG⟩
  obtain ⟨U, hU⟩ := eventually_atTop.mp hlate
  obtain ⟨T, hTU, hbound⟩ := hwindow U
  obtain ⟨hTW, herror, hgrow⟩ := hU T hTU
  simp only [W, max_le_iff] at hTW
  obtain ⟨hDT, hT₃, hTheight, hTC⟩ := hTW
  have hT : 0 ≤ T := by linarith only [hT₃]
  have hEC : C ≤ Real.log (T + 2) := by
    have hh := Real.log_le_log (Real.exp_pos C)
      (show Real.exp C ≤ T + 2 by linarith only [hTC])
    rwa [Real.log_exp] at hh
  have hE : 1 ≤ Real.log (T + 2) := (le_max_left _ _).trans hEC
  have hEsq : Real.log (T + 2) ≤ Real.log (T + 2) ^ 2 := by
    nlinarith only [hE, sq_nonneg (Real.log (T + 2) - 1)]
  have hED : D + 1 ≤ Real.log (T + 2) ^ 2 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hEC.trans hEsq))
  have hspan : B ≤ zetaLogSquareRadius * Real.log (T + 2) ^ 2 / 2 := by
    have hh : 2 * B / zetaLogSquareRadius ≤ Real.log (T + 2) ^ 2 :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (hEC.trans hEsq))
    have hm := (div_le_iff₀ zetaLogSquareRadius_pos).mp hh
    nlinarith only [hm]
  obtain ⟨t, ht, hbig⟩ := hlarge T
  have ht0 : 0 ≤ t := hT.trans ht.1
  have htB : |t| ≤ T + B := by rw [abs_of_nonneg ht0]; exact ht.2
  have hlocal : ∀ u, |u - t| ≤ zetaLogSquareRadius * Real.log (T + 2) ^ 2 / 2 →
      ‖∑' z : ℂ, c z * Complex.exp ((z - (α : ℂ)) * u)‖ ≤ |K| := by
    intro u hu
    have htT : |t - T| ≤ B := abs_le.mpr ⟨by linarith only [ht.1, hB], by linarith only [ht.2]⟩
    have huT : |u - T| ≤ zetaLogSquareRadius * Real.log (T + 2) ^ 2 := by
      have htri : |u - T| ≤ |u - t| + |t - T| := by
        calc |u - T| = |(u - t) + (t - T)| := by congr 1; ring
          _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_add_le (u - t) (t - T)
      linarith only [htri, htT, hu, hspan]
    change ‖∑' z : ℂ, evenCoeff zetaZeroConfig (boxSpline 1 3) z *
      Complex.exp ((z - (α : ℂ)) * u)‖ ≤ |K|
    rw [← ofReal_normTrace temperedConfig_zetaZeroConfig u, Complex.norm_real,
      Real.norm_eq_abs, normTrace, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hh := mul_le_mul_of_nonneg_right (hbound u huT) (Real.exp_pos (-(α * u))).le
    have he : (K * Real.exp (α * u)) * Real.exp (-(α * u)) = K := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rw [he] at hh
    exact hh.trans (le_abs_self K)
  have hupper := infinite_signed_zeta_logSquare_norm α M c (fun z => z - (α : ℂ))
    hD hc hw (abs_nonneg K) hDT hT₃ hTheight hE hED htB hlocal
  change ‖∑' z : ℂ, d z * Complex.exp ((z - (α : ℂ)) * t)‖ ≤
    V * (|K| + 2 * A * Real.exp (D * B - T)) at hupper
  rw [tsum_eq_sum (s := S) (fun z hz => by rw [hdout z hz, zero_mul])] at hupper
  have hnorm : ‖∑ z ∈ S, d z * Complex.exp ((z - (α : ℂ)) * t)‖ ≤ V * (|K| + 1) :=
    hupper.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl herror) hV.le)
  have hscaled := mul_le_mul_of_nonneg_right hnorm (Real.exp_pos (α * t)).le
  rw [finite_sum_cexp_norm_scale] at hscaled
  have hboundT : ‖∑ z ∈ S, d z * Complex.exp (z * t)‖ ≤
      V * (|K| + 1) * Real.exp (α * (T + B)) :=
    hscaled.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hα)) (by positivity))
  have hgt := mul_lt_mul_of_pos_right hgrow (Real.exp_pos (α * T))
  have he₁ : (V * (|K| + 1) * Real.exp (α * B)) * Real.exp (α * T) =
      V * (|K| + 1) * Real.exp (α * (T + B)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have he₂ : (η * Real.exp ((z₀.re - α) * T)) * Real.exp (α * T) =
      η * Real.exp (z₀.re * T) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he₁, he₂] at hgt
  exact (not_lt_of_ge (hbig.trans hboundT)) hgt

#print axioms zeta_re_le_of_abs_logSquare_windows_signed

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
