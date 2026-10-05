import GaloisForLFunctions.HTGeometry.MellinPlancherelBound
import GaloisForLFunctions.HTGeometry.SmoothedPerronContourShift

/-!
# Perron's formula for smooth test functions supported away from `0`

Let `f : ℝ → ℂ` be smooth with support in `[a, b]`, `0 < a ≤ b` (`IsTest f a b`).

* `𝓜f` is entire, `s 𝓜f(s) = −𝓜[u f'](s)` (`mellin_mul_deriv_eq`), hence
  `|s|² |𝓜f(s)| ≤ ∫_a^b |u (u f')'| u^{σ−1} du` and `𝓜f` is integrable on vertical lines.
* **Perron.**  For `|c| ≤ 1`, `c(0) = 0`, `σ > 1`, `X > 0`:
  `(1/2πi) ∫_{(σ)} L(c, s) 𝓜f(s) X^s ds = Σ_n c(n) f(n/X)` (`verticalIntegral'_eq_tsum`).
-/

open Real Complex Set MeasureTheory Function Filter Topology
open scoped ContDiff Interval

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TestFunctionPerron

/-- A smooth test function supported in `[a, b]`, `0 < a ≤ b`. -/
structure IsTest (f : ℝ → ℂ) (a b : ℝ) : Prop where
  pos : 0 < a
  le : a ≤ b
  smooth : ContDiff ℝ ∞ f
  supp : support f ⊆ Icc a b

namespace IsTest

variable {f : ℝ → ℂ} {a b : ℝ} (hf : IsTest f a b)
include hf

theorem eq_zero {u : ℝ} (hu : u ∉ Icc a b) : f u = 0 := by
  by_contra h; exact hu (hf.supp h)

theorem continuous : Continuous f := hf.smooth.continuous

theorem eq_zero_of_le {u : ℝ} (hu : u ≤ a) : f u = 0 := by
  rcases hu.lt_or_eq with h | h
  · exact hf.eq_zero fun h' => absurd h'.1 (not_le.mpr h)
  · -- `f = 0` left of `a`, so `f(a) = 0` by continuity
    have hlim : Tendsto f (𝓝[<] u) (𝓝 (f u)) := hf.continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have hzero : ∀ᶠ v in 𝓝[<] u, f v = 0 := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      have hv' : v < a := by rw [← h]; exact hv
      exact hf.eq_zero fun h' => absurd h'.1 (not_le.mpr hv')
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun v hv => hv.symm))

theorem eq_zero_of_ge {u : ℝ} (hu : b ≤ u) : f u = 0 := by
  rcases hu.lt_or_eq with h | h
  · exact hf.eq_zero fun h' => absurd h'.2 (not_le.mpr h)
  · have hlim : Tendsto f (𝓝[>] u) (𝓝 (f u)) := hf.continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have hzero : ∀ᶠ v in 𝓝[>] u, f v = 0 := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      have hv' : b < v := by rw [h]; exact hv
      exact hf.eq_zero fun h' => absurd h'.2 (not_le.mpr hv')
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun v hv => hv.symm))

/-- The Mellin transform is an integral over `[a, b]`. -/
theorem mellin_eq (s : ℂ) :
    mellin f s = ∫ u in a..b, (u : ℂ) ^ (s - 1) * f u := by
  rw [mellin, intervalIntegral.integral_of_le hf.le]
  simp_rw [smul_eq_mul]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_
  · intro u hu; exact lt_trans hf.pos hu.1
  · intro u hu
    have : f u = 0 := by
      by_cases h1 : u ≤ a
      · exact hf.eq_zero_of_le h1
      · push Not at h1
        exact hf.eq_zero_of_ge (by
          by_contra h2; push Not at h2; exact hu.2 ⟨h1, h2.le⟩)
    simp [this]

/-- The Euler derivative `u f'(u)` is again a test function on `[a, b]`. -/
theorem eulerDeriv : IsTest (fun u => (u : ℂ) * deriv f u) a b := by
  refine ⟨hf.pos, hf.le, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff).mul (contDiff_infty_iff_deriv.mp hf.smooth).2
  · intro u hu
    by_contra hnot
    apply hu
    have hloc : f =ᶠ[𝓝 u] fun _ => 0 := by
      have hopen : IsOpen (Icc a b)ᶜ := isClosed_Icc.isOpen_compl
      filter_upwards [hopen.mem_nhds hnot] with v hv
      exact hf.eq_zero hv
    show (u : ℂ) * deriv f u = 0
    rw [hloc.deriv_eq]; simp

theorem continuous_eulerDeriv : Continuous fun u : ℝ => (u : ℂ) * deriv f u :=
  hf.eulerDeriv.continuous

/-- **Integration by parts:** `𝓜[u f'](s) = −s 𝓜f(s)`. -/
theorem mellin_eulerDeriv (s : ℂ) :
    mellin (fun u => (u : ℂ) * deriv f u) s = -s * mellin f s := by
  rw [hf.eulerDeriv.mellin_eq, hf.mellin_eq]
  have ha := hf.pos
  have hb : 0 < b := lt_of_lt_of_le ha hf.le
  have hpos : ∀ u ∈ [[a, b]], 0 < u := fun u hu => by
    rw [Set.uIcc_of_le hf.le] at hu; exact lt_of_lt_of_le ha hu.1
  have hdf : ∀ u, HasDerivAt f (deriv f u) u := fun u =>
    ((contDiff_infty_iff_deriv.mp hf.smooth).1 u).hasDerivAt
  have hcont_df : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf.smooth).2.continuous
  have h1 : ∫ u in a..b, (u : ℂ) ^ (s - 1) * ((u : ℂ) * deriv f u) =
      ∫ u in a..b, (u : ℂ) ^ s * deriv f u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast (hpos u hu).ne'
    have hpow : (u : ℂ) ^ (s - 1) * u = (u : ℂ) ^ s := by
      conv_rhs => rw [show s = s - 1 + 1 by ring]
      rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
    rw [← mul_assoc, hpow]
  rw [h1]
  by_cases hs : s = 0
  · subst hs
    simp only [Complex.cpow_zero, one_mul, neg_zero, zero_mul]
    rw [intervalIntegral.integral_deriv_eq_sub (fun u _ => (hdf u).differentiableAt)
      (hcont_df.intervalIntegrable _ _), hf.eq_zero_of_le le_rfl, hf.eq_zero_of_ge le_rfl, sub_zero]
  have hU : ∀ u ∈ [[a, b]], HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (u : ℂ) ^ (s - 1)) u :=
    fun u hu => hasDerivAt_ofReal_cpow_const (hpos u hu).ne' hs
  have hcU : ContinuousOn (fun u : ℝ => s * (u : ℂ) ^ (s - 1)) [[a, b]] := by
    refine continuousOn_const.mul (fun u hu => ?_)
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (hpos u hu).ne')).continuousWithinAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hU (fun u _ => hdf u)
    (hcU.intervalIntegrable) (hcont_df.intervalIntegrable _ _), hf.eq_zero_of_le le_rfl,
    hf.eq_zero_of_ge le_rfl]
  simp only [mul_zero, sub_zero, zero_sub]
  rw [neg_mul, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  ring

/-- The scale `L = max(|log a|, |log b|)` of the support. -/
def logScale (a b : ℝ) : ℝ := max |Real.log a| |Real.log b|

/-- `|𝓜g(s)| ≤ (b − a) e^{R L} B` for `|Re s − 1| ≤ R` and `|g| ≤ B`. -/
theorem norm_mellin_le {R B : ℝ} (hB : ∀ u, ‖f u‖ ≤ B) {s : ℂ}
    (hs : |s.re - 1| ≤ R) :
    ‖mellin f s‖ ≤ (b - a) * Real.exp (R * logScale a b) * B := by
  rw [hf.mellin_eq]
  have ha := hf.pos
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Real.exp (R * logScale a b) * B) fun u hu => ?_).trans
    (le_of_eq (by rw [abs_of_nonneg (by linarith [hf.le])]; ring))
  rw [Set.uIoc_of_le hf.le] at hu
  have hu0 : 0 < u := lt_trans ha hu.1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  have hlog : |Real.log u| ≤ logScale a b := by
    unfold logScale
    rcases le_or_gt (Real.log u) 0 with h | h
    · rw [abs_of_nonpos h]
      have : Real.log a ≤ Real.log u := Real.log_le_log ha hu.1.le
      have hla : Real.log a ≤ 0 := by linarith
      calc -Real.log u ≤ -Real.log a := by linarith
        _ = |Real.log a| := (abs_of_nonpos hla).symm
        _ ≤ _ := le_max_left _ _
    · rw [abs_of_pos h]
      have : Real.log u ≤ Real.log b := Real.log_le_log hu0 hu.2
      calc Real.log u ≤ Real.log b := this
        _ ≤ |Real.log b| := le_abs_self _
        _ ≤ _ := le_max_right _ _
  have hpow : u ^ (s - 1).re ≤ Real.exp (R * logScale a b) := by
    rw [Real.rpow_def_of_pos hu0]
    apply Real.exp_le_exp.mpr
    have hre : (s - 1).re = s.re - 1 := by simp
    rw [hre]
    calc Real.log u * (s.re - 1) ≤ |Real.log u * (s.re - 1)| := le_abs_self _
      _ = |Real.log u| * |s.re - 1| := abs_mul _ _
      _ ≤ logScale a b * R := mul_le_mul hlog hs (abs_nonneg _) ((abs_nonneg _).trans hlog)
      _ = R * logScale a b := by ring
  exact mul_le_mul hpow (hB u) (norm_nonneg _) (Real.exp_pos _).le

/-- A test function is bounded. -/
theorem exists_bound : ∃ B, 0 ≤ B ∧ ∀ u, ‖f u‖ ≤ B := by
  obtain ⟨u₀, hu₀⟩ := hf.continuous.norm.exists_forall_ge_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun u hu => hf.eq_zero hu).norm
  exact ⟨‖f u₀‖, norm_nonneg _, hu₀⟩

/-- **Decay on vertical strips:** `|𝓜f(s)| ≤ C/(1 + (Im s)²)` for `|Re s − 1| ≤ R`. -/
theorem exists_norm_mellin_le_decay (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, |s.re - 1| ≤ R → ‖mellin f s‖ ≤ C / (1 + s.im ^ 2) := by
  have hf2 := hf.eulerDeriv.eulerDeriv
  obtain ⟨B₀, hB₀0, hB₀⟩ := hf.exists_bound
  obtain ⟨B₂, hB₂0, hB₂⟩ := hf2.exists_bound
  set C₀ := (b - a) * Real.exp (R * logScale a b) * B₀
  set C₂ := (b - a) * Real.exp (R * logScale a b) * B₂
  have hba : 0 ≤ b - a := by linarith [hf.le]
  refine ⟨2 * (C₀ + C₂), by positivity, fun s hs => ?_⟩
  have h0 := hf.norm_mellin_le hB₀ hs
  have h2 := hf2.norm_mellin_le hB₂ hs
  rw [hf.eulerDeriv.mellin_eulerDeriv, hf.mellin_eulerDeriv] at h2
  have hsq : ‖s‖ ^ 2 * ‖mellin f s‖ ≤ C₂ := by
    have : -s * (-s * mellin f s) = s ^ 2 * mellin f s := by ring
    rw [this, norm_mul, norm_pow] at h2; exact h2
  have him : s.im ^ 2 ≤ ‖s‖ ^ 2 := by
    have := Complex.abs_im_le_norm s
    nlinarith [abs_nonneg s.im, sq_abs s.im]
  rw [le_div_iff₀ (by positivity)]
  have hm0 := norm_nonneg (mellin f s)
  nlinarith

/-- The Mellin transform of a test function is entire. -/
theorem differentiableAt_mellin (s : ℂ) : DifferentiableAt ℂ (mellin f) s := by
  have ha := hf.pos
  have hb : 0 < b := lt_of_lt_of_le ha hf.le
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hf.continuous.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ (by linarith)
  · refine Asymptotics.isBigO_iff.mpr ⟨0, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop b] with u hu
    rw [hf.eq_zero_of_ge hu.le]; simp
  · refine Asymptotics.isBigO_iff.mpr ⟨0, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT ha] with u hu
    rw [hf.eq_zero_of_le hu.2.le]; simp

end IsTest

/-- Integrability on vertical lines. -/
theorem IsTest.verticalIntegrable {f : ℝ → ℂ} {a b : ℝ} (hf : IsTest f a b) (σ : ℝ) :
    Integrable fun t : ℝ => mellin f ((σ : ℂ) + t * I) := by
  obtain ⟨C, hC0, hC⟩ := hf.exists_norm_mellin_le_decay |σ - 1|
  refine (integrable_inv_one_add_sq.const_mul C).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun t => ?_)
    exact (hf.differentiableAt_mellin _).continuousAt.comp (by fun_prop)
  · filter_upwards with t
    have := hC ((σ : ℂ) + t * I) (by simp)
    simpa [div_eq_mul_inv] using this


end GaloisForLFunctions.HTGeometry.TestFunctionPerron
