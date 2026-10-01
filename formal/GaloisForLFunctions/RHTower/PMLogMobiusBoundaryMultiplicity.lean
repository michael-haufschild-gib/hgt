import GaloisForLFunctions.RHTower.PrimeLogZetaAbelPole
import GaloisForLFunctions.RHTower.PMLogMobiusContinuation

/-!
# Critical simplicity forced by fixed logarithmic Möbius convergence

An `o(log x / sqrt x)` source with an integrable fixed Mellin majorant has
vanishing quadratic Abel boundary values. Applied to the literal Möbius mean
defect, its continued cleared identity excludes any critical zeta zero whose
derivative also vanishes. Exact double divided slopes provide the quadratic
factor; no reciprocal-zeta bound near a zero is assumed.

The capstone is a necessary condition for convergence of the canonical Fermi
error. It proves neither that convergence nor RH nor unconditional simplicity.
-/

open MeasureTheory Set Filter Topology Asymptotics
noncomputable section
namespace RHTower

theorem pm_quadratic_abel_log_boundary {f : ℝ → ℂ}
    (hbase : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ) * ‖f x‖) (Ioi 1))
    (hsmall : f =o[atTop] (fun x : ℝ => Real.log x / Real.sqrt x))
    {s : ℂ} (hs : s.re = -1 / 2) :
    Tendsto (fun r : ℝ => (r : ℂ) ^ 2 *
      ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (-(s + (r : ℂ)) - 1) * f x)
      (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hnear : ∀ᶠ x : ℝ in atTop,
      ‖f x‖ ≤ (η / 2) * (Real.log x / Real.sqrt x) := by
    filter_upwards [hsmall.bound (half_pos hη), eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rwa [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.log_nonneg hx1) (Real.sqrt_nonneg x))] at hx
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hnear
  let X := max X₀ 1
  have hX1 : 1 ≤ X := le_max_right _ _
  have hX0 : 0 ≤ X := zero_le_one.trans hX1
  let A := ∫ x : ℝ in Ioi 1, x ^ (-2 : ℝ) * ‖f x‖
  have hlim : Tendsto (fun r : ℝ => r ^ 2 * (X ^ 2 * A)) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (hid.pow 2).mul_const (X ^ 2 * A)
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, r ^ 2 * (X ^ 2 * A) < η / 2 :=
    hlim.eventually (Iio_mem_nhds (half_pos hη))
  filter_upwards [self_mem_nhdsWithin, hev] with r hr hrsmall
  have hr0 : 0 < r := hr
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ (-(s + (r : ℂ)) - 1) * f x
  let G : ℝ → ℝ := fun x => (η / 2) * (x ^ (-r - 1) * Real.log x) +
    X ^ 2 * (x ^ (-2 : ℝ) * ‖f x‖)
  have hG : IntegrableOn G (Ioi 1) :=
    ((integrableOn_rpow_mul_log_Ioi_one hr0).const_mul (η / 2)).add (hbase.const_mul (X ^ 2))
  have hpoint : ∀ x ∈ Ioi (1 : ℝ), ‖F x‖ ≤ G x := by
    intro x hx
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := zero_lt_one.trans hx1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hpow : 0 ≤ x ^ (-r - 1) := Real.rpow_nonneg hx0.le _
    have hnorm : ‖F x‖ = x ^ (-1 / 2 - r) * ‖f x‖ := by
      dsimp only [F]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      congr 2
      simp only [Complex.sub_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
        Complex.one_re, hs]
      ring
    rw [hnorm]
    by_cases hhead : x ≤ X
    · have hpow1 : x ^ (-1 / 2 - r) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
      have hscale : 1 ≤ X ^ 2 * x ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hx0.le, Real.rpow_two, ← div_eq_mul_inv]
        apply (le_div_iff₀ (sq_pos_of_pos hx0)).mpr
        nlinarith
      have hh : x ^ (-1 / 2 - r) * ‖f x‖ ≤ X ^ 2 * (x ^ (-2 : ℝ) * ‖f x‖) := by
        calc
          _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right hpow1 (norm_nonneg _)
          _ ≤ (X ^ 2 * x ^ (-2 : ℝ)) * ‖f x‖ :=
            mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
          _ = _ := by ring
      exact hh.trans (le_add_of_nonneg_left (by positivity))
    · have htail := hX₀ x ((le_max_left X₀ 1).trans (le_of_not_ge hhead))
      have hprod : x ^ (-1 / 2 - r) * (Real.log x / Real.sqrt x) =
          x ^ (-r - 1) * Real.log x := by
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv]
        have heq : x ^ (-1 / 2 - r) * (x ^ (1 / 2 : ℝ))⁻¹ = x ^ (-r - 1) := by
          rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
          congr 1
          ring
        calc
          _ = (x ^ (-1 / 2 - r) * (x ^ (1 / 2 : ℝ))⁻¹) * Real.log x := by
            simp only [div_eq_mul_inv]
            ac_rfl
          _ = _ := by rw [heq]
      have ht : x ^ (-1 / 2 - r) * ‖f x‖ ≤ (η / 2) * (x ^ (-r - 1) * Real.log x) := by
        calc
          _ ≤ x ^ (-1 / 2 - r) * ((η / 2) * (Real.log x / Real.sqrt x)) :=
            mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hx0.le _)
          _ = (η / 2) * (x ^ (-1 / 2 - r) * (Real.log x / Real.sqrt x)) := by ring
          _ = _ := by rw [hprod]
      exact ht.trans (le_add_of_nonneg_right (by positivity))
  have hi : ‖∫ x : ℝ in Ioi 1, F x‖ ≤ (η / 2) * (1 / r ^ 2) + X ^ 2 * A := by
    have h := norm_integral_le_of_norm_le hG
      (ae_restrict_of_forall_mem measurableSet_Ioi hpoint)
    simpa only [G, integral_add
      ((integrableOn_rpow_mul_log_Ioi_one hr0).const_mul (η / 2)) (hbase.const_mul (X ^ 2)),
      integral_const_mul, integral_rpow_mul_log_Ioi_one hr0, A] using h
  rw [dist_zero_right, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hi' := mul_le_mul_of_nonneg_left hi (sq_nonneg r)
  have heq : r ^ 2 * ((η / 2) * (1 / r ^ 2) + X ^ 2 * A) = η / 2 + r ^ 2 * (X ^ 2 * A) := by
    field_simp [hr0.ne']
  change r ^ 2 * ‖∫ x : ℝ in Ioi 1, F x‖ < η
  rw [heq] at hi'
  linarith

theorem pmLogMobiusMeanDefect_eq_zero {x : ℝ} (hx : x ≤ 1) :
    pmLogMobiusMeanDefect x = 0 := by
  rcases lt_or_eq_of_le hx with h | rfl
  · simp [pmLogMobiusMeanDefect, Sieve.moebiusShiftedLogKernelReal, pmPrimeLogMean,
      Nat.floor_eq_zero.mpr h]
  · norm_num [pmLogMobiusMeanDefect, Sieve.moebiusShiftedLogKernelReal, pmPrimeLogMean]

theorem pmLogMobiusMeanDefect_integrable_base :
    IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ) * ‖(pmLogMobiusMeanDefect x : ℂ)‖) (Ioi 1) := by
  have h : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (-(1 : ℂ) - 1) •
      (pmLogMobiusMeanDefect x : ℂ)‖) (Ioi 0) :=
    (hasMellin_pmLogMobiusMeanDefect (s := 1) (by norm_num)).1.norm
  have h' := h.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  apply h'.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  norm_num

theorem pmLogMobiusMeanDefect_quadratic_abel
    (hE : Tendsto logMobiusFermiErrorEnergy atTop (𝓝 0))
    {s : ℂ} (hs : s.re = -1 / 2) :
    Tendsto (fun r : ℝ => (r : ℂ) ^ 2 *
      ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (-(s + (r : ℂ)) - 1) * (pmLogMobiusMeanDefect x : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  apply pm_quadratic_abel_log_boundary pmLogMobiusMeanDefect_integrable_base _ hs
  apply IsLittleO.of_norm_left
  simpa only [Complex.norm_real] using (pmLogMobiusMeanDefect_isLittleO_of_error hE).norm_left


theorem pm_exists_quadratic_factor_of_zero_deriv {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hzero : f z = 0) (hderiv : deriv f z = 0) :
    ∃ g : ℂ → ℂ, ContinuousAt g z ∧ ∀ w, f w = (w - z) ^ 2 * g w := by
  obtain ⟨p, hp⟩ := hf
  let g := dslope (dslope f z) z
  refine ⟨g, hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope.continuousAt, ?_⟩
  intro w
  have h₁ := sub_smul_dslope f z w
  have h₂ := sub_smul_dslope (dslope f z) z w
  simp only [smul_eq_mul, hzero, sub_zero] at h₁
  simp only [smul_eq_mul, dslope_same, hderiv, sub_zero] at h₂
  calc
    f w = (w - z) * dslope f z w := h₁.symm
    _ = (w - z) * ((w - z) * g w) := congrArg ((w - z) * ·) h₂.symm
    _ = _ := by ring

theorem pm_deriv_zeta_ne_zero_of_quadratic_abel {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) (hzero : riemannZeta ρ = 0) (H : ℝ → ℂ)
    (habel : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * H ε) (𝓝[>] 0) (𝓝 0))
    (hidentity : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (ρ - 1 + (ε : ℂ)) ^ 2 * (ρ + (ε : ℂ)) ^ 2 *
          riemannZeta (ρ + (ε : ℂ)) * H ε =
        (ρ + (ε : ℂ)) ^ 2 + (ρ - 1 + (ε : ℂ)) ^ 2 *
          deriv riemannZeta (ρ + (ε : ℂ))) :
    deriv riemannZeta ρ ≠ 0 := by
  intro hd
  have hρ1 : ρ ≠ 1 := by intro h; norm_num [h] at hρ
  have hρ0 : ρ ≠ 0 := by intro h; norm_num [h] at hρ
  have hA := analyticOn_riemannZeta ρ hρ1
  obtain ⟨g, hg, hfac⟩ := pm_exists_quadratic_factor_of_zero_deriv hA hzero hd
  have he : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto Complex.ofReal (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    simpa only [Complex.ofReal_zero] using hc.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    simpa using tendsto_const_nhds.add he
  have hs : Tendsto (fun ε : ℝ => ρ - 1 + (ε : ℂ)) (𝓝[>] 0) (𝓝 (ρ - 1)) := by
    simpa using tendsto_const_nhds.add he
  have hl : Tendsto (fun ε : ℝ =>
      (ρ - 1 + (ε : ℂ)) ^ 2 * (ρ + (ε : ℂ)) ^ 2 *
        (g (ρ + (ε : ℂ)) * ((ε : ℂ) ^ 2 * H ε))) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((hs.pow 2).mul (hr.pow 2)).mul ((hg.tendsto.comp hr).mul habel)
  have hl' : Tendsto (fun ε : ℝ =>
      (ρ - 1 + (ε : ℂ)) ^ 2 * (ρ + (ε : ℂ)) ^ 2 *
        riemannZeta (ρ + (ε : ℂ)) * H ε) (𝓝[>] 0) (𝓝 0) := by
    apply hl.congr'
    exact Eventually.of_forall (fun ε => by
      dsimp only
      rw [hfac]
      simp only [add_sub_cancel_left]
      ring)
  have hright : Tendsto (fun ε : ℝ =>
      (ρ + (ε : ℂ)) ^ 2 + (ρ - 1 + (ε : ℂ)) ^ 2 *
        deriv riemannZeta (ρ + (ε : ℂ))) (𝓝[>] 0) (𝓝 (ρ ^ 2)) := by
    simpa only [hd, mul_zero, add_zero, Function.comp_def] using
      (hr.pow 2).add ((hs.pow 2).mul (hA.deriv.continuousAt.tendsto.comp hr))
  have hz : (0 : ℂ) = ρ ^ 2 := tendsto_nhds_unique (hl'.congr' hidentity) hright
  exact pow_ne_zero 2 hρ0 hz.symm


theorem pmLogDefectReciprocal_mellin_eq_integral (s : ℂ) :
    mellin pmLogDefectReciprocal s =
      ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (-s - 1) * (pmLogMobiusMeanDefect x : ℂ) := by
  rw [show mellin pmLogDefectReciprocal s =
      mellin (fun x : ℝ => (pmLogMobiusMeanDefect x : ℂ)) (-s) from
        mellin_comp_inv (fun x : ℝ => (pmLogMobiusMeanDefect x : ℂ)) s]
  change (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (-s - 1) * (pmLogMobiusMeanDefect x : ℂ)) = _
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  intro x hx
  have hx1 : x ≤ 1 := le_of_not_gt hx.2
  simp [pmLogMobiusMeanDefect_eq_zero hx1]

theorem pmLogMobius_critical_simple_of_error
    (hE : Tendsto logMobiusFermiErrorEnergy atTop (𝓝 0))
    {ρ : ℂ} (hρ : ρ.re = 1 / 2) (hzero : riemannZeta ρ = 0) :
    deriv riemannZeta ρ ≠ 0 := by
  let H : ℝ → ℂ := fun r => mellin pmLogDefectReciprocal (ρ - 1 + (r : ℂ))
  apply pm_deriv_zeta_ne_zero_of_quadratic_abel hρ hzero H
  · have hs : (ρ - 1).re = -1 / 2 := by simp only [Complex.sub_re, Complex.one_re, hρ]; ring
    have h := pmLogMobiusMeanDefect_quadratic_abel hE hs
    simpa only [H, pmLogDefectReciprocal_mellin_eq_integral] using h
  · have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 / 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [self_mem_nhdsWithin, hev] with r hr hrlt
    have hr0 : 0 < r := hr
    have hs : -1 / 2 < (ρ - 1 + (r : ℂ)).re := by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, hρ]
      linarith
    have hs0 : ρ - 1 + (r : ℂ) ≠ 0 := by
      intro heq
      have heq' := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.zero_re, hρ] at heq'
      linarith
    have h := pmLogDefectMellin_cleared_identity hE hs hs0
    have heq : ρ - 1 + (r : ℂ) + 1 = ρ + (r : ℂ) := by ring
    rw [heq] at h
    exact h

end RHTower
