import GaloisForLFunctions.HTGeometry.PoissonJensenUpperBound
import GaloisForLFunctions.HTGeometry.PoissonInteriorLogKernel
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeBoundary
import GaloisForLFunctions.HTGeometry.FiniteOrderEntireQuotient

/-!
# Growth of the pole-cleared quotient without a zero-free assumption

Blaschke-corrected zero factors give a zero-free disk majorant with the same
boundary norm. This removes the zero-free restriction from the Poisson growth
step used for an entire quotient. It is a classical analytic bridge for WP07;
the finite-pole quotient construction remains a separate obligation.
-/

noncomputable section

open Complex Metric Set Filter Topology ValueDistribution
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.PoissonJensen
open GaloisForLFunctions.QuotientProximity GaloisForLFunctions.Nevanlinna

namespace RHTower.WeilHigherDenominator

private lemma norm_sub_le_innerLogKernel {c a z : ℂ} {R : ℝ} (hR : 0 < R)
    (ha : ‖a - c‖ < R) (hz : ‖z - c‖ ≤ R) :
    ‖z - a‖ ≤ ‖innerLogKernel c a R z‖ := by
  have hR₀ : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have ha' : ‖(a - c) / (R : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_lt_one hR]
    exact ha
  have hz' : ‖(z - c) / (R : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_le_one hR]
    exact hz
  have hb := norm_blaschkeFactor_le_one ha' hz'
  have hconj : star ((a - c) / (R : ℂ)) =
      ((starRingEnd ℂ) a - (starRingEnd ℂ) c) / (R : ℂ) := by
    change (starRingEnd ℂ) ((a - c) / (R : ℂ)) = _
    rw [map_div₀, map_sub, Complex.conj_ofReal]
  have he : (((z - c) / (R : ℂ) - (a - c) / (R : ℂ)) /
      (1 - star ((a - c) / (R : ℂ)) * ((z - c) / (R : ℂ)))) =
        (z - a) / innerLogKernel c a R z := by
    rw [hconj, innerLogKernel, map_sub]
    field_simp
    ring
  rw [he, norm_div] at hb
  have hk : innerLogKernel c a R z ≠ 0 := innerLogKernel_ne_zero hR (by
    nlinarith [norm_nonneg (a - c), norm_nonneg (z - c)])
  exact (div_le_one (norm_pos_iff.mpr hk)).mp hb

/-- A holomorphic function has a zero-free disk majorant preserving every boundary norm. -/
theorem exists_zeroFree_disk_majorant {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f univ)
    (hnz : ∀ a : ℂ, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hsph : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall c R) ∧
      (∀ z ∈ closedBall c R, h z ≠ 0) ∧
      (∀ z ∈ closedBall c R, ‖f z‖ ≤ ‖h z‖) ∧
      (∀ z ∈ sphere c R, ‖h z‖ = ‖f z‖) := by
  classical
  obtain ⟨T, m, g, hg, hgfree, hTmem, hfac⟩ :=
    exists_zero_free_factor_closedBall (c := c) (R := R) isOpen_univ (subset_univ _) hf
      (fun a _ => hnz a)
  have hapos : ∀ a ∈ T, m a ≠ 0 → ‖a - c‖ < R := by
    intro a ha hm
    apply lt_of_le_of_ne (mem_closedBall_iff_norm.mp (hTmem a ha))
    intro he
    have hfa := hsph a (mem_sphere_iff_norm.mpr he)
    rw [hfac a (mem_univ a)] at hfa
    have hterm := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hfa).1 a ha
    simp [hm] at hterm
  let h : ℂ → ℂ := fun z => (∏ a ∈ T, innerLogKernel c a R z ^ m a) * g z
  have hfree : ∀ z ∈ closedBall c R, h z ≠ 0 := by
    intro z hz
    apply mul_ne_zero _ (hgfree z hz)
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    by_cases hm : m a = 0
    · simp [hm]
    · apply pow_ne_zero
      apply innerLogKernel_ne_zero hR
      have := hapos a ha hm
      have := mem_closedBall_iff_norm.mp hz
      nlinarith [norm_nonneg (a - c), norm_nonneg (z - c)]
  refine ⟨h, ?_, hfree, ?_, ?_⟩
  · apply AnalyticOnNhd.mul _ (hg.mono (subset_univ _))
    apply Finset.analyticOnNhd_fun_prod
    intro a _ z _
    dsimp [innerLogKernel]
    fun_prop
  · intro z hz
    rw [hfac z (mem_univ z)]
    dsimp [h]
    simp only [norm_mul, norm_prod, norm_pow]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Finset.prod_le_prod (fun a _ => pow_nonneg (norm_nonneg _) _)
    intro a ha
    by_cases hm : m a = 0
    · simp [hm]
    · exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_sub_le_innerLogKernel hR (hapos a ha hm) (mem_closedBall_iff_norm.mp hz)) _
  · intro z hz
    rw [hfac z (mem_univ z)]
    dsimp [h]
    simp only [norm_mul, norm_prod, norm_pow, norm_innerLogKernel_sphere hR hz]

/-- The full Poisson growth bound, including functions with interior zeros. -/
theorem norm_le_exp_poisson_proximity {f : ℂ → ℂ} {c w : ℂ} {R r : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f univ)
    (hnz : ∀ a : ℂ, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hsph : ∀ z ∈ sphere c R, f z ≠ 0)
    (hw : w ∈ ball c R) (hwr : ‖w - c‖ ≤ r) (hrR : r < R) :
    ‖f w‖ ≤ Real.exp ((R + r) / (R - r) *
      Real.circleAverage (fun z => Real.posLog ‖f z‖) c R) := by
  obtain ⟨h, hh, hfree, hmajor, hboundary⟩ := exists_zeroFree_disk_majorant hR hf hnz hsph
  have hpo := log_norm_le_poisson_proximity hh hfree hw hwr hrR
  have hc : Real.circleAverage (fun z => Real.posLog ‖h z‖) c R =
      Real.circleAverage (fun z => Real.posLog ‖f z‖) c R := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    change Real.posLog ‖h z‖ = Real.posLog ‖f z‖
    rw [hboundary z (by simpa only [abs_of_pos hR] using hz)]
  rw [hc] at hpo
  have hw' := ball_subset_closedBall hw
  calc
    _ ≤ ‖h w‖ := hmajor w hw'
    _ = Real.exp (Real.log ‖h w‖) := (Real.exp_log (norm_pos_iff.mpr (hfree w hw'))).symm
    _ ≤ _ := Real.exp_le_exp.mpr hpo

/-- Finite order descends to every entire quotient; zeros of the quotient are allowed. -/
theorem finiteOrderEnvelope_entire_quotient {F G H : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ)
    (hH : AnalyticOnNhd ℂ H univ)
    (hFne : ∃ z, F z ≠ 0) (hGne : ∃ z, G z ≠ 0)
    (hfac : ∀ z, G z = H z * F z)
    (hFfinite : FiniteOrderEnvelope F) (hGfinite : FiniteOrderEnvelope G) :
    FiniteOrderEnvelope H := by
  obtain ⟨CF, dF, hCF, hFbound⟩ := hFfinite
  obtain ⟨CG, dG, hCG, hGbound⟩ := hGfinite
  obtain ⟨zF, hzF⟩ := hFne
  obtain ⟨zG, hzG⟩ := hGne
  have hFdiff : Differentiable ℂ F := Complex.analyticOnNhd_univ_iff_differentiable.mp hF
  have hGdiff : Differentiable ℂ G := Complex.analyticOnNhd_univ_iff_differentiable.mp hG
  have hHdiff : Differentiable ℂ H := Complex.analyticOnNhd_univ_iff_differentiable.mp hH
  have hHne : H zG ≠ 0 := by
    intro h
    apply hzG
    rw [hfac zG, h, zero_mul]
  have hHnz : ∀ a : ℂ, ¬ ∀ᶠ z in 𝓝 a, H z = 0 := by
    intro a ha
    exact analyticOrderAt_ne_top_of_entire hHdiff hHne a (analyticOrderAt_eq_top.mpr ha)
  have hFord : ∀ z, meromorphicOrderAt F z ≠ ⊤ := by
    intro z
    rw [(hF z (mem_univ z)).meromorphicOrderAt_eq]
    simp [analyticOrderAt_ne_top_of_entire hFdiff hzF z]
  have hGord : ∀ z, meromorphicOrderAt G z ≠ ⊤ := by
    intro z
    rw [(hG z (mem_univ z)).meromorphicOrderAt_eq]
    simp [analyticOrderAt_ne_top_of_entire hGdiff hzG z]
  obtain ⟨K, hK⟩ := proximity_quotient_le hF hG hH hFord hGord hfac
  let d : ℕ := max dF dG
  let C : ℝ := 3 * (CG * 4 ^ dG + CF * 4 ^ dF + |K|)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, d, hC, fun z => ?_⟩
  obtain ⟨R, hRlo, hRhi, hsph⟩ :=
    exists_radius_no_boundary_zero (c := 0) hH hHnz (2 * (1 + ‖z‖))
  have hz₀ : 0 ≤ ‖z‖ := norm_nonneg z
  have hR₀ : 0 < R := by linarith
  have hR₁ : 1 ≤ R := by linarith
  have hzR : ‖z‖ < R := by linarith
  have hpo := norm_le_exp_poisson_proximity hR₀ hH hHnz hsph
    (show z ∈ ball (0 : ℂ) R by simpa using hzR) (show ‖z - 0‖ ≤ ‖z‖ by simp) hzR
  have hav : Real.circleAverage (fun w => Real.posLog ‖H w‖) 0 R = proximity H ⊤ R := by
    have he := characteristic_top_eq_circleAverage_of_analyticOnNhd hH
    rw [characteristic_top_eq_proximity_of_analyticOnNhd hH] at he
    exact (congrFun he R).symm
  rw [hav] at hpo
  have hmerF : MeromorphicOn F (sphere (0 : ℂ) R) :=
    fun w _ => (hF w (mem_univ w)).meromorphicAt
  have hmerG : MeromorphicOn G (sphere (0 : ℂ) R) :=
    fun w _ => (hG w (mem_univ w)).meromorphicAt
  have hpF : proximity F ⊤ R ≤ CF * (1 + R) ^ dF := by
    refine le_trans (proximity_top_le_posLog_of_norm
      (M := Real.exp (CF * (1 + R) ^ dF)) hR₀.le hmerF ?_) ?_
    · intro w hw
      simpa [hw] using hFbound w
    · rw [Real.posLog, Real.log_exp]
      exact max_le (mul_nonneg hCF (by positivity)) le_rfl
  have hpG : proximity G ⊤ R ≤ CG * (1 + R) ^ dG := by
    refine le_trans (proximity_top_le_posLog_of_norm
      (M := Real.exp (CG * (1 + R) ^ dG)) hR₀.le hmerG ?_) ?_
    · intro w hw
      simpa [hw] using hGbound w
    · rw [Real.posLog, Real.log_exp]
      exact max_le (mul_nonneg hCG (by positivity)) le_rfl
  have hshape : 1 + R ≤ 4 * (1 + ‖z‖) := by linarith
  have hbase : 1 ≤ 1 + ‖z‖ := by linarith
  have hpowF : (1 + R) ^ dF ≤ 4 ^ dF * (1 + ‖z‖) ^ d := by
    calc
      _ ≤ (4 * (1 + ‖z‖)) ^ dF := pow_le_pow_left₀ (by positivity) hshape dF
      _ = 4 ^ dF * (1 + ‖z‖) ^ dF := by rw [mul_pow]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  have hpowG : (1 + R) ^ dG ≤ 4 ^ dG * (1 + ‖z‖) ^ d := by
    calc
      _ ≤ (4 * (1 + ‖z‖)) ^ dG := pow_le_pow_left₀ (by positivity) hshape dG
      _ = 4 ^ dG * (1 + ‖z‖) ^ dG := by rw [mul_pow]
      _ ≤ _ := by gcongr; exact le_max_right _ _
  have hpF' : proximity F ⊤ R ≤ (CF * 4 ^ dF) * (1 + ‖z‖) ^ d := by
    calc
      _ ≤ CF * (1 + R) ^ dF := hpF
      _ ≤ CF * (4 ^ dF * (1 + ‖z‖) ^ d) := mul_le_mul_of_nonneg_left hpowF hCF
      _ = _ := by ring
  have hpG' : proximity G ⊤ R ≤ (CG * 4 ^ dG) * (1 + ‖z‖) ^ d := by
    calc
      _ ≤ CG * (1 + R) ^ dG := hpG
      _ ≤ CG * (4 ^ dG * (1 + ‖z‖) ^ d) := mul_le_mul_of_nonneg_left hpowG hCG
      _ = _ := by ring
  have hpow₁ : 1 ≤ (1 + ‖z‖) ^ d := one_le_pow₀ hbase
  have hK' : K ≤ |K| * (1 + ‖z‖) ^ d :=
    (le_abs_self K).trans (by nlinarith [abs_nonneg K])
  have hpH : proximity H ⊤ R ≤
      (CG * 4 ^ dG + CF * 4 ^ dF + |K|) * (1 + ‖z‖) ^ d := by
    have hq := hK R hR₁
    nlinarith
  have hcoef : (R + ‖z‖) / (R - ‖z‖) ≤ 3 := by
    rw [div_le_iff₀ (sub_pos.mpr hzR)]
    linarith
  apply hpo.trans (Real.exp_le_exp.mpr ?_)
  calc
    _ ≤ 3 * proximity H ⊤ R := mul_le_mul_of_nonneg_right hcoef
      (proximity_nonneg_of_entire hH hR₁)
    _ ≤ 3 * ((CG * 4 ^ dG + CF * 4 ^ dF + |K|) * (1 + ‖z‖) ^ d) :=
      mul_le_mul_of_nonneg_left hpH (by norm_num)
    _ = _ := by dsimp [C]; ring

end RHTower.WeilHigherDenominator
