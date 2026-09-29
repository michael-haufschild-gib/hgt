import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

/-!
# Logarithmic derivatives of zero-free quotients

If `exp g · Z = N` on a closed disc, then `g` is a logarithm of the zero-free quotient `N/Z`, even
where `N` and `Z` vanish together.  Upper bounds for `|N|`, `|Z|` on the boundary circle and a
lower bound for `|Z|` at the centre control `g'` on smaller discs
(`norm_deriv_le_of_exp_mul_eq`).  No lower bound for `Z` away from the centre is used:

* Poisson's formula writes `Re g(w)` as an average of `log|N| - log|Z|` against a kernel bounded by
  `(R + |w-c|)/(R - |w-c|)`, and Jensen's inequality `log|Z(c)| ≤ ⨍ log|Z|` absorbs the
  negative part of `log|Z|` (`re_le_of_exp_mul_eq`);
* Borel--Carathéodory turns the one-sided bound into a bound for `|g|`, and Cauchy's estimate into
  one for `|g'|`.
-/

open Complex Metric Real Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem log_norm_le_circleAverage_log_norm {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ circleAverage (fun z => Real.log ‖f z‖) c R := by
  have hRabs : |R| = R := abs_of_pos hR
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rwa [hRabs]
  rw [hf'.circleAverage_log_norm hR.ne' hfc]
  have hsum : 0 ≤ ∑ᶠ u, (MeromorphicOn.divisor f (closedBall c |R|) u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall c |R|
    · have hd : (0 : ℝ) ≤ (MeromorphicOn.divisor f (closedBall c |R|) u : ℝ) := by
        exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf' u
      have hl : 0 ≤ Real.log (R * ‖c - u‖⁻¹) := by
        rcases eq_or_ne u c with rfl | hne
        · simp
        · have hcu : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
          have hle : ‖c - u‖ ≤ R := by
            rw [mem_closedBall, dist_eq_norm, hRabs] at hu
            rwa [norm_sub_rev]
          apply Real.log_nonneg
          rw [← div_eq_mul_inv, le_div_iff₀ hcu, one_mul]
          exact hle
      exact mul_nonneg hd hl
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  linarith

theorem poissonKernel_nonneg_of_mem_sphere {c w z : ℂ} {R : ℝ} (hz : z ∈ sphere c R)
    (hw : w ∈ ball c R) : 0 ≤ poissonKernel c w z := by
  rw [poissonKernel_def]
  apply div_nonneg _ (sq_nonneg _)
  rw [mem_sphere, dist_eq_norm] at hz
  rw [mem_ball, dist_eq_norm] at hw
  rw [hz]
  nlinarith [norm_nonneg (w - c)]

theorem poissonKernel_le_of_mem_sphere {c w z : ℂ} {R : ℝ} (hz : z ∈ sphere c R)
    (hw : w ∈ ball c R) : poissonKernel c w z ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact re_herglotzRieszKernel_le hz hw

/-- **Poisson ceiling for a zero-free quotient.**  If `exp g · Z = N` on a closed disc, `N` and `Z`
are at most `e^A` on the boundary and `Z(c) ≠ 0`, then inside the disc
`Re g(w) ≤ (R + |w-c|)/(R - |w-c|) · (2A - log |Z(c)|)`.  No lower bound for `Z` on the boundary is
needed: Jensen's inequality at the centre replaces it. -/
theorem re_le_of_exp_mul_eq {g N Z : ℂ → ℂ} {c w : ℂ} {R A : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hN : AnalyticOnNhd ℂ N (closedBall c R))
    (hZ : AnalyticOnNhd ℂ Z (closedBall c R))
    (hexp : ∀ z ∈ closedBall c R, Complex.exp (g z) * Z z = N z) (hZc : Z c ≠ 0)
    (hNA : ∀ z ∈ sphere c R, ‖N z‖ ≤ Real.exp A) (hZA : ∀ z ∈ sphere c R, ‖Z z‖ ≤ Real.exp A)
    (hA : 0 ≤ A) (hw : w ∈ ball c R) :
    (g w).re ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * (2 * A - Real.log ‖Z c‖) := by
  have hRabs : |R| = R := abs_of_pos hR
  set K : ℝ := (R + ‖w - c‖) / (R - ‖w - c‖) with hK
  have hwR : ‖w - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hw
  have hK0 : 0 ≤ K := div_nonneg (by linarith [norm_nonneg (w - c)]) (by linarith)
  set P : ℂ → ℝ := poissonKernel c w with hP
  -- Poisson representation of `Re g`
  have hdc : DiffContOnCl ℂ g (ball c R) := by
    have hd : DifferentiableOn ℂ g (closedBall c R) := hg.differentiableOn
    exact ⟨hd.mono ball_subset_closedBall, by rw [closure_ball c hR.ne']; exact hd.continuousOn⟩
  have hpois := hdc.circleAverage_poissonKernel_smul hw
  have hcontP : ContinuousOn (fun z => P z • g z) (sphere c |R|) := by
    rw [hRabs]
    intro z hz
    have hzw : z - c - (w - c) ≠ 0 := by
      intro h
      have : z = w := by linear_combination h
      rw [this, mem_sphere, dist_eq_norm] at hz
      linarith
    have : ContinuousAt (fun z => P z • g z) z := by
      rw [hP]
      unfold poissonKernel
      exact ((((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2).sub
        continuous_const).continuousAt.div
        ((continuous_norm.comp ((continuous_id.sub continuous_const).sub
          continuous_const)).pow 2).continuousAt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hzw))).smul
        (hg z (sphere_subset_closedBall hz)).continuousAt
    exact this.continuousWithinAt
  have hint : CircleIntegrable (fun z => P z • g z) c R := hcontP.circleIntegrable'
  have hpois' : circleAverage (fun z => P z • g z) c R = g w := hpois
  have hre : (g w).re = circleAverage (fun z => P z * (g z).re) c R := by
    have h := Complex.reCLM.circleAverage_comp_comm hint
    rw [hpois'] at h
    rw [← Complex.reCLM_apply, ← h]
    congr 1
    funext z
    simp [hP]
  have hcontP' : ContinuousOn (fun z => P z * (g z).re) (sphere c |R|) := by
    refine (Complex.continuous_re.comp_continuousOn hcontP).congr fun z _ => ?_
    simp [Function.comp]
  have hint1 : CircleIntegrable (fun z => P z * (g z).re) c R := hcontP'.circleIntegrable'
  -- replace `Re g` by `log|N| - log|Z|` away from the zeros of `Z`
  have hcodisc : Z ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere c |R|) := by
    have h := hZ.preimage_zero_mem_codiscreteWithin (x := c) hZc (mem_closedBall_self hR.le)
      (isConnected_closedBall hR.le)
    rw [hRabs]
    exact codiscreteWithin_mono sphere_subset_closedBall h
  have heq : (fun z => P z * (g z).re) =ᶠ[codiscreteWithin (sphere c |R|)]
      (fun z => P z * (Real.log ‖N z‖ - Real.log ‖Z z‖)) := by
    filter_upwards [hcodisc, self_mem_codiscreteWithin (sphere c |R|)] with z hz hzs
    have hzB : z ∈ closedBall c R := by
      rw [hRabs] at hzs
      exact sphere_subset_closedBall hzs
    have hZz : Z z ≠ 0 := hz
    have h := hexp z hzB
    have hnorm : Real.exp (g z).re * ‖Z z‖ = ‖N z‖ := by
      rw [← h, norm_mul, Complex.norm_exp]
    congr 1
    rw [← hnorm, Real.log_mul (Real.exp_pos _).ne' (norm_ne_zero_iff.mpr hZz), Real.log_exp]
    ring
  have hint2 : CircleIntegrable (fun z => P z * (Real.log ‖N z‖ - Real.log ‖Z z‖)) c R :=
    hint1.congr_codiscreteWithin heq
  have hNm : MeromorphicOn N (sphere c |R|) := by
    rw [hRabs]; exact (hN.mono sphere_subset_closedBall).meromorphicOn
  have hZm : MeromorphicOn Z (sphere c |R|) := by
    rw [hRabs]; exact (hZ.mono sphere_subset_closedBall).meromorphicOn
  have hiN : CircleIntegrable (fun z => log⁺ ‖N z‖) c R := hNm.circleIntegrable_posLog_norm
  have hiZ : CircleIntegrable (fun z => log⁺ ‖Z z‖) c R := hZm.circleIntegrable_posLog_norm
  have hiZi : CircleIntegrable (fun z => log⁺ ‖Z z‖⁻¹) c R := by
    have := hZm.inv.circleIntegrable_posLog_norm
    simpa using this
  have hiZl : CircleIntegrable (fun z => Real.log ‖Z z‖) c R := hZm.circleIntegrable_log_norm
  have hmaj : CircleIntegrable (fun z => K * (log⁺ ‖N z‖ + log⁺ ‖Z z‖⁻¹)) c R := by
    have h := (hiN.add hiZi).const_smul (a := K)
    refine h.congr_codiscreteWithin (Filter.Eventually.of_forall fun z => ?_)
    simp [smul_eq_mul]
  have hpt : ∀ z ∈ sphere c |R|, P z * (Real.log ‖N z‖ - Real.log ‖Z z‖) ≤
      K * (log⁺ ‖N z‖ + log⁺ ‖Z z‖⁻¹) := by
    intro z hz
    rw [hRabs] at hz
    have hP0 : 0 ≤ P z := poissonKernel_nonneg_of_mem_sphere hz hw
    have hPK : P z ≤ K := poissonKernel_le_of_mem_sphere hz hw
    have h1 : Real.log ‖N z‖ ≤ log⁺ ‖N z‖ := by rw [Real.posLog_apply]; exact le_max_right _ _
    have h2 : -Real.log ‖Z z‖ ≤ log⁺ ‖Z z‖⁻¹ := by
      rw [← Real.log_inv, Real.posLog_apply]; exact le_max_right _ _
    have hm0 : 0 ≤ log⁺ ‖N z‖ + log⁺ ‖Z z‖⁻¹ := add_nonneg Real.posLog_nonneg Real.posLog_nonneg
    calc P z * (Real.log ‖N z‖ - Real.log ‖Z z‖) ≤ P z * (log⁺ ‖N z‖ + log⁺ ‖Z z‖⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) hP0
      _ ≤ K * (log⁺ ‖N z‖ + log⁺ ‖Z z‖⁻¹) := mul_le_mul_of_nonneg_right hPK hm0
  have hmono := circleAverage_mono hint2 hmaj hpt
  have hcong := circleAverage_congr_codiscreteWithin heq hR.ne'
  -- evaluate the majorant
  have hid : (fun z => log⁺ ‖Z z‖⁻¹) = fun z => log⁺ ‖Z z‖ - Real.log ‖Z z‖ := by
    funext z
    have := Real.posLog_sub_posLog_inv (x := ‖Z z‖)
    linarith
  have hsplit : circleAverage (fun z => K * (log⁺ ‖N z‖ + log⁺ ‖Z z‖⁻¹)) c R =
      K * (circleAverage (fun z => log⁺ ‖N z‖) c R + (circleAverage (fun z => log⁺ ‖Z z‖) c R -
        circleAverage (fun z => Real.log ‖Z z‖) c R)) := by
    have h1 : circleAverage (fun z => K * (log⁺ ‖N z‖ + log⁺ ‖Z z‖⁻¹)) c R =
        K * circleAverage (fun z => log⁺ ‖N z‖ + log⁺ ‖Z z‖⁻¹) c R := by
      have := circleAverage_fun_smul (a := K) (f := fun z => log⁺ ‖N z‖ + log⁺ ‖Z z‖⁻¹)
        (c := c) (R := R)
      simpa [smul_eq_mul] using this
    rw [h1, circleAverage_fun_add hiN hiZi, hid, circleAverage_fun_sub hiZ hiZl]
  have hNavg : circleAverage (fun z => log⁺ ‖N z‖) c R ≤ A := by
    refine circleAverage_mono_on_of_le_circle hiN fun z hz => ?_
    rw [hRabs] at hz
    rw [Real.posLog_apply]
    refine max_le hA ?_
    rcases eq_or_ne ‖N z‖ 0 with h0 | h0
    · rw [h0, Real.log_zero]; exact hA
    · rw [Real.log_le_iff_le_exp (norm_pos_iff.mpr (norm_ne_zero_iff.mp h0))]
      exact hNA z hz
  have hZavg : circleAverage (fun z => log⁺ ‖Z z‖) c R ≤ A := by
    refine circleAverage_mono_on_of_le_circle hiZ fun z hz => ?_
    rw [hRabs] at hz
    rw [Real.posLog_apply]
    refine max_le hA ?_
    rcases eq_or_ne ‖Z z‖ 0 with h0 | h0
    · rw [h0, Real.log_zero]; exact hA
    · rw [Real.log_le_iff_le_exp (norm_pos_iff.mpr (norm_ne_zero_iff.mp h0))]
      exact hZA z hz
  have hJ := log_norm_le_circleAverage_log_norm hR hZ hZc
  rw [hre, hcong]
  calc circleAverage (fun z => P z * (Real.log ‖N z‖ - Real.log ‖Z z‖)) c R
      ≤ circleAverage (fun z => K * (log⁺ ‖N z‖ + log⁺ ‖Z z‖⁻¹)) c R := hmono
    _ = K * (circleAverage (fun z => log⁺ ‖N z‖) c R + (circleAverage (fun z => log⁺ ‖Z z‖) c R -
        circleAverage (fun z => Real.log ‖Z z‖) c R)) := hsplit
    _ ≤ K * (A + (A - Real.log ‖Z c‖)) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        linarith
    _ = K * (2 * A - Real.log ‖Z c‖) := by ring

/-- **Logarithmic-derivative ceiling for a zero-free quotient.**  Let `exp g · Z = N` on the closed
disc of radius `d + 2δ` about `c`, with `|N|, |Z| ≤ e^A` on its boundary, `|Z(c)| ≥ e^{-A}` and
`|g(c)| ≤ A`.  Then `|g'| ≤ C(d, δ)(A + 1)` on the disc of radius `d`.  The proof chains the Poisson
ceiling, Borel--Carathéodory on the disc of radius `d + δ` and Cauchy's estimate. -/
theorem norm_deriv_le_of_exp_mul_eq {g N Z : ℂ → ℂ} {c z : ℂ} {d δ A : ℝ} (hd : 0 ≤ d)
    (hδ : 0 < δ) (hg : AnalyticOnNhd ℂ g (closedBall c (d + 2 * δ)))
    (hN : AnalyticOnNhd ℂ N (closedBall c (d + 2 * δ)))
    (hZ : AnalyticOnNhd ℂ Z (closedBall c (d + 2 * δ)))
    (hexp : ∀ w ∈ closedBall c (d + 2 * δ), Complex.exp (g w) * Z w = N w) (hZc : Z c ≠ 0)
    (hNA : ∀ w ∈ sphere c (d + 2 * δ), ‖N w‖ ≤ Real.exp A)
    (hZA : ∀ w ∈ sphere c (d + 2 * δ), ‖Z w‖ ≤ Real.exp A) (hA : 0 ≤ A)
    (hZlow : -A ≤ Real.log ‖Z c‖) (hgc : ‖g c‖ ≤ A) (hz : ‖z - c‖ ≤ d) :
    ‖deriv g z‖ ≤
      2 / δ * ((2 * (3 * A * (2 * d + 3 * δ) / δ + 1) * (2 * d + δ) + A * (4 * d + 3 * δ)) / δ) := by
  set R₂ : ℝ := d + 2 * δ with hR₂
  set R₁ : ℝ := d + δ with hR₁
  have hR₂0 : 0 < R₂ := by rw [hR₂]; linarith
  set M : ℝ := 3 * A * (2 * d + 3 * δ) / δ + 1 with hMdef
  have hM : 0 < M := by rw [hMdef]; positivity
  -- the one-sided bound on the disc of radius `R₁`
  have hre : ∀ w ∈ ball c R₁, (g w).re ≤ M := by
    intro w hw
    have hwR₂ : w ∈ ball c R₂ := ball_subset_ball (by rw [hR₁, hR₂]; linarith) hw
    have h := re_le_of_exp_mul_eq hR₂0 hg hN hZ hexp hZc hNA hZA hA hwR₂
    have hx : ‖w - c‖ < R₁ := by rwa [mem_ball, dist_eq_norm] at hw
    have hx0 := norm_nonneg (w - c)
    have hden : 0 < R₂ - ‖w - c‖ := by rw [hR₂]; rw [hR₁] at hx; linarith
    have hratio : (R₂ + ‖w - c‖) / (R₂ - ‖w - c‖) ≤ (2 * d + 3 * δ) / δ := by
      rw [div_le_div_iff₀ hden hδ]
      rw [hR₂]; rw [hR₁] at hx
      nlinarith
    have hK0 : 0 ≤ (R₂ + ‖w - c‖) / (R₂ - ‖w - c‖) := div_nonneg (by linarith) hden.le
    calc (g w).re ≤ (R₂ + ‖w - c‖) / (R₂ - ‖w - c‖) * (2 * A - Real.log ‖Z c‖) := h
      _ ≤ (R₂ + ‖w - c‖) / (R₂ - ‖w - c‖) * (3 * A) :=
          mul_le_mul_of_nonneg_left (by linarith) hK0
      _ ≤ (2 * d + 3 * δ) / δ * (3 * A) := mul_le_mul_of_nonneg_right hratio (by linarith)
      _ ≤ M := by rw [hMdef]; linarith [show (2 * d + 3 * δ) / δ * (3 * A) =
            3 * A * (2 * d + 3 * δ) / δ by ring]
  -- Borel--Carathéodory for `z' ↦ g (c + z')`
  have hBC : ∀ w, ‖w - c‖ ≤ d + δ / 2 →
      ‖g w‖ ≤ 2 * M * (2 * d + δ) / δ + A * (4 * d + 3 * δ) / δ := by
    intro w hw
    have hR₁0 : 0 < R₁ := by rw [hR₁]; linarith
    have hf : DifferentiableOn ℂ (fun u => g (c + u)) (ball 0 R₁) := by
      intro u hu
      have hmem : c + u ∈ closedBall c R₂ := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
        rw [mem_ball_zero_iff] at hu
        rw [hR₂]; rw [hR₁] at hu; linarith
      exact ((hg (c + u) hmem).differentiableAt.comp u
        (differentiableAt_const _ |>.add differentiableAt_id)).differentiableWithinAt
    have hmaps : Set.MapsTo (fun u => g (c + u)) (ball 0 R₁) {u | u.re ≤ M} := by
      intro u hu
      apply hre
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      rwa [mem_ball_zero_iff] at hu
    have hu : w - c ∈ ball (0 : ℂ) R₁ := by
      rw [mem_ball_zero_iff, hR₁]; linarith
    have h := Complex.borelCaratheodory hM hf hmaps hR₁0 hu
    simp only [add_sub_cancel, add_zero] at h
    have hx0 := norm_nonneg (w - c)
    have hden : δ / 2 ≤ R₁ - ‖w - c‖ := by rw [hR₁]; linarith
    have hden0 : 0 < R₁ - ‖w - c‖ := by linarith
    have h1 : 2 * M * ‖w - c‖ / (R₁ - ‖w - c‖) ≤ 2 * M * (2 * d + δ) / δ := by
      rw [div_le_div_iff₀ hden0 hδ]
      have e0 : ‖w - c‖ * δ ≤ (d + δ / 2) * δ := mul_le_mul_of_nonneg_right hw hδ.le
      have e1 : (2 * d + δ) * (δ / 2) ≤ (2 * d + δ) * (R₁ - ‖w - c‖) :=
        mul_le_mul_of_nonneg_left hden (by linarith)
      have e2 : ‖w - c‖ * δ ≤ (2 * d + δ) * (R₁ - ‖w - c‖) := by nlinarith
      have e3 := mul_le_mul_of_nonneg_left e2 (by linarith : (0 : ℝ) ≤ 2 * M)
      nlinarith
    have h2 : ‖g c‖ * (R₁ + ‖w - c‖) / (R₁ - ‖w - c‖) ≤ A * (4 * d + 3 * δ) / δ := by
      rw [div_le_div_iff₀ hden0 hδ]
      have hg0 := norm_nonneg (g c)
      have hnum : R₁ + ‖w - c‖ ≤ 2 * d + 3 * δ / 2 := by rw [hR₁]; linarith
      have e0 : ‖g c‖ * (R₁ + ‖w - c‖) ≤ A * (2 * d + 3 * δ / 2) :=
        mul_le_mul hgc hnum (by linarith) hA
      have e1 : ‖g c‖ * (R₁ + ‖w - c‖) * δ ≤ A * (2 * d + 3 * δ / 2) * δ :=
        mul_le_mul_of_nonneg_right e0 hδ.le
      have e2 : A * (4 * d + 3 * δ) * (δ / 2) ≤ A * (4 * d + 3 * δ) * (R₁ - ‖w - c‖) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      nlinarith
    linarith
  -- Cauchy's estimate on the circle of radius `δ/2` about `z`
  have hδ2 : 0 < δ / 2 := by linarith
  have hdc : DiffContOnCl ℂ g (ball z (δ / 2)) := by
    have hsub : closedBall z (δ / 2) ⊆ closedBall c R₂ := by
      intro u hu
      rw [mem_closedBall, dist_eq_norm] at hu ⊢
      calc ‖u - c‖ = ‖(u - z) + (z - c)‖ := by ring_nf
        _ ≤ ‖u - z‖ + ‖z - c‖ := norm_add_le _ _
        _ ≤ δ / 2 + d := add_le_add hu hz
        _ ≤ R₂ := by rw [hR₂]; linarith
    have hd' : DifferentiableOn ℂ g (closedBall z (δ / 2)) :=
      (hg.differentiableOn).mono hsub
    exact ⟨hd'.mono ball_subset_closedBall, by rw [closure_ball z hδ2.ne']; exact hd'.continuousOn⟩
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ2 hdc (fun u hu => by
    apply hBC
    rw [mem_sphere, dist_eq_norm] at hu
    calc ‖u - c‖ = ‖(u - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖u - z‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ d + δ / 2 := by rw [hu]; linarith)
  calc ‖deriv g z‖ ≤ (2 * M * (2 * d + δ) / δ + A * (4 * d + 3 * δ) / δ) / (δ / 2) := hcauchy
    _ = 2 / δ * ((2 * (3 * A * (2 * d + 3 * δ) / δ + 1) * (2 * d + δ) + A * (4 * d + 3 * δ)) / δ) := by
        rw [hMdef]; field_simp

end GaloisForLFunctions.HTGeometry

end
