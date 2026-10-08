import GaloisForLFunctions.RHTower.WeilWorkDeficitSmoothCutoffJets
import GaloisForLFunctions.RHTower.WeilWorkDeficitTwistedGapBudget
import GaloisForLFunctions.RHTower.TruncatedRiemannKernelWeilEnergy
import GaloisForLFunctions.RHTower.PoissonArithmeticProgressionBound

/-!
# Actual moving-cutoff windows and their complete twisted off-diagonal

A fixed smooth bump times `smoothAFECutoff (P/t)` admits both an L1 bound
and two integrations by parts, uniformly in every positive product and
window. The quadratic product decay is retained. Combining this with the
full reciprocal-square arithmetic gap budget proves absolute convergence
and an O_n(T/H) bound for every positive factor pair off the exact diagonal.

At square-root width the error is O_n(sqrt T). No truncation, replacement
cutoff, or unproved estimate enters. Gaussian-window extension, the full
zeta moment, and spectral-deficit closure are not asserted here.
-/

noncomputable section
open Real MeasureTheory Filter Set Topology
open scoped FourierTransform
namespace RHTower.WeilWorkDeficitWindow
open WeilWorkDeficitCutoff

/-- The literal fixed compact bump used in the window estimate. -/
def profile : ℝ → ℝ := bulkCutoff 1
private theorem smooth_profile (k : ℕ) : ContDiff ℝ k profile := contDiff_bulkCutoff 1
private theorem profile_zero {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) : profile x = 0 := by
  apply bulkCutoff_eq_zero
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have h := le_abs_self (-x)
    rw [abs_neg] at h
    linarith
  · exact (le_abs_self x).trans' hx.le

private theorem profile_eventually_zero {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) :
    profile =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
  exact profile_zero hy

private theorem jet_zero (j : ℕ) {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) :
    iteratedDeriv j profile x = 0 := by
  rw [(profile_eventually_zero hx).iteratedDeriv_eq j]
  simp

private theorem jet_compact (j : ℕ) : HasCompactSupport (iteratedDeriv j profile) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => jet_zero j hx)

private theorem jet_continuous (j : ℕ) : Continuous (iteratedDeriv j profile) :=
  (smooth_profile j).continuous_iteratedDeriv j le_rfl

private theorem jet_derivative (j : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv j profile) (iteratedDeriv (j+1) profile x) x := by
  rw [iteratedDeriv_succ]
  exact ((smooth_profile (j+1)).differentiable_iteratedDeriv j (by exact_mod_cast Nat.lt_succ_self j) x).hasDerivAt

private theorem jet_bound : ∃ B : ℝ, 0 < B ∧ ∀ j ≤ 2, ∀ x : ℝ,
    |iteratedDeriv j profile x| ≤ B := by
  obtain ⟨B₀,h₀⟩ := (jet_compact 0).exists_bound_of_continuous (jet_continuous 0)
  obtain ⟨B₁,h₁⟩ := (jet_compact 1).exists_bound_of_continuous (jet_continuous 1)
  obtain ⟨B₂,h₂⟩ := (jet_compact 2).exists_bound_of_continuous (jet_continuous 2)
  refine ⟨1+|B₀|+|B₁|+|B₂|,by positivity,fun j hj x => ?_⟩
  interval_cases j
  · simpa only [Real.norm_eq_abs] using (h₀ x).trans (by linarith [le_abs_self B₀,abs_nonneg B₁,abs_nonneg B₂])
  · simpa only [Real.norm_eq_abs] using (h₁ x).trans (by linarith [le_abs_self B₁,abs_nonneg B₀,abs_nonneg B₂])
  · simpa only [Real.norm_eq_abs] using (h₂ x).trans (by linarith [le_abs_self B₂,abs_nonneg B₀,abs_nonneg B₁])

/-- Real part of the actual moving-cutoff window. -/
def window (P T H t : ℝ) : ℝ := profile ((t-T)/H) * (smoothAFECutoff (P/t)).re
private def windowFirst (P T H t : ℝ) : ℝ :=
  iteratedDeriv 1 profile ((t-T)/H) / H * (smoothAFECutoff (P/t)).re +
    profile ((t-T)/H) * cutoffFirst P t
private def windowSecond (P T H t : ℝ) : ℝ :=
  iteratedDeriv 2 profile ((t-T)/H) / H^2 * (smoothAFECutoff (P/t)).re +
    2 * (iteratedDeriv 1 profile ((t-T)/H) / H) * cutoffFirst P t +
    profile ((t-T)/H) * cutoffSecond P t

private theorem scaled_outside {T H t : ℝ} (hH : 0 < H) (ht : t ∉ Icc (T-H) (T+H)) :
    (t-T)/H ∉ Icc (-1 : ℝ) 1 := by
  contrapose! ht
  rcases ht with ⟨hl,hr⟩
  rw [le_div_iff₀ hH] at hl
  rw [div_le_iff₀ hH] at hr
  constructor <;> linarith

private theorem window_zero {P T H t : ℝ} (hH : 0 < H) (ht : t ∉ Icc (T-H) (T+H)) :
    window P T H t = 0 := by
  simp [window, profile_zero (scaled_outside hH ht)]
private theorem first_zero {P T H t : ℝ} (hH : 0 < H) (ht : t ∉ Icc (T-H) (T+H)) :
    windowFirst P T H t = 0 := by
  simp [windowFirst, profile_zero (scaled_outside hH ht), jet_zero 1 (scaled_outside hH ht)]
private theorem second_zero {P T H t : ℝ} (hH : 0 < H) (ht : t ∉ Icc (T-H) (T+H)) :
    windowSecond P T H t = 0 := by
  simp [windowSecond, profile_zero (scaled_outside hH ht), jet_zero 1 (scaled_outside hH ht),
    jet_zero 2 (scaled_outside hH ht)]

private theorem derivative_window {P T H : ℝ} (hP : 0 < P) (hH : 0 < H) (hTH : 2*H ≤ T) (t : ℝ) :
    HasDerivAt (window P T H) (windowFirst P T H t) t := by
  by_cases ht : 0 < t
  · have hs := ((hasDerivAt_id t).sub_const T).div_const H
    have hp := (jet_derivative 0 ((t-T)/H)).comp t hs
    simp only [iteratedDeriv_zero, Nat.zero_add, one_div] at hp
    have hd := hp.mul (hasDerivAt_cutoff hP ht)
    apply hd.congr_deriv
    dsimp [windowFirst]
    ring
  · have ht' : t ∉ Icc (T-H) (T+H) := by simp only [mem_Icc]; push Not; intro; linarith
    have he : window P T H =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht'] with y hy
      exact window_zero hH hy
    rw [first_zero hH ht']
    exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he

private theorem derivative_first {P T H : ℝ} (hP : 0 < P) (hH : 0 < H) (hTH : 2*H ≤ T) (t : ℝ) :
    HasDerivAt (windowFirst P T H) (windowSecond P T H t) t := by
  by_cases ht : 0 < t
  · have hs := ((hasDerivAt_id t).sub_const T).div_const H
    have hp₀ := (jet_derivative 0 ((t-T)/H)).comp t hs
    have hp₁ := (jet_derivative 1 ((t-T)/H)).comp t hs
    simp only [iteratedDeriv_zero, Nat.zero_add] at hp₀
    have hd := ((hp₁.div_const H).mul (hasDerivAt_cutoff hP ht)).add
      (hp₀.mul (hasDerivAt_cutoffFirst hP ht))
    apply hd.congr_deriv
    dsimp [windowSecond]
    ring
  · have ht' : t ∉ Icc (T-H) (T+H) := by simp only [mem_Icc]; push Not; intro; linarith
    have he : windowFirst P T H =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht'] with y hy
      exact first_zero hH hy
    rw [second_zero hH ht']
    exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he

private theorem continuous_second {P T H : ℝ} (hP : 0 < P) (hH : 0 < H) (hTH : 2*H ≤ T) :
    Continuous (windowSecond P T H) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : 0 < t
  · have hs : ContinuousAt (fun t : ℝ => (t-T)/H) t := by fun_prop
    have h₀ := (jet_continuous 0).continuousAt.comp hs
    have h₁ := (jet_continuous 1).continuousAt.comp hs
    have h₂ := (jet_continuous 2).continuousAt.comp hs
    simp only [iteratedDeriv_zero] at h₀
    have hv := (hasDerivAt_cutoff hP ht).continuousAt
    have hv₁ := (hasDerivAt_cutoffFirst hP ht).continuousAt
    have hv₂ : ContinuousAt (cutoffSecond P) t := by
      unfold cutoffSecond
      have hq : ContinuousAt (fun u : ℝ => P/u) t := continuousAt_const.div continuousAt_id ht.ne'
      have hl := hq.log (div_pos hP ht).ne'
      have hd : ContinuousAt (fun u : ℝ => 2*sqrt π*u^2) t := by fun_prop
      have hd0 : 2*sqrt π*t^2 ≠ 0 := by positivity
      have hg : ContinuousAt (fun u : ℝ => exp (-(log (P/u))^2/4)) t :=
        Real.continuous_exp.continuousAt.comp ((hl.pow 2).neg.div_const 4)
      exact (hg.mul ((hl.div_const 2).sub (continuousAt_const (y := (1:ℝ))))).div hd hd0
    exact (((h₂.div_const (H^2)).mul hv).add
      ((continuousAt_const.mul (h₁.div_const H)).mul hv₁)).add (h₀.mul hv₂)
  · have ht' : t ∉ Icc (T-H) (T+H) := by simp only [mem_Icc]; push Not; intro; linarith
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht'] with y hy
    exact second_zero hH hy

private theorem smooth_window {P T H : ℝ} (hP : 0 < P) (hH : 0 < H) (hTH : 2*H ≤ T) :
    ContDiff ℝ 2 (window P T H) := by
  have hd₀ : deriv (window P T H) = windowFirst P T H :=
    funext (fun t => (derivative_window hP hH hTH t).deriv)
  have hd₁ : deriv (windowFirst P T H) = windowSecond P T H :=
    funext (fun t => (derivative_first hP hH hTH t).deriv)
  have hc₁ : ContDiff ℝ 1 (windowFirst P T H) := by
    rw [contDiff_one_iff_deriv, hd₁]
    exact ⟨fun t => (derivative_first hP hH hTH t).differentiableAt, continuous_second hP hH hTH⟩
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv, hd₀]
  exact ⟨fun t => (derivative_window hP hH hTH t).differentiableAt, by simp, hc₁⟩

private theorem second_eq {P T H : ℝ} (hP : 0 < P) (hH : 0 < H) (hTH : 2*H ≤ T) :
    iteratedDeriv 2 (window P T H) = windowSecond P T H := by
  rw [show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hd : deriv (window P T H) = windowFirst P T H :=
    funext (fun t => (derivative_window hP hH hTH t).deriv)
  rw [hd]
  exact funext (fun t => (derivative_first hP hH hTH t).deriv)

private theorem window_jet_zero {P T H t : ℝ} (hH : 0 < H)
    (ht : t ∉ Icc (T-H) (T+H)) (j : ℕ) : iteratedDeriv j (window P T H) t = 0 := by
  have he : window P T H =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht] with y hy
    exact window_zero hH hy
  rw [he.iteratedDeriv_eq j]
  simp

private theorem min_compare {P T t : ℝ} (hP : 0 < P) (ht : 0 ≤ t) (htT : t ≤ 2*T) :
    min 1 ((t/P)^2) ≤ 4 * min 1 ((T/P)^2) := by
  have hq : (t/P)^2 ≤ (2*(T/P))^2 := by
    have hT : 0 ≤ T := by linarith
    apply (sq_le_sq₀ (div_nonneg ht hP.le) (by positivity)).mpr
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right htT hP.le
  by_cases h : (T/P)^2 ≤ 1
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (by nlinarith [hq])
  · rw [min_eq_left (le_of_not_ge h)]
    exact (min_le_left _ _).trans (by norm_num)

private theorem pointwise_bounds {B C P T H : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hb : ∀ j ≤ 2, ∀ x : ℝ, |iteratedDeriv j profile x| ≤ B)
    (hc : ∀ P t : ℝ, 0 < P → 0 < t →
      |(smoothAFECutoff (P/t)).re| ≤ C * min 1 ((t/P)^2) ∧
      |cutoffFirst P t| ≤ C/t * min 1 ((t/P)^2) ∧
      |cutoffSecond P t| ≤ C/t^2 * min 1 ((t/P)^2))
    (hP : 0 < P) (hH : 0 < H) (hTH : 2*H ≤ T) {t : ℝ} (ht : t ∈ Icc (T-H) (T+H)) :
    |window P T H t| ≤ 4*B*C*min 1 ((T/P)^2) ∧
    |windowSecond P T H t| ≤ 16*B*C/H^2*min 1 ((T/P)^2) := by
  have htH : H ≤ t := by linarith [ht.1]
  have htp : 0 < t := hH.trans_le htH
  have htT : t ≤ 2*T := by linarith [ht.2]
  have hm := min_compare hP htp.le htT
  have hm0 : 0 ≤ min 1 ((T/P)^2) := le_min (by norm_num) (sq_nonneg _)
  obtain ⟨h₀,h₁,h₂⟩ := hc P t hP htp
  have hv₀ : |(smoothAFECutoff (P/t)).re| ≤ C * (4 * min 1 ((T/P)^2)) := h₀.trans (by gcongr)
  have hv₁ : |cutoffFirst P t| ≤ C/H * (4 * min 1 ((T/P)^2)) := h₁.trans (by gcongr)
  have hv₂ : |cutoffSecond P t| ≤ C/H^2 * (4 * min 1 ((T/P)^2)) := h₂.trans (by gcongr)
  have hb₀ := hb 0 (by omega) ((t-T)/H)
  have hb₁ := hb 1 (by omega) ((t-T)/H)
  have hb₂ := hb 2 (by omega) ((t-T)/H)
  simp only [iteratedDeriv_zero] at hb₀
  constructor
  · dsimp [window]
    rw [abs_mul]
    calc _ ≤ B * (C * (4 * min 1 ((T/P)^2))) := mul_le_mul hb₀ hv₀ (abs_nonneg _) hB.le
         _ = _ := by ring
  · dsimp [windowSecond]
    calc |(_ + _) + _| ≤ |iteratedDeriv 2 profile ((t-T)/H) / H^2 * (smoothAFECutoff (P/t)).re| +
            |2 * (iteratedDeriv 1 profile ((t-T)/H) / H) * cutoffFirst P t| +
            |profile ((t-T)/H) * cutoffSecond P t| :=
              (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
         _ ≤ B/H^2 * (C * (4 * min 1 ((T/P)^2))) +
             2*(B/H)*(C/H * (4 * min 1 ((T/P)^2))) +
             B*(C/H^2 * (4 * min 1 ((T/P)^2))) := by
           simp only [abs_mul, abs_div, abs_of_pos hH, abs_pow, show |(2:ℝ)|=2 by norm_num]
           gcongr
         _ = _ := by ring

private theorem integral_support_bound {f : ℝ → ℝ} {T H D : ℝ} (hH : 0 < H)
    (hzero : ∀ t ∉ Icc (T-H) (T+H), f t = 0)
    (hbound : ∀ t ∈ Icc (T-H) (T+H), |f t| ≤ D) :
    (∫ t, |f t|) ≤ 2*H*D := by
  have hle : ∀ t, |f t| ≤ (Icc (T-H) (T+H)).indicator (fun _ => D) t := by
    intro t
    by_cases ht : t ∈ Icc (T-H) (T+H)
    · rw [indicator_of_mem ht]
      exact hbound t ht
    · rw [indicator_of_notMem ht, hzero t ht, abs_zero]
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
    (Eventually.of_forall hle)).trans (le_of_eq ?_)
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
  ring

private theorem integrable_window_derivative {P T H : ℝ} (hP : 0 < P) (hH : 0 < H)
    (hTH : 2*H ≤ T) {j : ℕ} (hj : j ≤ 2) :
    Integrable (iteratedDeriv j (fun t => (window P T H t : ℂ))) := by
  rw [iteratedDeriv_ofReal_comp_of_le (smooth_window hP hH hTH) hj]
  have hc := Complex.continuous_ofReal.comp
    ((smooth_window hP hH hTH).continuous_iteratedDeriv j (by exact_mod_cast hj))
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro isCompact_Icc
  intro t ht
  change ((iteratedDeriv j (window P T H) t : ℝ) : ℂ) = 0
  rw [window_jet_zero hH ht j, Complex.ofReal_zero]

private theorem window_eq_literal {P T H : ℝ} (hP : 0 < P) (hH : 0 < H)
    (hTH : 2*H ≤ T) (t : ℝ) :
    (window P T H t : ℂ) = (profile ((t-T)/H) : ℂ) * smoothAFECutoff (P/t) := by
  by_cases ht : t ∈ Icc (T-H) (T+H)
  · have htp : 0 < t := by linarith [ht.1]
    simp only [window, Complex.ofReal_mul]
    congr 1
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im, smoothAFECutoff_im_eq_zero (div_pos hP htp)]
  · simp only [window_zero hH ht, profile_zero (scaled_outside hH ht), Complex.ofReal_zero, zero_mul]

/-- A single constant controls the actual moving AFE cutoff on every positive
window and every nonzero frequency, including windows of square-root width.
The cutoff retains its quadratic decay in the product parameter. -/
theorem exists_uniform_oscillatory_window_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ P T H : ℝ, 0 < P → 0 < H → 2*H ≤ T → ∀ lam : ℝ,
      ‖∫ t : ℝ, (profile ((t-T)/H) : ℂ) * smoothAFECutoff (P/t) *
        Complex.exp ((lam*t : ℝ) * Complex.I)‖ ≤ K*H*min 1 ((T/P)^2) ∧
      (lam ≠ 0 → ‖∫ t : ℝ, (profile ((t-T)/H) : ℂ) * smoothAFECutoff (P/t) *
        Complex.exp ((lam*t : ℝ) * Complex.I)‖ ≤ K/(H*lam^2)*min 1 ((T/P)^2)) := by
  obtain ⟨B,hB,hb⟩ := jet_bound
  obtain ⟨C,hC,hc⟩ := exists_uniform_cutoff_two_jet_bound
  refine ⟨32*B*C,by positivity,fun P T H hP hH hTH lam => ?_⟩
  let f : ℝ → ℂ := fun t => (window P T H t : ℂ)
  have hfc : ContDiff ℝ 2 f := Complex.ofRealCLM.contDiff.comp (smooth_window hP hH hTH)
  have hfi : ∀ j ≤ 2, Integrable (iteratedDeriv j f) :=
    fun j hj => integrable_window_derivative hP hH hTH hj
  have hbnd (t : ℝ) (ht : t ∈ Icc (T-H) (T+H)) := pointwise_bounds hB hC hb hc hP hH hTH ht
  have hmass : (∫ t, |window P T H t|) ≤ 8*B*C*H*min 1 ((T/P)^2) := by
    refine (integral_support_bound hH (fun t ht => window_zero hH ht)
      (fun t ht => (hbnd t ht).1)).trans_eq ?_
    ring
  have hsecond : (∫ t, ‖iteratedDeriv 2 f t‖) ≤ 32*B*C/H*min 1 ((T/P)^2) := by
    dsimp [f]
    rw [iteratedDeriv_ofReal_comp_of_le (smooth_window hP hH hTH) (le_refl 2), second_eq hP hH hTH]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    refine (integral_support_bound hH (fun t ht => second_zero hH ht)
      (fun t ht => (hbnd t ht).2)).trans_eq ?_
    field_simp
    ring
  have hliteral : (fun t : ℝ => (profile ((t-T)/H) : ℂ) * smoothAFECutoff (P/t) *
      Complex.exp ((lam*t : ℝ) * Complex.I)) =
      (fun t : ℝ => f t * Complex.exp ((lam*t : ℝ) * Complex.I)) := by
    funext t
    rw [← window_eq_literal hP hH hTH]
  rw [hliteral]
  constructor
  · calc ‖∫ t, f t * Complex.exp ((lam*t : ℝ) * Complex.I)‖ ≤
          ∫ t, ‖f t * Complex.exp ((lam*t : ℝ) * Complex.I)‖ := norm_integral_le_integral_norm _
         _ = ∫ t, |window P T H t| := by
           congr 1
           funext t
           simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, f, Complex.norm_real, Real.norm_eq_abs]
         _ ≤ 8*B*C*H*min 1 ((T/P)^2) := hmass
         _ ≤ _ := by gcongr; norm_num
  · intro hlam
    have hfour : ∫ t, f t * Complex.exp ((lam*t : ℝ) * Complex.I) = 𝓕 f (-(lam/(2*π))) := by
      rw [Real.fourier_real_eq]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
      rw [mul_comm]
      congr 2
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
      push_cast
      field_simp
    have hibp := pow_mul_norm_fourier_le_of_iteratedDeriv hfc hfi (-(lam/(2*π)))
    have hξ : 2*π*|-(lam/(2*π))| = |lam| := by
      rw [abs_neg, abs_div, abs_of_pos (by positivity : (0:ℝ)<2*π)]
      field_simp
    rw [hξ, sq_abs] at hibp
    rw [hfour]
    have hlamp : 0 < lam^2 := sq_pos_of_ne_zero hlam
    calc ‖𝓕 f (-(lam/(2*π)))‖ ≤ (32*B*C/H*min 1 ((T/P)^2))/lam^2 :=
          (le_div_iff₀ hlamp).mpr (by simpa only [mul_comm] using hibp.trans hsecond)
         _ = _ := by ring

open ZetaNotch WeilWorkDeficitGap

/-- The full positive-pair family for the actual AFE window, with only the
exact arithmetic diagonal removed. -/
def offDiagonalWindowTerm (n : ℕ) (T H : ℝ) (p : ℕ × ℕ) : ℂ :=
  if pairFreq p - log n = 0 then 0 else
    (pairAmp p : ℂ) * ∫ t : ℝ, (profile ((t-T)/H) : ℂ) *
      smoothAFECutoff (2*π*pairProd p/t) *
      Complex.exp (((pairFreq p-log n)*t : ℝ) * Complex.I)

private theorem scaled_min {T : ℝ} (hT : 0 ≤ T) (p : ℕ × ℕ) :
    min 1 ((T/(2*π*pairProd p))^2) ≤ (min 1 (T/pairProd p))^2 := by
  have hp := pairProd_pos p
  have hpi : 1 ≤ 2*π := by linarith [pi_gt_three]
  have hq : 0 ≤ T/(2*π*pairProd p) := by positivity
  have hq' : 0 ≤ T/pairProd p := div_nonneg hT hp.le
  have hle : T/(2*π*pairProd p) ≤ T/pairProd p := by
    apply div_le_div_of_nonneg_left hT hp
    nlinarith
  have hs : (T/(2*π*pairProd p))^2 ≤ (T/pairProd p)^2 := (sq_le_sq₀ hq hq').mpr hle
  by_cases h : T/pairProd p ≤ 1
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans hs
  · rw [min_eq_left (le_of_not_ge h), one_pow]
    exact min_le_left _ _

/-- Absolute convergence and a conductor/width bound for the complete actual
cutoff off-diagonal. In particular the square-root window has an O_n(sqrt T)
error, with no pair truncation or extra analytic premise. -/
theorem exists_full_offDiagonalWindow_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 1 ≤ n → ∀ T H : ℝ, 1 ≤ T → 0 < H → 2*H ≤ T →
      Summable (offDiagonalWindowTerm n T H) ∧
      ‖∑' p : ℕ × ℕ, offDiagonalWindowTerm n T H p‖ ≤
        K*(48*(n:ℝ)^2*integerGapBudget+16*pairZeta)*T/H := by
  obtain ⟨K,hK,hwin⟩ := exists_uniform_oscillatory_window_bound
  refine ⟨K,hK,fun n hn T H hT hH hTH => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hmajor : Summable (fun p => (K/H)*twistedGapWeight T n p) :=
    (summable_twistedGapWeight hT0 hn).mul_left (K/H)
  have hpoint (p : ℕ × ℕ) : ‖offDiagonalWindowTerm n T H p‖ ≤ (K/H)*twistedGapWeight T n p := by
    by_cases hgap : pairFreq p-log n = 0
    · simp [offDiagonalWindowTerm, hgap, twistedGapWeight]
    · have hp : 0 < 2*π*pairProd p := by positivity [pairProd_pos p]
      have hi := (hwin (2*π*pairProd p) T H hp hH hTH (pairFreq p-log n)).2 hgap
      simp only [offDiagonalWindowTerm, if_neg hgap, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (pairAmp_pos p)]
      calc _ ≤ pairAmp p * (K/(H*(pairFreq p-log n)^2) * min 1 ((T/(2*π*pairProd p))^2)) :=
              mul_le_mul_of_nonneg_left hi (pairAmp_pos p).le
           _ ≤ pairAmp p * (K/(H*(pairFreq p-log n)^2) * (min 1 (T/pairProd p))^2) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (scaled_min hT0 p) (by positivity)) (pairAmp_pos p).le
           _ = _ := by
              unfold twistedGapWeight
              simp only [div_eq_mul_inv, mul_inv_rev]
              ring
  have hs := hmajor.of_norm_bounded hpoint
  refine ⟨hs, (norm_tsum_le_tsum_norm hs.norm).trans ?_⟩
  calc ∑' p, ‖offDiagonalWindowTerm n T H p‖ ≤ ∑' p, (K/H)*twistedGapWeight T n p :=
         hs.norm.tsum_le_tsum hpoint hmajor
       _ = (K/H)*∑' p, twistedGapWeight T n p := tsum_mul_left
       _ ≤ (K/H)*((48*(n:ℝ)^2*integerGapBudget+16*pairZeta)*T) :=
         mul_le_mul_of_nonneg_left (tsum_twistedGapWeight_le hT hn) (div_pos hK hH).le
       _ = _ := by ring

end RHTower.WeilWorkDeficitWindow



