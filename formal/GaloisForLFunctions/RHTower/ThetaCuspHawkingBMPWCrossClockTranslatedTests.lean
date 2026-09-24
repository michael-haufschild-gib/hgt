import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWCrossClockLogError
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWindowMoments

open Complex MeasureTheory Set Filter Topology
open RHTower RHTower.D4BMModularCore
open RHTower.D4BMPWCrossClockMeanEquation RHTower.D4BMPWCrossClockMeanError
open RHTower.D4BMPWCrossClockLogIdentity RHTower.D4BMPWCrossClockLogError
open RHTower.D4BMMixedParticularCuspFlux
open scoped ContDiff
noncomputable section
set_option autoImplicit false

namespace RHTower.D4BMPWCrossClockTranslatedTests

theorem translated_L1_pairing_vanish
    (E ψ : ℝ → ℂ) (hE : Integrable E) (hψmeas : Measurable ψ)
    {M : ℝ} (hψbound : ∀ s, ‖ψ s‖ ≤ M)
    (hψsupport : ∀ s, s < -1 → ψ s = 0) :
    Tendsto (fun T : ℝ => ∫ x : ℝ, E x * ψ (x-T)) atTop (𝓝 (0:ℂ)) := by
  rw [show (0:ℂ) = ∫ _x : ℝ, (0:ℂ) by simp]
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun (T : ℝ) (x : ℝ) => E x * ψ (x-T))
    (f := fun _ => (0:ℂ)) (l := atTop)
    (fun x => M * ‖E x‖) ?_ ?_ (hE.norm.const_mul M) ?_
  · exact Eventually.of_forall (fun T => hE.aestronglyMeasurable.mul
      ((hψmeas.comp (measurable_id.sub measurable_const)).aestronglyMeasurable))
  · exact Eventually.of_forall (fun T => ae_of_all _ (fun x => by
      rw [norm_mul]
      calc
        ‖E x‖ * ‖ψ (x-T)‖ ≤ ‖E x‖ * M :=
          mul_le_mul_of_nonneg_left (hψbound _) (norm_nonneg _)
        _ = M * ‖E x‖ := mul_comm _ _))
  · filter_upwards with x
    have hT : ∀ᶠ T : ℝ in atTop, x-T < -1 := by
      filter_upwards [eventually_gt_atTop (x+1)] with T hT
      linarith
    exact tendsto_const_nhds.congr' (by
      filter_upwards [hT] with T hT
      simp [hψsupport _ hT])

theorem translated_limit_pairing
    (P ψ : ℝ → ℂ) (C : ℂ) (hP : Tendsto P atTop (𝓝 C))
    (hPmeas : Measurable P) (hψmeas : Measurable ψ)
    (hψint : Integrable ψ)
    (hψsupport : ∀ s, s ∉ Icc (-1:ℝ) 1 → ψ s = 0) :
    Tendsto (fun T : ℝ => ∫ x : ℝ, P x * ψ (x-T)) atTop
      (𝓝 (C * ∫ s : ℝ, ψ s)) := by
  have hshift (T : ℝ) :
      (∫ x : ℝ, P x * ψ (x-T)) = ∫ s : ℝ, P (s+T) * ψ s := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun x : ℝ => P x * ψ (x-T)) T
    simpa only [add_sub_cancel_right] using h.symm
  simp_rw [hshift]
  rw [← integral_const_mul]
  have hPbd : ∀ᶠ x : ℝ in atTop, ‖P x‖ ≤ ‖C‖ + 1 := by
    have hc : ∀ᶠ x : ℝ in atTop, dist (P x) C < 1 :=
      hP.eventually (Metric.ball_mem_nhds C (by norm_num : (0:ℝ)<1))
    filter_upwards [hc] with x hx
    have := norm_le_norm_add_norm_sub' (P x) C
    rw [dist_eq_norm] at hx
    linarith
  obtain ⟨A,hA⟩ := eventually_atTop.1 hPbd
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun (T : ℝ) (s : ℝ) => P (s+T) * ψ s)
    (f := fun s : ℝ => C*ψ s) (l := atTop)
    (fun s => (‖C‖+1)*‖ψ s‖) ?_ ?_
    (hψint.norm.const_mul (‖C‖+1)) ?_
  · exact Eventually.of_forall (fun T =>
      ((hPmeas.comp (measurable_id.add_const T)).mul hψmeas).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (A+1)] with T hT
    exact ae_of_all _ (fun s => by
      by_cases hs : s ∈ Icc (-1:ℝ) 1
      · have hsA : A ≤ s+T := by have := hs.1; linarith
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hA _ hsA) (norm_nonneg _)
      · simp [hψsupport s hs])
  · filter_upwards with s
    have ht : Tendsto (fun T : ℝ => s+T) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [eventually_ge_atTop (b-s)] with T hT
      linarith
    exact (hP.comp ht).mul_const (ψ s)

private def testWindow (s : ℝ) : ℂ := ((cuspWindowDerivative 0 s)^(2:ℕ):ℝ)

private theorem testWindow_continuous : Continuous testWindow := by
  exact Complex.continuous_ofReal.comp ((cuspWindowDerivative_smooth 0).continuous.pow 2)

private theorem testWindow_support {s : ℝ} (hs : s ∉ Icc (-1:ℝ) 1) :
    testWindow s = 0 := by
  have hnot : s ∉ tsupport (cuspWindowDerivative 0) :=
    fun h => hs (cuspWindowDerivative_support 0 h)
  have hz : cuspWindowDerivative 0 s = 0 :=
    image_eq_zero_of_notMem_tsupport hnot
  simp [testWindow,hz]

private theorem testWindow_integrable : Integrable testWindow :=
  (cuspWindowDerivative_sq_integrable 0).ofReal

private theorem testWindow_bounded : ∃ M : ℝ, ∀ s, ‖testWindow s‖ ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    testWindow_continuous.continuousOn
  refine ⟨max M 0,fun s => ?_⟩
  by_cases hs : s ∈ Icc (-1:ℝ) 1
  · exact (hM s hs).trans (le_max_left _ _)
  · rw [testWindow_support hs,norm_zero]
    exact le_max_right _ _

private def errorFull (q : XiZeroCopy) (t : ℝ) : ℂ :=
  Complex.exp (-rate q*(t:ℂ)) *
    (crossMean q (Real.exp t)-principalCross q (Real.exp t))

private def errorCut (q : XiZeroCopy) (t : ℝ) : ℂ :=
  (Ioi (Real.log 3)).indicator (errorFull q) t

private theorem errorCut_integrable (q : XiZeroCopy)
    (hleft : (q.1:ℂ).re < 1/2) : Integrable (errorCut q) := by
  change Integrable ((Ioi (Real.log 3)).indicator (errorFull q))
  exact (integrable_indicator_iff measurableSet_Ioi).mpr
    (actual_normalized_error_integrable q hleft)

/-- The actual normalized full-minus-principal mean disappears under fixed
compact windows translated to logarithmic infinity. -/
theorem actual_error_translated_test_vanish (q : XiZeroCopy)
    (hleft : (q.1:ℂ).re < 1/2) :
    Tendsto (fun T : ℝ => ∫ t : ℝ, errorCut q t * testWindow (t-T))
      atTop (𝓝 (0:ℂ)) := by
  obtain ⟨M,hM⟩ := testWindow_bounded
  exact translated_L1_pairing_vanish (errorCut q) testWindow
    (errorCut_integrable q hleft) testWindow_continuous.measurable
    hM (fun s hs => testWindow_support (fun h => by have := h.1; linarith))

private def principalNorm (q : XiZeroCopy) (t : ℝ) : ℂ :=
  Complex.exp (-rate q*(t:ℂ))*principalCross q (Real.exp t)

private theorem principalNorm_continuous (q : XiZeroCopy) :
    Continuous (principalNorm q) := by
  have hpow (i : Fin 3) :
      Continuous (fun t : ℝ => (Real.exp t:ℂ)^(RHTower.D4BMMixedParticularCuspFlux.sourcePower q i)) := by
    have heq (t : ℝ) :
        (Real.exp t:ℂ)^(RHTower.D4BMMixedParticularCuspFlux.sourcePower q i) =
        Complex.exp ((t:ℂ)*RHTower.D4BMMixedParticularCuspFlux.sourcePower q i) := by
      rw [GaloisForLFunctions.HTGeometry.ofReal_cpow_eq_exp (Real.exp_pos t),Real.log_exp]
    simp_rw [heq]
    fun_prop
  have hb (b : Bool) :
      Continuous (fun t : ℝ => RHTower.D4BMGlobalAngularResponse.cuspResponse q b ![0,Real.exp t]) := by
    have heq : (fun t : ℝ => RHTower.D4BMGlobalAngularResponse.cuspResponse q b ![0,Real.exp t]) =
        (fun t : ℝ => ∑ i : Fin 3,
          RHTower.D4BMMixedParticularCuspFlux.responseCoefficient q b i *
            (Real.exp t:ℂ)^(RHTower.D4BMMixedParticularCuspFlux.sourcePower q i)) := by
      funext t
      exact RHTower.D4BMMixedParticularCuspFlux.cuspResponse_eq_sum q b (Real.exp t)
    rw [heq]
    exact continuous_finset_sum _ (fun i _ => continuous_const.mul (hpow i))
  change Continuous (fun t : ℝ => Complex.exp (-rate q*(t:ℂ))*
    (RHTower.D4BMGlobalAngularResponse.cuspResponse q true ![0,Real.exp t] *
      RHTower.D4BMGlobalAngularResponse.cuspResponse q false ![0,Real.exp t]))
  exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-rate q*(t:ℂ)))).mul
    ((hb true).mul (hb false))

private theorem testWindow_mass :
    (∫ s : ℝ, testWindow s) = (cuspWindowMoment 0:ℂ) := by
  rw [show (∫ s : ℝ, testWindow s) =
      ((∫ s : ℝ, cuspWindowDerivative 0 s^(2:ℕ)):ℝ) by
        exact integral_complex_ofReal]
  rfl

/-- The actual principal two-branch product retains its nonzero leading
coefficient against the same translated positive-mass window. -/
theorem actual_principal_translated_test_limit (q : XiZeroCopy)
    (hleft : (q.1:ℂ).re < 1/2) :
    Tendsto (fun T : ℝ => ∫ t : ℝ, principalNorm q t * testWindow (t-T))
      atTop (𝓝 ((RHTower.D4BMMixedParticularCuspFlux.responseCoefficient q true 2 *
        RHTower.D4BMMixedParticularCuspFlux.responseCoefficient q false 2) *
        (cuspWindowMoment 0:ℂ))) := by
  have h := translated_limit_pairing (principalNorm q) testWindow
    (RHTower.D4BMMixedParticularCuspFlux.responseCoefficient q true 2 *
      RHTower.D4BMMixedParticularCuspFlux.responseCoefficient q false 2)
    (normalizedPrincipal_tendsto q hleft) (principalNorm_continuous q).measurable
    testWindow_continuous.measurable testWindow_integrable (fun s hs => testWindow_support hs)
  simpa only [testWindow_mass] using h

private theorem testWindow_smooth : ContDiff ℝ ∞ testWindow := by
  unfold testWindow
  exact Complex.ofRealCLM.contDiff.comp ((cuspWindowDerivative_smooth 0).pow 2)

private theorem testWindow_tsupport : tsupport testWindow ⊆ Icc (-1:ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  by_contra hn
  exact hs (testWindow_support hn)

private theorem testWindow_compact : HasCompactSupport testWindow :=
  isCompact_Icc.of_isClosed_subset isClosed_closure testWindow_tsupport

private theorem testWindow_deriv_smooth : ContDiff ℝ ∞ (deriv testWindow) :=
  (contDiff_infty_iff_deriv.mp testWindow_smooth).2

private theorem testWindow_second_smooth : ContDiff ℝ ∞ (deriv (deriv testWindow)) :=
  (contDiff_infty_iff_deriv.mp testWindow_deriv_smooth).2

private theorem testWindow_deriv_tsupport : tsupport (deriv testWindow) ⊆ Icc (-1:ℝ) 1 :=
  tsupport_deriv_subset.trans testWindow_tsupport

private theorem testWindow_second_tsupport :
    tsupport (deriv (deriv testWindow)) ⊆ Icc (-1:ℝ) 1 :=
  tsupport_deriv_subset.trans testWindow_deriv_tsupport

private theorem testWindow_deriv_compact : HasCompactSupport (deriv testWindow) :=
  testWindow_compact.deriv

private theorem testWindow_second_compact : HasCompactSupport (deriv (deriv testWindow)) :=
  testWindow_deriv_compact.deriv

private theorem testWindow_shift_compact (T : ℝ) :
    HasCompactSupport (fun t : ℝ => testWindow (t-T)) := by
  simpa [Function.comp_def, sub_eq_add_neg] using
    testWindow_compact.comp_homeomorph (Homeomorph.addRight (-T))

private theorem testWindow_deriv_shift_compact (T : ℝ) :
    HasCompactSupport (fun t : ℝ => deriv testWindow (t-T)) := by
  simpa [Function.comp_def, sub_eq_add_neg] using
    testWindow_deriv_compact.comp_homeomorph (Homeomorph.addRight (-T))

private theorem testWindow_second_shift_compact (T : ℝ) :
    HasCompactSupport (fun t : ℝ => deriv (deriv testWindow) (t-T)) := by
  simpa [Function.comp_def, sub_eq_add_neg] using
    testWindow_second_compact.comp_homeomorph (Homeomorph.addRight (-T))

private theorem testWindow_shift_hasDerivAt (T t : ℝ) :
    HasDerivAt (fun s : ℝ => testWindow (s-T)) (deriv testWindow (t-T)) t := by
  have h := (testWindow_smooth.differentiable (by simp) (t-T)).hasDerivAt.scomp t
    ((hasDerivAt_id t).sub_const T)
  simpa [Function.comp_def,Complex.real_smul] using h

private theorem testWindow_deriv_shift_hasDerivAt (T t : ℝ) :
    HasDerivAt (fun s : ℝ => deriv testWindow (s-T))
      (deriv (deriv testWindow) (t-T)) t := by
  have h := (testWindow_deriv_smooth.differentiable (by simp) (t-T)).hasDerivAt.scomp t
    ((hasDerivAt_id t).sub_const T)
  simpa [Function.comp_def,Complex.real_smul] using h

private theorem integral_deriv_zero_of_compact {g : ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) :
    (∫ t : ℝ, deriv g t) = 0 := by
  have hi : Integrable (fun t : ℝ => deriv g t) :=
    (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hs.deriv
  have hsplit := MeasureTheory.integral_add_compl (μ := (volume : Measure ℝ))
    (measurableSet_Iic (a := (0:ℝ))) hi
  have hleft : (∫ t : ℝ in Iic (0:ℝ), deriv g t) = g 0 :=
    HasCompactSupport.integral_Iic_deriv_eq hg hs 0
  have hright : (∫ t : ℝ in Ioi (0:ℝ), deriv g t) = -g 0 :=
    HasCompactSupport.integral_Ioi_deriv_eq hg hs 0
  rw [compl_Iic,hleft,hright] at hsplit
  simpa using hsplit.symm

private theorem testWindow_deriv_mass_zero : (∫ t : ℝ, deriv testWindow t) = 0 :=
  integral_deriv_zero_of_compact (testWindow_smooth.of_le (by simp)) testWindow_compact

private theorem testWindow_second_mass_zero :
    (∫ t : ℝ, deriv (deriv testWindow) t) = 0 :=
  integral_deriv_zero_of_compact (testWindow_deriv_smooth.of_le (by simp))
    testWindow_deriv_compact

private theorem compact_second_ibp
    (f ψ ψ1 ψ2 : ℝ → ℂ)
    (hf : Continuous f) (hf1 : Continuous (deriv f))
    (hf2 : Continuous (deriv (deriv f)))
    (hψ : Continuous ψ) (hψ1 : Continuous ψ1) (hψ2 : Continuous ψ2)
    (hs0 : HasCompactSupport ψ) (hs1 : HasCompactSupport ψ1)
    (hs2 : HasCompactSupport ψ2)
    (hfd : ∀ x, HasDerivAt f (deriv f x) x)
    (hfd1 : ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x)
    (hψd : ∀ x, HasDerivAt ψ (ψ1 x) x)
    (hψd1 : ∀ x, HasDerivAt ψ1 (ψ2 x) x) :
    (∫ x : ℝ, deriv (deriv f) x * ψ x) = ∫ x : ℝ, f x * ψ2 x := by
  have hInt (g v : ℝ → ℂ) (hg : Continuous g) (hv : Continuous v)
      (hs : HasCompactSupport g) : Integrable (fun x => g x * v x) :=
    (hg.mul hv).integrable_of_hasCompactSupport hs.mul_right
  have hfirst := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := ψ) (u' := ψ1) (v := deriv f) (v' := deriv (deriv f))
    (fun x _ => hψd x) (fun x _ => hfd1 x)
    (hInt ψ (deriv (deriv f)) hψ hf2 hs0)
    (hInt ψ1 (deriv f) hψ1 hf1 hs1)
    (hInt ψ (deriv f) hψ hf1 hs0)
  have hsecond := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := ψ1) (u' := ψ2) (v := f) (v' := deriv f)
    (fun x _ => hψd1 x) (fun x _ => hfd x)
    (hInt ψ1 (deriv f) hψ1 hf1 hs1)
    (hInt ψ2 f hψ2 hf hs2)
    (hInt ψ1 f hψ1 hf hs1)
  calc
    (∫ x : ℝ, deriv (deriv f) x * ψ x) =
        ∫ x : ℝ, ψ x * deriv (deriv f) x := by
          apply integral_congr_ae
          filter_upwards [] with x
          ring
    _ = -(∫ x : ℝ, ψ1 x * deriv f x) := hfirst
    _ = ∫ x : ℝ, ψ2 x * f x := by rw [hsecond]; ring
    _ = ∫ x : ℝ, f x * ψ2 x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring

private theorem compact_first_ibp
    (f ψ ψ1 : ℝ → ℂ)
    (hf : Continuous f) (hf1 : Continuous (deriv f))
    (hψ : Continuous ψ) (hψ1 : Continuous ψ1)
    (hs0 : HasCompactSupport ψ) (hs1 : HasCompactSupport ψ1)
    (hfd : ∀ x, HasDerivAt f (deriv f x) x)
    (hψd : ∀ x, HasDerivAt ψ (ψ1 x) x) :
    (∫ x : ℝ, deriv f x * ψ x) = -(∫ x : ℝ, f x * ψ1 x) := by
  have hInt (g v : ℝ → ℂ) (hg : Continuous g) (hv : Continuous v)
      (hs : HasCompactSupport g) : Integrable (fun x => g x * v x) :=
    (hg.mul hv).integrable_of_hasCompactSupport hs.mul_right
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := ψ) (u' := ψ1) (v := f) (v' := deriv f)
    (fun x _ => hψd x) (fun x _ => hfd x)
    (hInt ψ (deriv f) hψ hf1 hs0)
    (hInt ψ1 f hψ1 hf hs1)
    (hInt ψ f hψ hf hs0)
  calc
    (∫ x : ℝ, deriv f x * ψ x) = ∫ x : ℝ, ψ x * deriv f x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = -(∫ x : ℝ, ψ1 x * f x) := h
    _ = -(∫ x : ℝ, f x * ψ1 x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      ring

private theorem normalizedMean_continuous (q : XiZeroCopy) :
    Continuous (normalizedMean q) :=
  continuous_iff_continuousAt.mpr (fun t => (normalizedMean_hasDerivAt q t).continuousAt)

private theorem normalizedMean_deriv_continuous (q : XiZeroCopy) :
    Continuous (deriv (normalizedMean q)) :=
  continuous_iff_continuousAt.mpr
    (fun t => (normalizedMean_deriv_hasDerivAt q t).continuousAt)

private theorem normalizedForcing_test_adjoint (q : XiZeroCopy) (T : ℝ) :
    (∫ t : ℝ, normalizedForcing q t * testWindow (t-T)) =
      (∫ t : ℝ, normalizedMean q t * deriv (deriv testWindow) (t-T)) -
      (2*rate q-1)*(∫ t : ℝ, normalizedMean q t * deriv testWindow (t-T)) +
      (rate q*(rate q-1)-20)*
        (∫ t : ℝ, normalizedMean q t * testWindow (t-T)) := by
  let f := normalizedMean q
  let ψ := fun t : ℝ => testWindow (t-T)
  let ψ1 := fun t : ℝ => deriv testWindow (t-T)
  let ψ2 := fun t : ℝ => deriv (deriv testWindow) (t-T)
  let A := 2*rate q-1
  let B := rate q*(rate q-1)-20
  have hf : Continuous f := normalizedMean_continuous q
  have hf1 : Continuous (deriv f) := normalizedMean_deriv_continuous q
  have hf2 : Continuous (deriv (deriv f)) := normalizedMean_second_continuous q
  have hψ : Continuous ψ := testWindow_smooth.continuous.comp
    (continuous_id.sub continuous_const)
  have hψ1 : Continuous ψ1 := testWindow_deriv_smooth.continuous.comp
    (continuous_id.sub continuous_const)
  have hψ2 : Continuous ψ2 := testWindow_second_smooth.continuous.comp
    (continuous_id.sub continuous_const)
  have hs0 : HasCompactSupport ψ := testWindow_shift_compact T
  have hs1 : HasCompactSupport ψ1 := testWindow_deriv_shift_compact T
  have hs2 : HasCompactSupport ψ2 := testWindow_second_shift_compact T
  have hfd : ∀ x, HasDerivAt f (deriv f x) x := normalizedMean_hasDerivAt q
  have hfd1 : ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    normalizedMean_deriv_hasDerivAt q
  have hψd : ∀ x, HasDerivAt ψ (ψ1 x) x := testWindow_shift_hasDerivAt T
  have hψd1 : ∀ x, HasDerivAt ψ1 (ψ2 x) x := testWindow_deriv_shift_hasDerivAt T
  have hib (g v : ℝ → ℂ) (hg : Continuous g) (hv : Continuous v)
      (hs : HasCompactSupport g) : Integrable (fun x => v x * g x) := by
    have h : Integrable (fun x => g x * v x) :=
      (hg.mul hv).integrable_of_hasCompactSupport hs.mul_right
    simpa only [mul_comm] using h
  have hi2 : Integrable (fun t => deriv (deriv f) t * ψ t) :=
    hib ψ (deriv (deriv f)) hψ hf2 hs0
  have hi1 : Integrable (fun t => deriv f t * ψ t) := hib ψ (deriv f) hψ hf1 hs0
  have hi0 : Integrable (fun t => f t * ψ t) := hib ψ f hψ hf hs0
  have h2 := compact_second_ibp f ψ ψ1 ψ2 hf hf1 hf2 hψ hψ1 hψ2
    hs0 hs1 hs2 hfd hfd1 hψd hψd1
  have h1 := compact_first_ibp f ψ ψ1 hf hf1 hψ hψ1 hs0 hs1 hfd hψd
  change (∫ t : ℝ, normalizedForcing q t * ψ t) = _
  calc
    _ = ∫ t : ℝ,
          (deriv (deriv f) t * ψ t + A*(deriv f t * ψ t)) + B*(f t * ψ t) := by
          apply integral_congr_ae
          filter_upwards [] with t
          rw [normalizedForcing_eq_log_operator]
          dsimp [f, A, B]
          ring
    _ = (∫ t : ℝ, deriv (deriv f) t * ψ t) +
          A*(∫ t : ℝ, deriv f t * ψ t) + B*(∫ t : ℝ, f t * ψ t) := by
          change (∫ t : ℝ,
              ((fun t => deriv (deriv f) t * ψ t) +
                (fun t => A*(deriv f t * ψ t)) +
                (fun t => B*(f t * ψ t))) t) = _
          rw [integral_add' (hi2.add (hi1.const_mul A)) (hi0.const_mul B),
            integral_add' hi2 (hi1.const_mul A), integral_const_mul, integral_const_mul]
    _ = (∫ t : ℝ, f t * ψ2 t) - A*(∫ t : ℝ, f t * ψ1 t) +
          B*(∫ t : ℝ, f t * ψ t) := by rw [h2,h1]; ring
    _ = _ := by dsimp only [f,ψ,ψ1,ψ2,A,B]

private theorem compact_test_bounded (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hs : ∀ s, s ∉ Icc (-1:ℝ) 1 → φ s = 0) :
    ∃ M : ℝ, ∀ s, ‖φ s‖ ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨max M 0,fun s => ?_⟩
  by_cases hmem : s ∈ Icc (-1:ℝ) 1
  · exact (hM s hmem).trans (le_max_left _ _)
  · rw [hs s hmem,norm_zero]
    exact le_max_right _ _

private theorem normalizedMean_translated_test_limit (q : XiZeroCopy)
    (hleft : (q.1:ℂ).re < 1/2) (φ : ℝ → ℂ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : ∀ s, s ∉ Icc (-1:ℝ) 1 → φ s = 0) :
    Tendsto (fun T : ℝ => ∫ t : ℝ, normalizedMean q t * φ (t-T))
      atTop (𝓝 ((responseCoefficient q true 2 * responseCoefficient q false 2) *
        ∫ s : ℝ, φ s)) := by
  let C := responseCoefficient q true 2 * responseCoefficient q false 2
  obtain ⟨M,hM⟩ := compact_test_bounded φ hφ hs
  have hφint : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hP := translated_limit_pairing (principalNorm q) φ C
    (normalizedPrincipal_tendsto q hleft) (principalNorm_continuous q).measurable
    hφ.measurable hφint hs
  have hE := translated_L1_pairing_vanish (errorCut q) φ
    (errorCut_integrable q hleft) hφ.measurable hM
    (fun s hsmall => hs s (fun h => by have := h.1; linarith))
  have hsum : Tendsto (fun T : ℝ =>
      (∫ t : ℝ, principalNorm q t * φ (t-T)) +
      (∫ t : ℝ, errorCut q t * φ (t-T))) atTop
      (𝓝 (C * ∫ s : ℝ, φ s)) := by
    simpa only [add_zero] using hP.add hE
  have hshift (T : ℝ) : Continuous (fun t : ℝ => φ (t-T)) :=
    hφ.comp (continuous_id.sub continuous_const)
  have hcompact (T : ℝ) : HasCompactSupport (fun t : ℝ => φ (t-T)) := by
    simpa [Function.comp_def,sub_eq_add_neg] using
      hc.comp_homeomorph (Homeomorph.addRight (-T))
  have hPint (T : ℝ) : Integrable (fun t : ℝ => principalNorm q t * φ (t-T)) := by
    have hi : Integrable (fun t : ℝ => φ (t-T) * principalNorm q t) :=
      ((hshift T).mul (principalNorm_continuous q)).integrable_of_hasCompactSupport
        (hcompact T).mul_right
    simpa only [mul_comm] using hi
  have hEint (T : ℝ) : Integrable (fun t : ℝ => errorCut q t * φ (t-T)) := by
    apply Integrable.mono' ((errorCut_integrable q hleft).norm.const_mul M)
    · exact (errorCut_integrable q hleft).aestronglyMeasurable.mul
        ((hφ.measurable.comp (measurable_id.sub measurable_const)).aestronglyMeasurable)
    · exact ae_of_all _ (fun t => by
        rw [norm_mul]
        calc
          ‖errorCut q t‖ * ‖φ (t-T)‖ ≤ ‖errorCut q t‖ * M :=
            mul_le_mul_of_nonneg_left (hM (t-T)) (norm_nonneg _)
          _ = M * ‖errorCut q t‖ := mul_comm _ _)
  have hmatch (t : ℝ) (ht : Real.log 3 < t) :
      normalizedMean q t = principalNorm q t + errorCut q t := by
    have hmem : t ∈ Ioi (Real.log 3) := ht
    simp only [normalizedMean,principalNorm,errorCut,errorFull,
      Set.indicator_of_mem hmem]
    ring
  have heq (T : ℝ) (hT : Real.log 3 + 1 < T) :
      (∫ t : ℝ, normalizedMean q t * φ (t-T)) =
        (∫ t : ℝ, principalNorm q t * φ (t-T)) +
        (∫ t : ℝ, errorCut q t * φ (t-T)) := by
    calc
      _ = ∫ t : ℝ, principalNorm q t * φ (t-T) + errorCut q t * φ (t-T) := by
        apply integral_congr_ae
        filter_upwards [] with t
        by_cases hmem : t-T ∈ Icc (-1:ℝ) 1
        · have ht : Real.log 3 < t := by have := hmem.1; linarith
          rw [hmatch t ht]
          ring
        · rw [hs (t-T) hmem]
          ring
      _ = _ := integral_add (hPint T) (hEint T)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (Real.log 3 + 1)] with T hT
  exact (heq T hT).symm

private theorem testWindow_deriv_support {s : ℝ} (hs : s ∉ Icc (-1:ℝ) 1) :
    deriv testWindow s = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hs (testWindow_deriv_tsupport h))

private theorem testWindow_second_support {s : ℝ} (hs : s ∉ Icc (-1:ℝ) 1) :
    deriv (deriv testWindow) s = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hs (testWindow_second_tsupport h))

/-- The actual two-branch clock forcing has a nonzero translated cusp source charge. -/
theorem normalizedForcing_translated_charge (q : XiZeroCopy)
    (hleft : (q.1:ℂ).re < 1/2) :
    Tendsto (fun T : ℝ => ∫ t : ℝ, normalizedForcing q t * testWindow (t-T))
      atTop (𝓝 ((rate q*(rate q-1)-20) *
        (responseCoefficient q true 2 * responseCoefficient q false 2) *
        (cuspWindowMoment 0:ℂ))) := by
  let C := responseCoefficient q true 2 * responseCoefficient q false 2
  let A := 2*rate q-1
  let B := rate q*(rate q-1)-20
  have h0 := normalizedMean_translated_test_limit q hleft testWindow
    testWindow_continuous testWindow_compact (fun s hs => testWindow_support hs)
  have h1 := normalizedMean_translated_test_limit q hleft (deriv testWindow)
    testWindow_deriv_smooth.continuous testWindow_deriv_compact
    (fun s hs => testWindow_deriv_support hs)
  have h2 := normalizedMean_translated_test_limit q hleft (deriv (deriv testWindow))
    testWindow_second_smooth.continuous testWindow_second_compact
    (fun s hs => testWindow_second_support hs)
  have hh : Tendsto (fun T : ℝ =>
      (∫ t : ℝ, normalizedMean q t * deriv (deriv testWindow) (t-T)) -
      A*(∫ t : ℝ, normalizedMean q t * deriv testWindow (t-T)) +
      B*(∫ t : ℝ, normalizedMean q t * testWindow (t-T)))
      atTop (𝓝 (B*C*(cuspWindowMoment 0:ℂ))) := by
    have h := (h2.sub (h1.const_mul A)).add (h0.const_mul B)
    simpa only [testWindow_deriv_mass_zero,testWindow_second_mass_zero,
      mul_zero,zero_mul,sub_zero,zero_add,testWindow_mass,mul_assoc,mul_left_comm,mul_comm,
      C,A,B] using h
  apply hh.congr'
  filter_upwards with T
  simpa only [A,B] using (normalizedForcing_test_adjoint q T).symm

/-- Nonzero translated charge excludes integrability on the actual upper cusp,
not merely on the whole logarithmic line. -/
theorem normalizedForcing_cusp_not_integrable (q : XiZeroCopy)
    (hleft : (q.1:ℂ).re < 1/2) :
    ¬ IntegrableOn (normalizedForcing q) (Ioi (Real.log 3)) := by
  intro hi
  have hcut : Integrable ((Ioi (Real.log 3)).indicator (normalizedForcing q)) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hi
  obtain ⟨M,hM⟩ := testWindow_bounded
  have hzero := translated_L1_pairing_vanish
    ((Ioi (Real.log 3)).indicator (normalizedForcing q)) testWindow
    hcut testWindow_continuous.measurable hM
    (fun s hs => testWindow_support (fun h => by have := h.1; linarith))
  have heq (T : ℝ) (hT : Real.log 3 + 1 < T) :
      (∫ t : ℝ, normalizedForcing q t * testWindow (t-T)) =
        ∫ t : ℝ, (Ioi (Real.log 3)).indicator (normalizedForcing q) t *
          testWindow (t-T) := by
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases hs : t-T ∈ Icc (-1:ℝ) 1
    · have ht : t ∈ Ioi (Real.log 3) := by
        have := hs.1
        change Real.log 3 < t
        linarith
      rw [Set.indicator_of_mem ht]
    · rw [testWindow_support hs]
      ring
  have hzero' : Tendsto
      (fun T : ℝ => ∫ t : ℝ, normalizedForcing q t * testWindow (t-T))
      atTop (𝓝 (0:ℂ)) := by
    apply hzero.congr'
    filter_upwards [eventually_gt_atTop (Real.log 3 + 1)] with T hT
    exact (heq T hT).symm
  have hcharge := normalizedForcing_translated_charge q hleft
  have hgap : rate q*(rate q-1)-20 ≠ 0 := rate_clock_gap_ne_zero q hleft
  have hcoeff : responseCoefficient q true 2 * responseCoefficient q false 2 ≠ 0 :=
    (RHTower.D4BMPWCrossClockPrincipalGrowth.cuspResponse_cross_left_normalized_nonzero
      q hleft).1
  have hmass : (cuspWindowMoment 0:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr cuspWindowMoment_zero_pos.ne'
  have hnonzero : (rate q*(rate q-1)-20) *
      (responseCoefficient q true 2 * responseCoefficient q false 2) *
      (cuspWindowMoment 0:ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hgap hcoeff) hmass
  exact hnonzero (tendsto_nhds_unique hcharge hzero')

/-- Whole-line nonintegrability follows from the sharp upper-cusp obstruction. -/
theorem normalizedForcing_not_integrable (q : XiZeroCopy)
    (hleft : (q.1:ℂ).re < 1/2) :
    ¬ Integrable (normalizedForcing q) :=
  fun hi => normalizedForcing_cusp_not_integrable q hleft hi.integrableOn

end RHTower.D4BMPWCrossClockTranslatedTests
