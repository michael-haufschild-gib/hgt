import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWCrossClockLogError
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWindowMoments

open Complex MeasureTheory Set Filter Topology
open RHTower RHTower.D4BMModularCore
open RHTower.D4BMPWCrossClockMeanEquation RHTower.D4BMPWCrossClockMeanError
open RHTower.D4BMPWCrossClockLogIdentity RHTower.D4BMPWCrossClockLogError
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

end RHTower.D4BMPWCrossClockTranslatedTests
