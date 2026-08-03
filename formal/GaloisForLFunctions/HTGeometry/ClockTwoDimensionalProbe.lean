import GaloisForLFunctions.HTGeometry.ClockGoursatC2
import GaloisForLFunctions.HTGeometry.ClockCharacteristicProbe

/-!
# Every potential on a two-dimensional clock spacetime carries a probe

The characteristic form of the clock equation on two-dimensional Minkowski space is the Goursat
problem `∂ξ∂η u = K u` with the kernel `K = V/4` read in null coordinates. Its solution normalised
to `1` along a characteristic exists, is twice continuously differentiable when the potential is
continuously differentiable, and transports through the null frame to a clock probe.

So the two-dimensional inverse step closes with no hypothesis on the potential beyond one
derivative: at every event there is a clock probe taking the value `1` there. Since a probe which
does not vanish at an event already determines the potential at that event, a two-dimensional clock
potential is determined by its probes everywhere.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- The point of a two-dimensional coordinate space with prescribed coordinates. -/
def pairPoint (ξ η : ℝ) : Fin (1 + 1) → ℝ := fun i => if i = 0 then ξ else η

theorem pairPoint_zero (ξ η : ℝ) : pairPoint ξ η 0 = ξ := if_pos rfl

theorem pairPoint_one (ξ η : ℝ) : pairPoint ξ η 1 = η := if_neg (Ne.symm fin_zero_ne_one)

theorem pairPoint_self (y : Fin (1 + 1) → ℝ) : pairPoint (y 0) (y 1) = y :=
  fin_two_ext (pairPoint_zero _ _) (pairPoint_one _ _)

/-- The kernel of the characteristic equation attached to a potential. -/
noncomputable def nullKernel (V : (Fin (1 + 1) → ℝ) → ℝ) (p : ℝ × ℝ) : ℝ :=
  V (invNullFrame (pairPoint p.1 p.2)) / 4

theorem nullKernel_nullFrame (V : (Fin (1 + 1) → ℝ) → ℝ) (x : Fin (1 + 1) → ℝ) :
    nullKernel V (nullFrame x 0, nullFrame x 1) = V x / 4 := by
  rw [nullKernel]
  congr 2
  rw [pairPoint_self, invNullFrame_nullFrame]

theorem contDiff_nullKernel {V : (Fin (1 + 1) → ℝ) → ℝ} (hV : ContDiff ℝ 1 V) :
    ContDiff ℝ 1 (nullKernel V) := by
  have hlin : ContDiff ℝ 1 fun p : ℝ × ℝ => invNullFrame (pairPoint p.1 p.2) := by
    refine contDiff_pi.mpr fun i => ?_
    fin_cases i
    · show ContDiff ℝ 1 fun p : ℝ × ℝ => invNullFrame (pairPoint p.1 p.2) 0
      have hcoord : (fun p : ℝ × ℝ => invNullFrame (pairPoint p.1 p.2) 0)
          = fun p : ℝ × ℝ => (p.1 + p.2) / 2 := by
        funext p
        rw [invNullFrame_zero, pairPoint_zero, pairPoint_one]
      rw [hcoord]
      exact (contDiff_fst.add contDiff_snd).div_const 2
    · show ContDiff ℝ 1 fun p : ℝ × ℝ => invNullFrame (pairPoint p.1 p.2) 1
      have hcoord : (fun p : ℝ × ℝ => invNullFrame (pairPoint p.1 p.2) 1)
          = fun p : ℝ × ℝ => (p.1 - p.2) / 2 := by
        funext p
        rw [invNullFrame_one, pairPoint_zero, pairPoint_one]
      rw [hcoord]
      exact (contDiff_fst.sub contDiff_snd).div_const 2
  exact (hV.comp hlin).div_const 4

/-! ## The partial derivatives of a continuously differentiable bivariate function -/

variable {F : ℝ × ℝ → ℝ}

/-- The first partial derivative, read off the total derivative. -/
noncomputable def planarFst (F : ℝ × ℝ → ℝ) (ξ η : ℝ) : ℝ := fderiv ℝ F (ξ, η) (1, 0)

/-- The second partial derivative, read off the total derivative. -/
noncomputable def planarSnd (F : ℝ × ℝ → ℝ) (ξ η : ℝ) : ℝ := fderiv ℝ F (ξ, η) (0, 1)

theorem continuous_planarFst (hF : ContDiff ℝ 1 F) :
    Continuous fun p : ℝ × ℝ => planarFst F p.1 p.2 :=
  (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_planarSnd (hF : ContDiff ℝ 1 F) :
    Continuous fun p : ℝ × ℝ => planarSnd F p.1 p.2 :=
  (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem hasDerivAt_planarFst (hF : ContDiff ℝ 1 F) (ξ t : ℝ) :
    HasDerivAt (fun w => F (w, t)) (planarFst F ξ t) ξ := by
  have h1 : HasFDerivAt F (fderiv ℝ F (ξ, t)) (ξ, t) :=
    (hF.differentiable one_ne_zero (ξ, t)).hasFDerivAt
  have h2 : HasFDerivAt (fun w : ℝ => (w, t))
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) ξ :=
    (hasFDerivAt_id ξ).prodMk (hasFDerivAt_const t ξ)
  have h3 := (h1.comp ξ h2).hasDerivAt
  have hval : ((fderiv ℝ F (ξ, t)).comp ((ContinuousLinearMap.id ℝ ℝ).prod 0)) 1
      = planarFst F ξ t := by simp [planarFst]
  rw [hval] at h3
  exact h3

theorem hasDerivAt_planarSnd (hF : ContDiff ℝ 1 F) (ξ t : ℝ) :
    HasDerivAt (fun w => F (ξ, w)) (planarSnd F ξ t) t := by
  have h1 : HasFDerivAt F (fderiv ℝ F (ξ, t)) (ξ, t) :=
    (hF.differentiable one_ne_zero (ξ, t)).hasFDerivAt
  have h2 : HasFDerivAt (fun w : ℝ => (ξ, w))
      ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) t :=
    (hasFDerivAt_const ξ t).prodMk (hasFDerivAt_id t)
  have h3 := (h1.comp t h2).hasDerivAt
  have hval : ((fderiv ℝ F (ξ, t)).comp ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ))) 1
      = planarSnd F ξ t := by simp [planarSnd]
  rw [hval] at h3
  exact h3

/-! ## The probe -/

/-- **Every continuously differentiable potential on a two-dimensional clock spacetime admits a
clock probe normalised to `1` at any prescribed event.** -/
theorem exists_clockProbe_two_dimensional {V : (Fin (1 + 1) → ℝ) → ℝ} (hV : ContDiff ℝ 1 V)
    (x : Fin (1 + 1) → ℝ) :
    ∃ U : (Fin (1 + 1) → ℝ) → ℝ,
      SolvesPotentialWaveAt
          (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert V U x ∧
        U x = 1 := by
  classical
  set F : ℝ × ℝ → ℝ := nullKernel V with hF_def
  have hFC : ContDiff ℝ 1 F := contDiff_nullKernel hV
  set ξ₀ : ℝ := nullFrame x 0 with hξ₀
  set η₀ : ℝ := nullFrame x 1 with hη₀
  set c : ℝ := ξ₀ - 1 with hc
  set c' : ℝ := ξ₀ + 1 with hc'
  set b : ℝ := η₀ - 1 with hb
  set b' : ℝ := η₀ + 1 with hb'
  have hcc : c ≤ c' := by rw [hc, hc']; linarith
  have hbb : b ≤ b' := by rw [hb, hb']; linarith
  obtain ⟨M, hMbound⟩ := ((isCompact_Icc (a := c) (b := c')).prod
    (isCompact_Icc (a := b) (b := b'))).exists_bound_of_continuousOn hFC.continuous.continuousOn
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg (F (c, b))) (hMbound (c, b) ⟨⟨le_rfl, hcc⟩, ⟨le_rfl, hbb⟩⟩)
  have hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |F (ξ, t)| ≤ M := by
    intro ξ hξ t ht
    have := hMbound (ξ, t) ⟨hξ, ht⟩
    rwa [Real.norm_eq_abs] at this
  obtain ⟨h, hh, u, A, B, Aa, Ab, Ba, Bb, hu0, _hujoint, hC1u, hC1A, hC1B, hAbeq, hBaeq⟩ :=
    exists_goursat_C2 (fun ξ η => F (ξ, η)) (planarFst F) (planarSnd F) b b' c c' M
      hFC.continuous (continuous_planarFst hFC) (continuous_planarSnd hFC)
      (hasDerivAt_planarFst hFC) (hasDerivAt_planarSnd hFC) hbb hcc hM0 hM ξ₀
  have hmemΩ : ((ξ₀, η₀) : ℝ × ℝ) ∈ (Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b' :=
    ⟨⟨⟨by linarith, by linarith⟩, by rw [hc, hc']; constructor <;> linarith⟩,
      by rw [hb, hb']; constructor <;> linarith⟩
  have hx : nullFrame x ∈ chartBox ((Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b') := hmemΩ
  have hker : F (ξ₀, η₀) = V x / 4 := by
    rw [hF_def, hξ₀, hη₀]
    exact nullKernel_nullFrame V x
  have hchar : Ab (nullFrame x 0) (nullFrame x 1) + Ba (nullFrame x 0) (nullFrame x 1)
      = V x * u (nullFrame x 0) (nullFrame x 1) / 2 := by
    rw [← hξ₀, ← hη₀, hAbeq (ξ₀, η₀) hmemΩ, hBaeq (ξ₀, η₀) hmemΩ]
    show F (ξ₀, η₀) * u ξ₀ η₀ + F (ξ₀, η₀) * u ξ₀ η₀ = V x * u ξ₀ η₀ / 2
    rw [hker]
    ring
  refine ⟨nullChartFun u, solvesPotentialWaveAt_nullChartFun hC1u hC1A hC1B hx hchar, ?_⟩
  show u (nullFrame x 0) (nullFrame x 1) = 1
  rw [← hξ₀]
  exact hu0 _

/-- **A two-dimensional clock spacetime has local probes at every event.** -/
theorem localProbesOn_univ_two_dimensional {V : (Fin (1 + 1) → ℝ) → ℝ} (hV : ContDiff ℝ 1 V) :
    LocalProbesOn (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert V
      Set.univ := by
  intro x _
  obtain ⟨U, hU, hUx⟩ := exists_clockProbe_two_dimensional hV x
  exact ⟨U, hU, by rw [hUx]; exact one_ne_zero⟩

/-- **The clock probes determine a two-dimensional potential completely.** If every probe of a
continuously differentiable potential is a probe of a second potential, the two agree everywhere.
No regularity at all is assumed of the second potential. -/
theorem potential_eq_of_probes_two_dimensional {V₁ V₂ : (Fin (1 + 1) → ℝ) → ℝ}
    (hV₁ : ContDiff ℝ 1 V₁)
    (hprobe : ∀ (U : (Fin (1 + 1) → ℝ) → ℝ) (x : Fin (1 + 1) → ℝ),
      SolvesPotentialWaveAt
          (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert V₁ U x →
        SolvesPotentialWaveAt
          (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert V₂ U x) :
    V₂ = V₁ := by
  have hEq := potential_eqOn_of_localProbes
    (wave := (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert)
    (potential := V₁) (other := V₂) (region := Set.univ) ?_
  · exact funext fun x => hEq (Set.mem_univ x)
  · intro x _
    obtain ⟨U, hU, hUx⟩ := exists_clockProbe_two_dimensional hV₁ x
    exact ⟨U, hU, hprobe U x hU, by rw [hUx]; exact one_ne_zero⟩

end GaloisForLFunctions.HTGeometry
