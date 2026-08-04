import GaloisForLFunctions.HTGeometry.VolterraLinearIntegralEquation

/-!
# The Volterra equation with locally bounded data

The perturbation series of the previous file asks for one bound on the kernel and one on the free
term, valid for all times. A propagator whose energy grows — the hyperbolic evolution of a
*time-dependent* principal part is the example — has bounds on every window of times and none on the
line.

Nothing has to be reproved. The Picard iterates at a time inside a window never evaluate the data
outside it, because the integral runs between `0` and that time. So the iterates, and hence the
solution, agree with those of the data clamped to the window, and the clamped data satisfy the
global hypotheses with the window's constants. Every conclusion transports along that equality.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory intervalIntegral

open scoped Interval

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Clamping a time to a window -/

/-- The time, clamped to the window `[-T, T]`. -/
noncomputable def timeClamp (T t : ℝ) : ℝ := max (-T) (min T t)

theorem continuous_timeClamp (T : ℝ) : Continuous (timeClamp T) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem timeClamp_of_abs_le {T t : ℝ} (h : |t| ≤ T) : timeClamp T t = t := by
  have hpair := abs_le.mp h
  rw [timeClamp, min_eq_right hpair.2, max_eq_right hpair.1]

theorem abs_timeClamp_le {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : |timeClamp T t| ≤ T := by
  rw [abs_le]
  refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-! ## The iterates only see the window -/

/-- **Data agreeing on a window give the same Picard iterates inside it.** -/
theorem volterraIterate_congr_of_window {f f' : ℝ → X} {K K' : ℝ → ℝ → X →L[ℝ] X} {T : ℝ}
    (hf : ∀ s : ℝ, |s| ≤ T → f s = f' s)
    (hK : ∀ t s : ℝ, |t| ≤ T → |s| ≤ T → K t s = K' t s) :
    ∀ (n : ℕ) (t : ℝ), |t| ≤ T → volterraIterate f K n t = volterraIterate f' K' n t := by
  intro n
  induction n with
  | zero =>
    intro t ht
    exact hf t ht
  | succ n ih =>
    intro t ht
    rw [volterraIterate_succ, volterraIterate_succ, hf t ht]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hsT : |s| ≤ T := le_trans (abs_le_abs_of_mem_uIcc_zero hs) ht
    rw [hK t s ht hsT, ih s hsT]

/-- **Hence the solutions agree on the window.** -/
theorem volterraSolution_congr_of_window {f f' : ℝ → X} {K K' : ℝ → ℝ → X →L[ℝ] X} {T : ℝ}
    (hf : ∀ s : ℝ, |s| ≤ T → f s = f' s)
    (hK : ∀ t s : ℝ, |t| ≤ T → |s| ≤ T → K t s = K' t s) {t : ℝ} (ht : |t| ≤ T) :
    volterraSolution f K t = volterraSolution f' K' t := by
  rw [volterraSolution, volterraSolution, hf t ht]
  congr 1
  refine tsum_congr fun n => ?_
  rw [volterraIterate_congr_of_window hf hK (n + 1) t ht,
    volterraIterate_congr_of_window hf hK n t ht]

/-! ## The windowed conclusions -/

section Clamp

variable {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X} {M F T : ℝ}

/-- The free term, clamped to the window. -/
noncomputable def volterraClampF (T : ℝ) (f : ℝ → X) : ℝ → X := fun t => f (timeClamp T t)

/-- The kernel, clamped to the window. -/
noncomputable def volterraClampK (T : ℝ) (K : ℝ → ℝ → X →L[ℝ] X) : ℝ → ℝ → X →L[ℝ] X :=
  fun t s => K (timeClamp T t) (timeClamp T s)

omit [NormedSpace ℝ X] in
theorem continuous_volterraClampF (T : ℝ) (hf : Continuous f) :
    Continuous (volterraClampF T f) := hf.comp (continuous_timeClamp T)

theorem continuous_volterraClampK (T : ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) :
    Continuous fun p : ℝ × ℝ => volterraClampK T K p.1 p.2 :=
  hK.comp (((continuous_timeClamp T).comp continuous_fst).prodMk
    ((continuous_timeClamp T).comp continuous_snd))

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem volterraClampF_eq {T : ℝ} {s : ℝ} (hs : |s| ≤ T) : f s = volterraClampF T f s := by
  rw [volterraClampF, timeClamp_of_abs_le hs]

theorem volterraClampK_eq {T : ℝ} {t s : ℝ} (ht : |t| ≤ T) (hs : |s| ≤ T) :
    K t s = volterraClampK T K t s := by
  rw [volterraClampK, timeClamp_of_abs_le ht, timeClamp_of_abs_le hs]

omit [NormedSpace ℝ X] in
theorem norm_volterraClampF_le (hT : 0 ≤ T) (hfb : ∀ t : ℝ, |t| ≤ T → ‖f t‖ ≤ F) (t : ℝ) :
    ‖volterraClampF T f t‖ ≤ F := hfb _ (abs_timeClamp_le hT t)

theorem norm_volterraClampK_le (hT : 0 ≤ T)
    (hKb : ∀ t s : ℝ, |t| ≤ T → |s| ≤ T → ‖K t s‖ ≤ M) (t s : ℝ) :
    ‖volterraClampK T K t s‖ ≤ M :=
  hKb _ _ (abs_timeClamp_le hT t) (abs_timeClamp_le hT s)

theorem volterraSolution_eq_clamp {t : ℝ} (ht : |t| ≤ T) :
    volterraSolution f K t = volterraSolution (volterraClampF T f) (volterraClampK T K) t :=
  volterraSolution_congr_of_window (fun _ hs => volterraClampF_eq hs)
    (fun _ _ hr hq => volterraClampK_eq hr hq) ht

end Clamp

section Windowed

variable [CompleteSpace X] {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X} {M F T : ℝ}

/-- **The solution satisfies the Volterra equation inside a window on which the data are
bounded.** -/
theorem volterraSolution_eq_window (hf : Continuous f)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hT : 0 ≤ T) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hKb : ∀ t s : ℝ, |t| ≤ T → |s| ≤ T → ‖K t s‖ ≤ M)
    (hfb : ∀ t : ℝ, |t| ≤ T → ‖f t‖ ≤ F) {t : ℝ} (ht : |t| ≤ T) :
    volterraSolution f K t = f t + ∫ s in (0 : ℝ)..t, K t s (volterraSolution f K s) := by
  have hbase := volterraSolution_eq (f := volterraClampF T f) (K := volterraClampK T K)
    (continuous_volterraClampF T hf) (continuous_volterraClampK T hK) hM hF
    (norm_volterraClampK_le hT hKb) (norm_volterraClampF_le hT hfb) t
  rw [volterraSolution_eq_clamp ht, hbase, ← volterraClampF_eq ht]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hsT : |s| ≤ T := le_trans (abs_le_abs_of_mem_uIcc_zero hs) ht
  rw [← volterraClampK_eq ht hsT, ← volterraSolution_eq_clamp hsT]

/-- **The exponential bound inside the window.** -/
theorem norm_volterraSolution_le_window (hf : Continuous f)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hT : 0 ≤ T) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hKb : ∀ t s : ℝ, |t| ≤ T → |s| ≤ T → ‖K t s‖ ≤ M)
    (hfb : ∀ t : ℝ, |t| ≤ T → ‖f t‖ ≤ F) {t : ℝ} (ht : |t| ≤ T) :
    ‖volterraSolution f K t‖ ≤ F * Real.exp (M * |t|) := by
  rw [volterraSolution_eq_clamp ht]
  exact norm_volterraSolution_le (continuous_volterraClampF T hf)
    (continuous_volterraClampK T hK) hM hF (norm_volterraClampK_le hT hKb)
    (norm_volterraClampF_le hT hfb) t

/-- **Continuity inside the window.** -/
theorem continuousOn_volterraSolution_window (hf : Continuous f)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hT : 0 ≤ T) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hKb : ∀ t s : ℝ, |t| ≤ T → |s| ≤ T → ‖K t s‖ ≤ M)
    (hfb : ∀ t : ℝ, |t| ≤ T → ‖f t‖ ≤ F) :
    ContinuousOn (volterraSolution f K) {t : ℝ | |t| ≤ T} := by
  refine ContinuousOn.congr
    (continuous_volterraSolution (f := volterraClampF T f) (K := volterraClampK T K)
      (continuous_volterraClampF T hf) (continuous_volterraClampK T hK) hM hF
      (norm_volterraClampK_le hT hKb) (norm_volterraClampF_le hT hfb)).continuousOn ?_
  intro t ht
  exact volterraSolution_eq_clamp (f := f) (K := K) ht

/-! ## Locally bounded data -/

/-- The data are bounded on every window. -/
def VolterraLocallyBounded (f : ℝ → X) (K : ℝ → ℝ → X →L[ℝ] X) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ M F : ℝ, 0 ≤ M ∧ 0 ≤ F ∧
    (∀ t s : ℝ, |t| ≤ T → |s| ≤ T → ‖K t s‖ ≤ M) ∧ (∀ t : ℝ, |t| ≤ T → ‖f t‖ ≤ F)

/-- **The solution satisfies the Volterra equation at every time**, for locally bounded data. -/
theorem volterraSolution_eq_of_locallyBounded (hf : Continuous f)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hloc : VolterraLocallyBounded f K) (t : ℝ) :
    volterraSolution f K t = f t + ∫ s in (0 : ℝ)..t, K t s (volterraSolution f K s) := by
  obtain ⟨M, F, hM, hF, hKb, hfb⟩ := hloc |t| (abs_nonneg t)
  exact volterraSolution_eq_window hf hK (abs_nonneg t) hM hF hKb hfb le_rfl

/-- **The solution is continuous**, for locally bounded data. -/
theorem continuous_volterraSolution_of_locallyBounded (hf : Continuous f)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hloc : VolterraLocallyBounded f K) :
    Continuous (volterraSolution f K) := by
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  obtain ⟨M, F, hM, hF, hKb, hfb⟩ := hloc (|t₀| + 1) (by positivity)
  have hmem : {t : ℝ | |t| ≤ |t₀| + 1} ∈ nhds t₀ := by
    have hopen : IsOpen {t : ℝ | |t| < |t₀| + 1} := isOpen_lt continuous_abs continuous_const
    have hsub : {t : ℝ | |t| < |t₀| + 1} ⊆ {t : ℝ | |t| ≤ |t₀| + 1} := by
      intro t ht
      simp only [Set.mem_setOf_eq] at ht ⊢
      exact le_of_lt ht
    have hmem₀ : t₀ ∈ {t : ℝ | |t| < |t₀| + 1} := by
      simp only [Set.mem_setOf_eq]
      linarith
    exact Filter.mem_of_superset (hopen.mem_nhds hmem₀) hsub
  exact (continuousOn_volterraSolution_window hf hK (by positivity) hM hF hKb hfb).continuousAt hmem

end Windowed

end GaloisForLFunctions.HTGeometry
