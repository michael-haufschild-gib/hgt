import GaloisForLFunctions.HTGeometry.ExpRayL2
import GaloisForLFunctions.HTGeometry.HalfPlaneGapApproximation
import GaloisForLFunctions.HTGeometry.WeightedHolder

/-!
# The half-line Laplace transform of an `L²` datum

For `φ` square-integrable on `(0, ∞)` the integral `∫_0^∞ φ(x)e^{-wx}dx` converges absolutely on
the half-plane `Re w > 0` and defines a holomorphic function there.  The truncations to `(0, T]`
are entire, and the tail is bounded by `‖φ‖ e^{-T Re w}/√(2 Re w)`, so the convergence is locally
uniform: this is the easy half of the Paley--Wiener description of the Hardy space of a half-plane.

## Main results

* `norm_laplaceRay_tail_le`
* `differentiable_laplaceRayTrunc`
* `differentiableOn_laplaceRay`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology

noncomputable section

/-- The half-line Laplace transform of an `L²` datum. -/
def laplaceRay (φ : ℝ → ℂ) (w : ℂ) : ℂ := ∫ x in Ioi (0 : ℝ), φ x * expRay w x

/-- The truncation of the half-line Laplace transform to `(0, T]`. -/
def laplaceRayTrunc (φ : ℝ → ℂ) (T : ℝ) (w : ℂ) : ℂ := ∫ x in Ioc (0 : ℝ) T, φ x * expRay w x

/-- The `L²` mass of the datum on the ray. -/
def rayL2Norm (φ : ℝ → ℂ) : ℝ := Real.sqrt (∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ 2)

theorem rayL2Norm_nonneg (φ : ℝ → ℂ) : 0 ≤ rayL2Norm φ := Real.sqrt_nonneg _

theorem integrableOn_norm_sq_of_memLp {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    IntegrableOn (fun x : ℝ => ‖φ x‖ ^ 2) (Ioi (0 : ℝ)) :=
  (memLp_two_iff_integrable_sq_norm hφ.aestronglyMeasurable).1 hφ

theorem integrableOn_laplaceRay {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun x : ℝ => φ x * expRay w x) (Ioi (0 : ℝ)) :=
  hφ.integrable_mul (memLp_two_expRay_restrict hw 0)

/-- **The tail estimate.**  Beyond `T` the Laplace integral is `O(e^{-T Re w})`, uniformly. -/
theorem norm_laplaceRay_tail_le {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {w : ℂ} (hw : 0 < w.re) {T : ℝ}
    (hT : 0 ≤ T) :
    ‖∫ x in Ioi T, φ x * expRay w x‖
      ≤ rayL2Norm φ * (Real.exp (-(w.re * T)) / Real.sqrt (2 * w.re)) := by
  have hsub : Ioi T ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hT
  have hφT : MemLp φ 2 (volume.restrict (Ioi T)) :=
    hφ.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hsqT : IntegrableOn (fun x : ℝ => ‖φ x‖ ^ 2) (Ioi T) :=
    (integrableOn_norm_sq_of_memLp hφ).mono_set hsub
  have hcs := integral_mul_le_sqrt_mul_sqrt_measure (μ := volume.restrict (Ioi T))
    hφT.aestronglyMeasurable ((continuous_expRay w).aestronglyMeasurable)
    hsqT (integrableOn_norm_sq_expRay hw T)
  have hnorm : ‖∫ x in Ioi T, φ x * expRay w x‖ ≤ ∫ x in Ioi T, ‖φ x‖ * ‖expRay w x‖ := by
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [norm_mul]
  have hmono : Real.sqrt (∫ x in Ioi T, ‖φ x‖ ^ 2) ≤ rayL2Norm φ := by
    refine Real.sqrt_le_sqrt ?_
    refine setIntegral_mono_set (integrableOn_norm_sq_of_memLp hφ) ?_ (LE.le.eventuallyLE hsub)
    filter_upwards with x
    positivity
  calc ‖∫ x in Ioi T, φ x * expRay w x‖
      ≤ ∫ x in Ioi T, ‖φ x‖ * ‖expRay w x‖ := hnorm
    _ ≤ Real.sqrt (∫ x in Ioi T, ‖φ x‖ ^ 2) * Real.sqrt (∫ x in Ioi T, ‖expRay w x‖ ^ 2) := hcs
    _ = Real.sqrt (∫ x in Ioi T, ‖φ x‖ ^ 2)
          * (Real.exp (-(w.re * T)) / Real.sqrt (2 * w.re)) := by
        rw [sqrt_integral_norm_sq_expRay hw T]
    _ ≤ rayL2Norm φ * (Real.exp (-(w.re * T)) / Real.sqrt (2 * w.re)) := by
        refine mul_le_mul_of_nonneg_right hmono ?_
        have h2 : (0 : ℝ) < 2 * w.re := by linarith
        positivity

/-- The Laplace integral minus its truncation is the tail. -/
theorem laplaceRay_sub_trunc {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {w : ℂ} (hw : 0 < w.re) {T : ℝ}
    (hT : 0 ≤ T) :
    laplaceRay φ w - laplaceRayTrunc φ T w = ∫ x in Ioi T, φ x * expRay w x := by
  have hint := integrableOn_laplaceRay hφ hw
  have hunion : Ioc (0 : ℝ) T ∪ Ioi T = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hT
  have hdisj : Disjoint (Ioc (0 : ℝ) T) (Ioi T) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.2 hx')
  have hsplit : (∫ x in Ioi (0 : ℝ), φ x * expRay w x)
      = (∫ x in Ioc (0 : ℝ) T, φ x * expRay w x) + ∫ x in Ioi T, φ x * expRay w x := by
    rw [← hunion] at hint ⊢
    exact setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set Set.subset_union_left) (hint.mono_set Set.subset_union_right)
  rw [laplaceRay, laplaceRayTrunc, hsplit]
  ring

/-! ### The truncations are entire -/

/-- The clamp of a real number into `[0, T]`. -/
def rayClamp (T x : ℝ) : ℝ := max 0 (min x T)

theorem rayClamp_nonneg (T x : ℝ) : 0 ≤ rayClamp T x := le_max_left _ _

theorem rayClamp_le {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : rayClamp T x ≤ T :=
  max_le hT (min_le_right _ _)

theorem rayClamp_eq_self {T x : ℝ} (hx : x ∈ Ioc (0 : ℝ) T) : rayClamp T x = x := by
  rw [rayClamp, min_eq_left hx.2, max_eq_right hx.1.le]

theorem continuous_rayClamp (T : ℝ) : Continuous (rayClamp T) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem hasDerivAt_expRay_shift (c : ℝ) (a w : ℂ) :
    HasDerivAt (fun z : ℂ => expRay (z - a) c) (-((c : ℝ) : ℂ) * expRay (w - a) c) w := by
  have h0 : HasDerivAt (fun z : ℂ => -((c : ℝ) : ℂ) * z + a * ((c : ℝ) : ℂ))
      (-((c : ℝ) : ℂ)) w := by
    simpa using ((hasDerivAt_id w).const_mul (-((c : ℝ) : ℂ))).add_const (a * ((c : ℝ) : ℂ))
  have h1 : HasDerivAt (fun z : ℂ => -((z - a) * ((c : ℝ) : ℂ))) (-((c : ℝ) : ℂ)) w :=
    h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by ring)
  refine (h1.cexp).congr_deriv ?_
  rw [expRay]
  ring

/-- **The truncated Laplace transform is entire.** -/
theorem differentiable_laplaceRayTrunc {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {T : ℝ} (hT : 0 ≤ T) :
    Differentiable ℂ (laplaceRayTrunc φ T) := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T) with hμ
  have hsub : Ioc (0 : ℝ) T ⊆ Ioi (0 : ℝ) := fun x hx => hx.1
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hbase : Integrable (fun x : ℝ => φ x * expRay 1 x) μ :=
    (integrableOn_laplaceRay hφ hone).mono_set hsub
  have hfun : laplaceRayTrunc φ T
      = fun w : ℂ => ∫ x, (φ x * expRay 1 x) * expRay (w - 1) (rayClamp T x) ∂μ := by
    funext w
    rw [laplaceRayTrunc, hμ]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [rayClamp_eq_self hx]
    simp only [expRay]
    have hexp : -((1 : ℂ) * ((x : ℝ) : ℂ)) + -((w - 1) * ((x : ℝ) : ℂ))
        = -(w * ((x : ℝ) : ℂ)) := by ring
    rw [mul_assoc, ← Complex.exp_add, hexp]
  rw [hfun]
  refine differentiable_integral_kernel μ hbase
    (fun x w => expRay (w - 1) (rayClamp T x))
    (fun x w => -((rayClamp T x : ℝ) : ℂ) * expRay (w - 1) (rayClamp T x))
    (fun w => ((continuous_expRay (w - 1)).comp (continuous_rayClamp T)).measurable)
    (fun w => (((Complex.continuous_ofReal.comp (continuous_rayClamp T)).neg).mul
      ((continuous_expRay (w - 1)).comp (continuous_rayClamp T))).measurable)
    ?_ ?_
  · intro x w
    exact hasDerivAt_expRay_shift (rayClamp T x) 1 w
  · intro w₀
    refine ⟨max (Real.exp ((‖w₀‖ + 2) * T)) (T * Real.exp ((‖w₀‖ + 2) * T)), ?_⟩
    intro x w hw
    have hd : ‖w - w₀‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.1 hw
    have hre : |(w - 1).re| ≤ ‖w₀‖ + 2 := by
      have h1 : |(w - 1).re| ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
      have h2 : ‖w - 1‖ ≤ ‖w - w₀‖ + ‖w₀‖ + 1 := by
        calc ‖w - 1‖ = ‖(w - w₀) + w₀ - 1‖ := by ring_nf
          _ ≤ ‖(w - w₀) + w₀‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖w - w₀‖ + ‖w₀‖ + 1 := by
              have := norm_add_le (w - w₀) w₀
              simp only [norm_one] at *
              linarith
      linarith
    have hK : ‖expRay (w - 1) (rayClamp T x)‖ ≤ Real.exp ((‖w₀‖ + 2) * T) := by
      rw [norm_expRay]
      refine Real.exp_le_exp.2 ?_
      have hc0 := rayClamp_nonneg T x
      have hcT := rayClamp_le hT x
      have habs : -((w - 1).re * rayClamp T x) ≤ |(w - 1).re| * T := by
        have h1 : -((w - 1).re * rayClamp T x) ≤ |(w - 1).re * rayClamp T x| := neg_le_abs _
        have h2 : |(w - 1).re * rayClamp T x| = |(w - 1).re| * rayClamp T x := by
          rw [abs_mul, abs_of_nonneg hc0]
        have h3 : |(w - 1).re| * rayClamp T x ≤ |(w - 1).re| * T :=
          mul_le_mul_of_nonneg_left hcT (abs_nonneg _)
        linarith
      have h4 : |(w - 1).re| * T ≤ (‖w₀‖ + 2) * T := mul_le_mul_of_nonneg_right hre hT
      linarith
    refine ⟨le_trans hK (le_max_left _ _), ?_⟩
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (rayClamp_nonneg T x)]
    refine le_trans (mul_le_mul (rayClamp_le hT x) hK (norm_nonneg _) hT) (le_max_right _ _)

/-! ### Holomorphy on the right half-plane -/

/-- The truncations converge to the transform, locally uniformly on the right half-plane. -/
theorem tendstoLocallyUniformlyOn_laplaceRayTrunc {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    TendstoLocallyUniformlyOn (fun n : ℕ => laplaceRayTrunc φ (n : ℝ))
      (laplaceRay φ) atTop {w : ℂ | 0 < w.re} := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε w₀ hw₀
  have hw₀re : 0 < w₀.re := hw₀
  set σ₀ : ℝ := w₀.re / 2 with hσ₀
  have hσ₀pos : 0 < σ₀ := by rw [hσ₀]; linarith
  set B : ℝ := rayL2Norm φ / Real.sqrt (2 * σ₀) with hB
  have hB0 : 0 ≤ B := by
    have h := rayL2Norm_nonneg φ
    rw [hB]
    positivity
  refine ⟨{w : ℂ | σ₀ < w.re}, ?_, ?_⟩
  · refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds
      (isOpen_lt continuous_const Complex.continuous_re) ?_)
    simp only [Set.mem_setOf_eq, hσ₀]
    linarith
  · have hbase : Tendsto (fun n : ℕ => Real.exp (-(σ₀ * (n : ℝ))) * B) atTop (𝓝 0) := by
      have h := (tendsto_exp_neg_mul_atTop_nhds_zero hσ₀pos).comp tendsto_natCast_atTop_atTop
      simpa [Function.comp_def] using h.mul_const B
    have hev1 : ∀ᶠ n : ℕ in atTop, Real.exp (-(σ₀ * (n : ℝ))) * B < ε :=
      hbase.eventually (gt_mem_nhds hε)
    filter_upwards [hev1] with n hn1
    intro y hy
    have hyre : σ₀ < y.re := hy
    have hy0 : 0 < y.re := lt_trans hσ₀pos hyre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hb : ‖laplaceRay φ y - laplaceRayTrunc φ (n : ℝ) y‖
        ≤ rayL2Norm φ * (Real.exp (-(y.re * (n : ℝ))) / Real.sqrt (2 * y.re)) := by
      rw [laplaceRay_sub_trunc hφ hy0 hn0]
      exact norm_laplaceRay_tail_le hφ hy0 hn0
    have hstep : rayL2Norm φ * (Real.exp (-(y.re * (n : ℝ))) / Real.sqrt (2 * y.re))
        ≤ Real.exp (-(σ₀ * (n : ℝ))) * B := by
      have hexp : Real.exp (-(y.re * (n : ℝ))) ≤ Real.exp (-(σ₀ * (n : ℝ))) := by
        refine Real.exp_le_exp.2 ?_
        have : σ₀ * (n : ℝ) ≤ y.re * (n : ℝ) := mul_le_mul_of_nonneg_right hyre.le hn0
        linarith
      have hsq : Real.sqrt (2 * σ₀) ≤ Real.sqrt (2 * y.re) := by
        refine Real.sqrt_le_sqrt ?_
        linarith
      have hsq0 : 0 < Real.sqrt (2 * σ₀) := Real.sqrt_pos.2 (by linarith)
      have hN := rayL2Norm_nonneg φ
      rw [hB]
      calc rayL2Norm φ * (Real.exp (-(y.re * (n : ℝ))) / Real.sqrt (2 * y.re))
          ≤ rayL2Norm φ * (Real.exp (-(σ₀ * (n : ℝ))) / Real.sqrt (2 * σ₀)) := by
            gcongr
        _ = Real.exp (-(σ₀ * (n : ℝ))) * (rayL2Norm φ / Real.sqrt (2 * σ₀)) := by ring
    rw [Complex.dist_eq]
    exact lt_of_le_of_lt (le_trans hb hstep) hn1

/-- **The half-line Laplace transform of an `L²` datum is holomorphic on `Re w > 0`.** -/
theorem differentiableOn_laplaceRay {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    DifferentiableOn ℂ (laplaceRay φ) {w : ℂ | 0 < w.re} := by
  refine TendstoLocallyUniformlyOn.differentiableOn
    (tendstoLocallyUniformlyOn_laplaceRayTrunc hφ) ?_
    (isOpen_lt continuous_const Complex.continuous_re)
  filter_upwards with n
  exact (differentiable_laplaceRayTrunc hφ (Nat.cast_nonneg n)).differentiableOn

/-- **Elements of the Hardy space are bounded away from the boundary.** -/
theorem norm_laplaceRay_le {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {w : ℂ} (hw : 0 < w.re) :
    ‖laplaceRay φ w‖ ≤ rayL2Norm φ / Real.sqrt (2 * w.re) := by
  have h := norm_laplaceRay_tail_le hφ hw (le_refl (0 : ℝ))
  have h0 : Real.exp (-(w.re * (0 : ℝ))) = 1 := by norm_num
  rw [h0, mul_one_div] at h
  rw [laplaceRay]
  exact h

end

end GaloisForLFunctions.HTGeometry
