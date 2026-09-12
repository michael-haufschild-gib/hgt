import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Smooth normalized angular averages

Compact angular integration preserves smoothness, commutes with two radial
derivatives, and kills derivatives of periodic functions. Bounds needed for
differentiation under the integral are derived from compact rectangles.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry.SmoothAngularAverage
noncomputable section

def average (f : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi : ℂ)) * ∫ theta in Ioc 0 (2 * Real.pi), f theta

def radialPartial (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ F p (1,0)

theorem partial_smooth {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialPartial F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem slice_hasDerivAt {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (r theta : ℝ) :
    HasDerivAt (fun t => F (t,theta)) (radialPartial F (r,theta)) r :=
  (hF.differentiable (by simp) (r,theta)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r theta))

theorem average_hasDerivAt {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (r : ℝ) :
    HasDerivAt (fun t => average (fun theta => F (t,theta)))
      (average (fun theta => radialPartial F (r,theta))) r := by
  have hD := partial_smooth hF
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hD.continuous.continuousOn : ContinuousOn (radialPartial F)
      (Icc (r-1) (r+1) ×ˢ Icc 0 (2*Real.pi)))
  have hneigh : Ioo (r-1) (r+1) ∈ 𝓝 r := Ioo_mem_nhds (by linarith) (by linarith)
  have hc (t : ℝ) : Continuous (fun theta => F (t,theta)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hd (t : ℝ) : Continuous (fun theta => radialPartial F (t,theta)) :=
    hD.continuous.comp (continuous_const.prodMk continuous_id)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 (2*Real.pi)))
    (F := fun t theta => F (t,theta)) (F' := fun t theta => radialPartial F (t,theta))
    (bound := fun _ => C) hneigh
    (Eventually.of_forall fun t => (hc t).aestronglyMeasurable.restrict)
    ((hc r).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((hd r).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
        intro t ht
        exact hC (t,theta) ⟨⟨ht.1.le,ht.2.le⟩,⟨htheta.1.le,htheta.2⟩⟩)
    (integrable_const C)
    (by filter_upwards with theta
        intro t _
        exact slice_hasDerivAt hF t theta)).2
  exact h.const_mul _

theorem average_deriv {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (r : ℝ) :
    deriv (fun t => average (fun theta => F (t,theta))) r =
      average (fun theta => deriv (fun t => F (t,theta)) r) := by
  rw [(average_hasDerivAt hF r).deriv]
  congr 1
  funext theta
  exact (slice_hasDerivAt hF r theta).deriv.symm

theorem average_second {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (r : ℝ) :
    deriv (deriv (fun t => average (fun theta => F (t,theta)))) r =
      average (fun theta => deriv (deriv (fun t => F (t,theta))) r) := by
  have hfirst : deriv (fun t => average (fun theta => F (t,theta))) =
      fun t => average (fun theta => radialPartial F (t,theta)) :=
    funext fun t => (average_hasDerivAt hF t).deriv
  rw [hfirst, average_deriv (partial_smooth hF)]
  congr 1
  funext theta
  have he : (fun t => radialPartial F (t,theta)) = deriv (fun t => F (t,theta)) :=
    funext fun t => (slice_hasDerivAt hF t theta).deriv.symm
  rw [he]

theorem average_smooth {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun t => average (fun theta => F (t,theta))) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing F with
  | zero =>
      have hd : Differentiable ℝ (fun t => average (fun theta => F (t,theta))) :=
        fun t => (average_hasDerivAt hF t).differentiableAt
      exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
      change ContDiff ℝ ((n : WithTop ℕ∞)+1) _
      apply contDiff_succ_iff_deriv.mpr
      refine ⟨fun t => (average_hasDerivAt hF t).differentiableAt, by simp, ?_⟩
      have he : deriv (fun t => average (fun theta => F (t,theta))) =
          fun t => average (fun theta => radialPartial F (t,theta)) :=
        funext fun t => (average_hasDerivAt hF t).deriv
      rw [he]
      exact ih (partial_smooth hF)

theorem average_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    average (fun t => f t + g t) = average f + average g := by
  rw [average, integral_add (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self), mul_add]
  rfl

theorem average_const_mul (c : ℂ) (f : ℝ → ℂ) :
    average (fun t => c * f t) = c * average f := by
  rw [average, integral_const_mul]
  change _ = c * ((1/(2*Real.pi:ℂ)) * _)
  ring

theorem average_const (c : ℂ) : average (fun _ => c) = c := by
  have hT : 0 ≤ 2 * Real.pi := by positivity
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [average, ← intervalIntegral.integral_of_le hT]
  simp only [intervalIntegral.integral_const, sub_zero, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp [hp]

theorem average_periodic_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, f (t + 2*Real.pi) = f t) : average (deriv f) = 0 := by
  have hT : 0 ≤ 2 * Real.pi := by positivity
  have h := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    ((hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).contDiffOn) hT
  rw [intervalIntegral.integral_of_le hT] at h
  rw [average, h, show f (2*Real.pi) = f 0 by simpa using hp 0, sub_self, mul_zero]

theorem periodic_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, f (t + 2*Real.pi) = f t) (t : ℝ) :
    deriv f (t + 2*Real.pi) = deriv f t := by
  have h := (hf.differentiable (by simp) (t + 2*Real.pi)).hasDerivAt.scomp t
    ((hasDerivAt_id t).add_const (2*Real.pi))
  have he : (fun r => f (r + 2*Real.pi)) = f := funext hp
  simpa only [Function.comp_def, id_eq, one_smul, he] using h.deriv.symm

end
end GaloisForLFunctions.HTGeometry.SmoothAngularAverage
