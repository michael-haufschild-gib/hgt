import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import GaloisForLFunctions.RHTower.SlepianSmoothKernel

/-!
# The Slepian commuting theorem on the band

The time–band transform `T̃f(x) = ∫_{−1}^{1} K̃_c(x,y)·f(y) dy` built on the entire sinc kernel
commutes with the prolate Sturm–Liouville operator:

`P_c (T̃ f) = T̃ (P_c f)` pointwise on `ℝ`  (`slepian_commutation`).

The derivative of the transform passes under the integral sign (dominated differentiation on
the band, with the compactly-bounded smooth kernel supplying its own dominating constant), so
`P_c(T̃f)(x) = ∫ (P_c K̃(·,y))(x)·f(y) dy`, and the Slepian transfer identity moves the action
onto `f`.  Consequently every pointwise eigenfunction of the prolate operator is mapped by the
transform to an eigenfunction with the same eigenvalue (`slepian_commutation_eigen`): the
transform preserves each prolate eigenline, which is the mechanism identifying concentration
eigenfunctions with prolate ODE eigenfunctions.
-/

open Filter MeasureTheory intervalIntegral

namespace RHTower

theorem differentiable_sincSmooth (c : ℝ) : Differentiable ℝ (sincSmooth c) :=
  (contDiff_infty_iff_deriv.mp (contDiff_sincSmooth c)).1

theorem contDiff_deriv_sincSmooth (c : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (sincSmooth c)) :=
  (contDiff_infty_iff_deriv.mp (contDiff_sincSmooth c)).2

theorem differentiable_deriv_sincSmooth (c : ℝ) : Differentiable ℝ (deriv (sincSmooth c)) :=
  (contDiff_infty_iff_deriv.mp (contDiff_deriv_sincSmooth c)).1

theorem continuous_deriv2_sincSmooth (c : ℝ) :
    Continuous (deriv (deriv (sincSmooth c))) :=
  ((contDiff_infty_iff_deriv.mp (contDiff_deriv_sincSmooth c)).2).continuous

theorem deriv_sincKernelSmooth_fst (c y x : ℝ) :
    deriv (fun t => sincKernelSmooth c t y) x = deriv (sincSmooth c) (x - y) :=
  deriv_comp_sub_const (sincSmooth c) y x

theorem deriv2_sincKernelSmooth_fst (c y x : ℝ) :
    deriv (deriv (fun t => sincKernelSmooth c t y)) x
      = deriv (deriv (sincSmooth c)) (x - y) := by
  have hfun : deriv (fun t => sincKernelSmooth c t y)
      = fun t => deriv (sincSmooth c) (t - y) :=
    funext fun t => deriv_comp_sub_const (sincSmooth c) y t
  rw [hfun]
  exact deriv_comp_sub_const (deriv (sincSmooth c)) y x

/-- Differentiation under the band integral for a translation kernel with `C¹` profile:
`d/dx ∫ g(x−y)·f(y) dy = ∫ g'(x−y)·f(y) dy`.  The dominating bound is the supremum of `g'` on
a compact window, available by continuity. -/
theorem hasDerivAt_bandTranslationTransform {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (hg' : Continuous (deriv g)) {f : ℝ → ℝ} (hf : Continuous f) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ y in (-1 : ℝ)..1, g (x - y) * f y)
      (∫ y in (-1 : ℝ)..1, deriv g (x₀ - y) * f y) x₀ := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ 2).exists_bound_of_continuousOn hg'.continuousOn
  have harg : ∀ x ∈ Metric.ball x₀ 1, ∀ t ∈ Set.uIoc (-1 : ℝ) 1,
      x - t ∈ Metric.closedBall x₀ 2 := by
    intro x hx t ht
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    rw [Metric.mem_ball, Real.dist_eq] at hx
    rw [Metric.mem_closedBall, Real.dist_eq,
      show x - t - x₀ = (x - x₀) + -t by ring]
    have h1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
    calc |(x - x₀) + -t| ≤ |x - x₀| + |(-t)| := abs_add_le _ _
      _ ≤ 1 + 1 := by rw [abs_neg]; exact add_le_add hx.le h1
      _ = 2 := by norm_num
  have hmeas : ∀ᶠ x in nhds x₀, AEStronglyMeasurable (fun y => g (x - y) * f y)
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) :=
    Eventually.of_forall fun x =>
      ((hg.continuous.comp (continuous_const.sub continuous_id)).mul hf).aestronglyMeasurable
  have hint : IntervalIntegrable (fun y => g (x₀ - y) * f y) volume (-1) 1 :=
    ((hg.continuous.comp (continuous_const.sub continuous_id)).mul hf).intervalIntegrable _ _
  have hmeas' : AEStronglyMeasurable (fun y => deriv g (x₀ - y) * f y)
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) :=
    ((hg'.comp (continuous_const.sub continuous_id)).mul hf).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ x ∈ Metric.ball x₀ 1,
      ‖deriv g (x - t) * f t‖ ≤ |M| * |f t| := by
    refine Eventually.of_forall fun t ht x hx => ?_
    have hb : |deriv g (x - t)| ≤ |M| := by
      rw [← Real.norm_eq_abs]
      exact (hM _ (harg x hx t ht)).trans (le_abs_self M)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hbint : IntervalIntegrable (fun t => |M| * |f t|) volume (-1) 1 :=
    (continuous_const.mul hf.abs).intervalIntegrable _ _
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ x ∈ Metric.ball x₀ 1,
      HasDerivAt (fun x' => g (x' - t) * f t) (deriv g (x - t) * f t) x := by
    refine Eventually.of_forall fun t _ x _ => ?_
    have h0 := ((hg (x - t)).hasDerivAt).comp x ((hasDerivAt_id x).sub_const t)
    simpa using h0.mul_const (f t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x₀ one_pos) hmeas hint hmeas' hbound hbint hdiff).2

/-- The time–band transform with the entire sinc kernel. -/
noncomputable def bandTransform (c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * f y

theorem hasDerivAt_bandTransform (c : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (x₀ : ℝ) :
    HasDerivAt (bandTransform c f)
      (∫ y in (-1 : ℝ)..1, deriv (sincSmooth c) (x₀ - y) * f y) x₀ :=
  hasDerivAt_bandTranslationTransform (differentiable_sincSmooth c)
    ((contDiff_deriv_sincSmooth c).continuous) hf x₀

theorem deriv_bandTransform (c : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    deriv (bandTransform c f)
      = fun x => ∫ y in (-1 : ℝ)..1, deriv (sincSmooth c) (x - y) * f y :=
  funext fun x => (hasDerivAt_bandTransform c hf x).deriv

theorem deriv2_bandTransform (c : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    deriv (deriv (bandTransform c f)) x
      = ∫ y in (-1 : ℝ)..1, deriv (deriv (sincSmooth c)) (x - y) * f y := by
  rw [deriv_bandTransform c hf]
  exact (hasDerivAt_bandTranslationTransform (differentiable_deriv_sincSmooth c)
    (continuous_deriv2_sincSmooth c) hf x).deriv

/-- The prolate action passes under the band integral: `P_c(T̃f)(x)` is the integral of the
prolate action of the kernel's outer-variable slice against `f`. -/
theorem prolateSLAction_bandTransform (c : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    prolateSLAction c (bandTransform c f) x
      = ∫ y in (-1 : ℝ)..1, prolateSLAction c (fun t => sincKernelSmooth c t y) x * f y := by
  have hK : Continuous (fun y => sincKernelSmooth c x y * f y) :=
    (((contDiff_sincSmooth c).continuous.comp (continuous_const.sub continuous_id)).mul hf)
  have hK1 : Continuous (fun y => deriv (sincSmooth c) (x - y) * f y) :=
    (((contDiff_deriv_sincSmooth c).continuous.comp (continuous_const.sub continuous_id)).mul hf)
  have hK2 : Continuous (fun y => deriv (deriv (sincSmooth c)) (x - y) * f y) :=
    (((continuous_deriv2_sincSmooth c).comp (continuous_const.sub continuous_id)).mul hf)
  have hIA : IntervalIntegrable
      (fun y => (1 - x ^ (2 : ℕ)) * (deriv (deriv (sincSmooth c)) (x - y) * f y)) volume (-1) 1 :=
    (hK2.intervalIntegrable _ _).const_mul _
  have hIB : IntervalIntegrable
      (fun y => 2 * x * (deriv (sincSmooth c) (x - y) * f y)) volume (-1) 1 :=
    (hK1.intervalIntegrable _ _).const_mul _
  have hIC : IntervalIntegrable
      (fun y => c ^ (2 : ℕ) * x ^ (2 : ℕ) * (sincKernelSmooth c x y * f y)) volume (-1) 1 :=
    (hK.intervalIntegrable _ _).const_mul _
  simp only [prolateSLAction]
  rw [deriv2_bandTransform c hf, deriv_bandTransform c hf]
  simp only [bandTransform]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hIA hIB, ← intervalIntegral.integral_sub (hIA.sub hIB) hIC]
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [deriv_sincKernelSmooth_fst, deriv2_sincKernelSmooth_fst]
  ring

/-- **Slepian commuting theorem on the band.**  The prolate Sturm–Liouville operator commutes
with the time–band transform: `P_c(T̃f) = T̃(P_c f)` pointwise, for twice differentiable `f`
with continuous second derivative. -/
theorem slepian_commutation (c x : ℝ) {f : ℝ → ℝ}
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hf2c : Continuous (deriv (deriv f))) :
    prolateSLAction c (bandTransform c f) x
      = ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * prolateSLAction c f y := by
  rw [prolateSLAction_bandTransform c hf1.continuous x]
  exact (slepian_transfer c x hf1 hf2 hf2c).symm

/-- **Eigenline preservation.**  A pointwise eigenfunction of the prolate operator transforms
to an eigenfunction with the same eigenvalue: `P_c ψ = χ·ψ` implies
`P_c(T̃ψ) = χ·(T̃ψ)`.  The band transform preserves every prolate eigenline — the mechanism
identifying time–band concentration eigenfunctions with prolate ODE eigenfunctions. -/
theorem slepian_commutation_eigen (c x : ℝ) {ψ : ℝ → ℝ} {χ : ℝ}
    (hf1 : Differentiable ℝ ψ) (hf2 : Differentiable ℝ (deriv ψ))
    (hf2c : Continuous (deriv (deriv ψ)))
    (heig : ∀ y, prolateSLAction c ψ y = χ * ψ y) :
    prolateSLAction c (bandTransform c ψ) x = χ * bandTransform c ψ x := by
  have hcongr : ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * prolateSLAction c ψ y
      = ∫ y in (-1 : ℝ)..1, χ * (sincKernelSmooth c x y * ψ y) :=
    intervalIntegral.integral_congr fun y _ => by rw [heig y]; ring
  rw [slepian_commutation c x hf1 hf2 hf2c, hcongr, intervalIntegral.integral_const_mul]
  rfl

end RHTower
