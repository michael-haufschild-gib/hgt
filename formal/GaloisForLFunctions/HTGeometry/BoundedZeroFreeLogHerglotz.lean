import GaloisForLFunctions.HTGeometry.BallLogarithm
import GaloisForLFunctions.HTGeometry.BoundedRealHerglotz
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.HTGeometry.DiskMultiplierBoundary
import GaloisForLFunctions.HTGeometry.HerglotzRepresentationDisc

/-!
# Herglotz representation of a bounded zero-free analytic logarithm

A nonzero bounded analytic function with no disk zeros has a normalized analytic logarithm.  Its
real part is bounded above, though generally not below: singular inner factors are exactly why a
two-sided bound is unavailable.  Subtracting that logarithm from a positive constant produces a
normalized Carathéodory function, hence a genuine probability-measure Herglotz representation.

This is the factorization interface needed to keep singular inner phase separate from outer
Hilbert phase; no invertibility or lower modulus hypothesis is introduced.
-/

open Complex Metric MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Complex Herglotz transform of a probability measure -/

/-- Complex Herglotz transform of a circle probability measure. -/
def circleMeasureHerglotz (μ : ProbabilityMeasure Circle) (w : ℂ) : ℂ :=
  ∫ ζ : Circle, circleHerglotzKernel w ζ ∂(μ : Measure Circle)

private theorem norm_circleHerglotzKernel_le_of_norm_le
    {w : ℂ} {ρ : ℝ} (hρ : ρ < 1) (hw : ‖w‖ ≤ ρ) (ζ : Circle) :
    ‖circleHerglotzKernel w ζ‖ ≤ (1 + ρ) / (1 - ρ) := by
  rw [circleHerglotzKernel, norm_div]
  have hnum : ‖(ζ : ℂ) + w‖ ≤ 1 + ρ := by
    calc
      ‖(ζ : ℂ) + w‖ ≤ ‖(ζ : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 1 + ρ := by rw [Circle.norm_coe]; linarith
  have hden : 1 - ρ ≤ ‖(ζ : ℂ) - w‖ := by
    calc
      1 - ρ ≤ ‖(ζ : ℂ)‖ - ‖w‖ := by rw [Circle.norm_coe]; linarith
      _ ≤ ‖(ζ : ℂ) - w‖ := norm_sub_norm_le _ _
  exact div_le_div₀ (by linarith [norm_nonneg w, hw]) hnum (sub_pos.mpr hρ) hden

theorem differentiableOn_circleMeasureHerglotz
    (μ : ProbabilityMeasure Circle) :
    DifferentiableOn ℂ (circleMeasureHerglotz μ) (ball (0 : ℂ) 1) := by
  intro z hz
  rw [mem_ball, dist_zero_right] at hz
  let R : ℝ := (1 - ‖z‖) / 2
  let ρ : ℝ := (1 + ‖z‖) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hρ : ρ < 1 := by dsimp [ρ]; linarith
  have hnorm : ∀ w ∈ ball z R, ‖w‖ ≤ ρ := by
    intro w hw
    calc
      ‖w‖ = dist w 0 := by rw [dist_zero_right]
      _ ≤ dist w z + dist z 0 := dist_triangle w z 0
      _ ≤ R + ‖z‖ := by
        rw [dist_zero_right]
        exact add_le_add (Metric.mem_ball.mp hw).le le_rfl
      _ = ρ := by dsimp [R, ρ]; ring
  have hmeas : ∀ w ∈ ball z R,
      AEStronglyMeasurable (fun ζ : Circle => circleHerglotzKernel w ζ)
        (μ : Measure Circle) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := lt_of_le_of_lt (hnorm w hw) hρ
    have hne : ∀ ζ : Circle, (ζ : ℂ) - w ≠ 0 := by
      intro ζ heq
      have hzw : (ζ : ℂ) = w := sub_eq_zero.mp heq
      rw [← hzw, Circle.norm_coe] at hw1
      exact (lt_irrefl 1) hw1
    apply Continuous.aestronglyMeasurable
    unfold circleHerglotzKernel
    fun_prop (disch := exact hne _)
  have hdiff : ∀ ζ : Circle,
      DifferentiableOn ℂ (fun w => circleHerglotzKernel w ζ) (ball z R) := by
    intro ζ w hw
    have hw1 : ‖w‖ < 1 := lt_of_le_of_lt (hnorm w hw) hρ
    have hne : (ζ : ℂ) - w ≠ 0 := by
      intro heq
      have hzw : (ζ : ℂ) = w := sub_eq_zero.mp heq
      rw [← hzw, Circle.norm_coe] at hw1
      exact (lt_irrefl 1) hw1
    unfold circleHerglotzKernel
    fun_prop (disch := exact hne)
  have hbound : ∀ ζ : Circle, ∀ w ∈ ball z R,
      ‖circleHerglotzKernel w ζ‖ ≤ (1 + ρ) / (1 - ρ) :=
    fun ζ w hw => norm_circleHerglotzKernel_le_of_norm_le hρ (hnorm w hw) ζ
  have hboundInt : Integrable (fun _ζ : Circle => (1 + ρ) / (1 - ρ))
      (μ : Measure Circle) := integrable_const _
  change DifferentiableWithinAt ℂ (circleMeasureHerglotz μ) (ball 0 1) z
  apply DifferentiableAt.differentiableWithinAt
  unfold circleMeasureHerglotz
  exact differentiableAt_integral_of_cauchy_dominated hR hmeas hdiff hbound hboundInt

@[simp] theorem circleMeasureHerglotz_zero
    (μ : ProbabilityMeasure Circle) : circleMeasureHerglotz μ 0 = 1 := by
  rw [circleMeasureHerglotz]
  have hpoint : ∀ ζ : Circle, circleHerglotzKernel 0 ζ = 1 := by
    intro ζ
    rw [circleHerglotzKernel]
    have hz : (ζ : ℂ) ≠ 0 := by simp
    field_simp
    ring
  simp_rw [hpoint]
  simp

theorem circleMeasureHerglotz_re
    (μ : ProbabilityMeasure Circle) {w : ℂ} (hw : ‖w‖ < 1) :
    (circleMeasureHerglotz μ w).re =
      ∫ ζ : Circle, _root_.poissonKernel 0 w (ζ : ℂ) ∂(μ : Measure Circle) := by
  have hcont : Continuous fun ζ : Circle => circleHerglotzKernel w ζ := by
    have hne : ∀ ζ : Circle, (ζ : ℂ) - w ≠ 0 := by
      intro ζ heq
      have hzw : (ζ : ℂ) = w := sub_eq_zero.mp heq
      rw [← hzw, Circle.norm_coe] at hw
      exact (lt_irrefl 1) hw
    unfold circleHerglotzKernel
    fun_prop (disch := exact hne _)
  have hint : Integrable (fun ζ : Circle => circleHerglotzKernel w ζ)
      (μ : Measure Circle) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [circleMeasureHerglotz]
  change Complex.reCLM
      (∫ ζ : Circle, circleHerglotzKernel w ζ ∂(μ : Measure Circle)) = _
  rw [← Complex.reCLM.integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards with ζ
  exact circleHerglotzKernel_re hw ζ

/-- A bounded zero-free multiplier admits a normalized analytic logarithm whose real part has a
global upper bound. -/
theorem exists_upperBounded_log
    (φ : DiskMultiplier)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0) :
    ∃ g : ℂ → ℂ, ∃ C : ℝ,
      DifferentiableOn ℂ g (ball 0 1) ∧ g 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) 1,
        φ.fn z = φ.fn 0 * Complex.exp (g z)) ∧
      0 ≤ C ∧ ∀ z ∈ ball (0 : ℂ) 1, (g z).re ≤ C := by
  obtain ⟨g, hg, hg0, hgeq⟩ := exists_log_on_ball (by norm_num) φ.diff hne
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hφ0 : φ.fn 0 ≠ 0 := hne 0 h0mem
  have hφ0pos : 0 < ‖φ.fn 0‖ := norm_pos_iff.mpr hφ0
  have hbdpos : 0 < φ.bd := lt_of_lt_of_le hφ0pos (φ.bd_le 0 h0mem)
  let C : ℝ := Real.log (φ.bd / ‖φ.fn 0‖)
  have hratioOne : 1 ≤ φ.bd / ‖φ.fn 0‖ := by
    rw [le_div_iff₀ hφ0pos]
    simpa using φ.bd_le 0 h0mem
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Real.log_nonneg hratioOne
  refine ⟨g, C, hg, hg0, hgeq, hC, ?_⟩
  intro z hz
  have hmod := congrArg norm (hgeq z hz)
  rw [norm_mul, Complex.norm_exp] at hmod
  have hexp : Real.exp (g z).re = ‖φ.fn z‖ / ‖φ.fn 0‖ := by
    rw [eq_div_iff hφ0pos.ne']
    simpa [mul_comm] using hmod.symm
  have hratioPos : 0 < ‖φ.fn z‖ / ‖φ.fn 0‖ :=
    div_pos (norm_pos_iff.mpr (hne z hz)) hφ0pos
  have hre : (g z).re = Real.log (‖φ.fn z‖ / ‖φ.fn 0‖) := by
    rw [← hexp, Real.log_exp]
  rw [hre]
  dsimp [C]
  exact Real.log_le_log hratioPos
    (div_le_div_of_nonneg_right (φ.bd_le z hz) hφ0pos.le)

/-- Normalized analytic logarithm of a bounded zero-free disk multiplier. -/
structure BoundedZeroFreeLog (φ : DiskMultiplier) where
  fn : ℂ → ℂ
  bound : ℝ
  diff : DifferentiableOn ℂ fn (ball 0 1)
  zero : fn 0 = 0
  center_ne_zero : φ.fn 0 ≠ 0
  exp_eq : ∀ z ∈ ball (0 : ℂ) 1,
    φ.fn z = φ.fn 0 * Complex.exp (fn z)
  bound_nonneg : 0 ≤ bound
  re_le : ∀ z ∈ ball (0 : ℂ) 1, (fn z).re ≤ bound

/-- Choose the normalized logarithm of a bounded multiplier known to be zero-free. -/
noncomputable def BoundedZeroFreeLog.ofZeroFree
    (φ : DiskMultiplier)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0) :
    BoundedZeroFreeLog φ :=
  Classical.choice (by
    obtain ⟨g, C, hg, hg0, hgeq, hC, hupper⟩ :=
      exists_upperBounded_log φ hne
    exact ⟨⟨g, C, hg, hg0, hne 0 (by simp), hgeq, hC, hupper⟩⟩)

/-- Positive normalization constant used in the Carathéodory transform. -/
def BoundedZeroFreeLog.scale {φ : DiskMultiplier}
    (L : BoundedZeroFreeLog φ) : ℝ := L.bound + 1

theorem BoundedZeroFreeLog.scale_pos {φ : DiskMultiplier}
    (L : BoundedZeroFreeLog φ) : 0 < L.scale := by
  rw [BoundedZeroFreeLog.scale]
  linarith [L.bound_nonneg]

/-- Normalized Carathéodory function attached to the upper-bounded logarithm. -/
def BoundedZeroFreeLog.caratheodoryFn {φ : DiskMultiplier}
    (L : BoundedZeroFreeLog φ) (z : ℂ) : ℂ :=
  ((L.scale : ℝ) : ℂ)⁻¹ * (((L.scale : ℝ) : ℂ) - L.fn z)

theorem BoundedZeroFreeLog.caratheodoryFn_diff
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) :
    DifferentiableOn ℂ L.caratheodoryFn (ball (0 : ℂ) 1) := by
  unfold BoundedZeroFreeLog.caratheodoryFn
  intro z hz
  exact (differentiableWithinAt_const ((L.scale : ℂ)⁻¹)).mul
    ((differentiableWithinAt_const (L.scale : ℂ)).sub (L.diff z hz))

@[simp] theorem BoundedZeroFreeLog.caratheodoryFn_zero
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) :
    L.caratheodoryFn 0 = 1 := by
  rw [BoundedZeroFreeLog.caratheodoryFn, L.zero]
  have hs : (((L.scale : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast L.scale_pos.ne'
  field_simp
  ring

theorem BoundedZeroFreeLog.caratheodoryFn_re_nonneg
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    0 ≤ (L.caratheodoryFn z).re := by
  have hre : (L.caratheodoryFn z).re =
      (L.scale - (L.fn z).re) / L.scale := by
    rw [BoundedZeroFreeLog.caratheodoryFn, Complex.mul_re]
    norm_num [Complex.inv_re, Complex.inv_im, Complex.normSq_ofReal]
    field_simp [L.scale_pos.ne']
  rw [hre]
  apply div_nonneg _ L.scale_pos.le
  rw [sub_nonneg]
  dsimp [BoundedZeroFreeLog.scale]
  linarith [L.re_le z hz]

/-- Exact reconstruction of the logarithm from its Carathéodory function. -/
theorem BoundedZeroFreeLog.fn_eq_scale_mul_one_sub_caratheodoryFn
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) (z : ℂ) :
    L.fn z = (L.scale : ℂ) * (1 - L.caratheodoryFn z) := by
  rw [BoundedZeroFreeLog.caratheodoryFn]
  have hs : (L.scale : ℂ) ≠ 0 := by exact_mod_cast L.scale_pos.ne'
  field_simp
  ring

/-- Herglotz probability measure representing the real part of a bounded zero-free logarithm's
normalized Carathéodory transform. -/
theorem BoundedZeroFreeLog.exists_herglotzMeasure
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) :
    ∃ μ : ProbabilityMeasure Circle, ∀ w ∈ ball (0 : ℂ) 1,
      (L.caratheodoryFn w).re =
        ∫ ζ : Circle, _root_.poissonKernel 0 w (ζ : ℂ) ∂(μ : Measure Circle) :=
  exists_herglotz_representation L.caratheodoryFn_diff
    (fun _z hz => L.caratheodoryFn_re_nonneg hz) L.caratheodoryFn_zero

/-- Complex Herglotz representation, with imaginary constant fixed by normalization at the
origin. -/
theorem BoundedZeroFreeLog.exists_herglotzMeasure_complex
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) :
    ∃ μ : ProbabilityMeasure Circle, ∀ w ∈ ball (0 : ℂ) 1,
      L.caratheodoryFn w = circleMeasureHerglotz μ w := by
  obtain ⟨μ, hμ⟩ := L.exists_herglotzMeasure
  refine ⟨μ, ?_⟩
  let D : ℂ → ℂ := fun w => L.caratheodoryFn w - circleMeasureHerglotz μ w
  have hDdiff : DifferentiableOn ℂ D (ball (0 : ℂ) 1) :=
    L.caratheodoryFn_diff.sub (differentiableOn_circleMeasureHerglotz μ)
  have hDanalytic : AnalyticOnNhd ℂ D (ball (0 : ℂ) 1) :=
    hDdiff.analyticOnNhd isOpen_ball
  have hDre : ∀ w ∈ ball (0 : ℂ) 1, (D w).re = 0 := by
    intro w hw
    dsimp [D]
    rw [hμ w hw, circleMeasureHerglotz_re]
    · ring
    · simpa [mem_ball, dist_zero_right] using hw
  obtain ⟨k, hk⟩ := hDanalytic.eq_const_of_re_eq_const hDre isOpen_ball
    ⟨⟨0, mem_ball_self zero_lt_one⟩, (convex_ball (0 : ℂ) 1).isPreconnected⟩
  have hkzero : k = 0 := by
    have h0 := hk 0 (mem_ball_self zero_lt_one)
    dsimp [D] at h0
    simpa using h0.symm
  intro w hw
  have h := hk w hw
  dsimp [D] at h
  rw [hkzero] at h
  exact sub_eq_zero.mp h

end GaloisForLFunctions.HTGeometry
