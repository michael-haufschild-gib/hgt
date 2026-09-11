import GaloisForLFunctions.HTGeometry.FirstEndpointMellin
import GaloisForLFunctions.HTGeometry.SimplePoleResidueValue

/-!
# Laurent extraction through the first-endpoint Mellin finite part

Under the uniform horizon Lipschitz bound of `firstEndpointMellinRemainder_differentiableAt`, the
complete first-endpoint Mellin finite part, endpoint counterterm included, is holomorphic in the
frequency and hence analytic on a ball.  Consequently, for a density `F u t / (u - w)` whose
numerator is uniformly controlled at the horizon, the order `-1` Laurent coefficient of its
finite part at `w` is the finite part of the residue density `F w`: residue extraction commutes
with the horizon finite part.  This is the abstract interchange behind the HB radial residue; it
evaluates no physical current.
-/

namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology MeasureTheory Set Metric
noncomputable section
set_option autoImplicit false

/-- The full first-endpoint Mellin finite part is holomorphic in the frequency. -/
theorem firstEndpointMellin_differentiableAt
    {F : ℂ → ℝ → ℂ} {w : ℂ} {b R C β : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hR : 0 < R) (hC0 : 0 ≤ C) (hβ : -2 < β)
    (hreal : ∀ u ∈ ball w R, β ≤ u.re)
    (hm : ∀ u ∈ ball w R, Measurable (F u))
    (hd : ∀ t ∈ Icc (0:ℝ) b, ∀ u ∈ ball w R, DifferentiableAt ℂ (fun v => F v t) u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t - F u 0‖ ≤ C * t)
    (hw1 : w + 1 ≠ 0) :
    DifferentiableAt ℂ (firstEndpointMellin F b) w := by
  have hrem := firstEndpointMellinRemainder_differentiableAt hb.le hb1 hR hC0 hβ hreal hm hd hC
  have hF0 : DifferentiableAt ℂ (fun v => F v 0) w := hd 0 ⟨le_rfl, hb.le⟩ w (mem_ball_self hR)
  have hpow : DifferentiableAt ℂ (fun v : ℂ => (b:ℂ) ^ (v + 1)) w :=
    (differentiableAt_id.add_const 1).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne'))
  have hlin : DifferentiableAt ℂ (fun v : ℂ => v + 1) w := differentiableAt_id.add_const 1
  have h1 : DifferentiableAt ℂ (fun v => F v 0 * (b:ℂ) ^ (v + 1) / (v + 1)) w :=
    (hF0.mul hpow).div hlin hw1
  show DifferentiableAt ℂ
    (fun v => F v 0 * (b:ℂ) ^ (v + 1) / (v + 1) + firstEndpointMellinRemainder F b v) w
  exact h1.add hrem

/-- Under uniform bounds on a ball avoiding `-1`, the finite part is analytic at the centre. -/
theorem firstEndpointMellin_analyticAt
    {F : ℂ → ℝ → ℂ} {w : ℂ} {b R C β : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hR : 0 < R) (hC0 : 0 ≤ C) (hβ : -2 < β)
    (hreal : ∀ u ∈ ball w R, β ≤ u.re)
    (hm : ∀ u ∈ ball w R, Measurable (F u))
    (hd : ∀ t ∈ Icc (0:ℝ) b, ∀ u ∈ ball w R, DifferentiableAt ℂ (fun v => F v t) u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t - F u 0‖ ≤ C * t)
    (hw1 : ∀ u ∈ ball w R, u + 1 ≠ 0) :
    AnalyticAt ℂ (firstEndpointMellin F b) w := by
  have hdiff : DifferentiableOn ℂ (firstEndpointMellin F b) (ball w (R / 2)) := by
    intro u hu
    have hsub : ball u (R / 2) ⊆ ball w R := by
      apply ball_subset_ball'
      have := mem_ball.mp hu
      linarith
    exact (firstEndpointMellin_differentiableAt hb hb1 (half_pos hR) hC0 hβ
      (fun v hv => hreal v (hsub hv)) (fun v hv => hm v (hsub hv))
      (fun t ht v hv => hd t ht v (hsub hv)) (fun v hv t ht => hC v (hsub hv) t ht)
      (hw1 u (ball_subset_ball (by linarith) hu))).differentiableWithinAt
  exact hdiff.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hR)))

/-- A frequency-dependent scalar factor passes through the finite part. -/
theorem firstEndpointMellin_const_mul (c : ℂ → ℂ) (F : ℂ → ℝ → ℂ) (b : ℝ) (w : ℂ) :
    firstEndpointMellin (fun u t => c u * F u t) b w = c w * firstEndpointMellin F b w := by
  unfold firstEndpointMellin firstEndpointMellinRemainder
  rw [mul_add, ← MeasureTheory.integral_const_mul]
  congr 1
  · ring
  · refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    ring

/-- The finite part of a simple-pole density is the simple-pole scaling of the finite part. -/
theorem firstEndpointMellin_div_sub (F : ℂ → ℝ → ℂ) (b : ℝ) (w₀ u : ℂ) :
    firstEndpointMellin (fun v t => F v t / (v - w₀)) b u =
      firstEndpointMellin F b u / (u - w₀) := by
  have he : (fun v t => F v t / (v - w₀)) = fun v t => (1 / (v - w₀)) * F v t := by
    funext v t
    ring
  rw [he, firstEndpointMellin_const_mul]
  ring

/-- Residue extraction commutes with the horizon finite part: the order `-1` Laurent coefficient
at `w` of the finite part of `F u t / (u - w)` is the finite part of the residue density `F w`. -/
theorem laurentCoeff_firstEndpointMellin_div_sub
    {F : ℂ → ℝ → ℂ} {w : ℂ} {b R C β : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hR : 0 < R) (hC0 : 0 ≤ C) (hβ : -2 < β)
    (hreal : ∀ u ∈ ball w R, β ≤ u.re)
    (hm : ∀ u ∈ ball w R, Measurable (F u))
    (hd : ∀ t ∈ Icc (0:ℝ) b, ∀ u ∈ ball w R, DifferentiableAt ℂ (fun v => F v t) u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t - F u 0‖ ≤ C * t)
    (hw1 : ∀ u ∈ ball w R, u + 1 ≠ 0) :
    laurentCoeff (fun u => firstEndpointMellin (fun v t => F v t / (v - w)) b u) w (-1) =
      firstEndpointMellin F b w := by
  have he : (fun u => firstEndpointMellin (fun v t => F v t / (v - w)) b u) =
      fun u => firstEndpointMellin F b u / (u - w) := by
    funext u
    exact firstEndpointMellin_div_sub F b w u
  rw [he]
  exact laurentCoeff_analytic_div_sub
    (firstEndpointMellin_analyticAt hb hb1 hR hC0 hβ hreal hm hd hC hw1)

end
end GaloisForLFunctions.HTGeometry
