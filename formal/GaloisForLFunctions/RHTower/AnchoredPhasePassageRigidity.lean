import GaloisForLFunctions.RHTower.GaussianEulerContinuumRelativeFormation
import GaloisForLFunctions.HTGeometry.VitaliConvergence
import GaloisForLFunctions.HTGeometry.BallLogarithm


/-!
# Anchored phase-passage rigidity: holomorphic passages cannot lose degree at finite energy

Route 1 (`docs/reports/route-proposals/route1.md`) asks for weak `H^(1/2)` convergence of the
zero-free Gaussian Euler–continuum phases `Φₓ/|Φₓ|` through the passage `x → 0⁺`, and then for a
sub-unit bound `κ₋ < 1` on the negative-chirality Hankel energy lost there.  This file shows that
the second input is idle.

* `schwarz_difference_formula`: for `G` holomorphic near `closedBall c r`, the increment `G z - G z₁`
  is `(i/π)∫ K (Im G - m) dθ` over `C(c,r)`, with an explicit kernel `K` and any real `m`.  The
  anti-holomorphic half is killed by Cauchy's theorem applied to the reflected integrand.
* `norm_sub_le_of_boundary_im_oscillation`: hence
  `‖G z - G z₁‖ ≤ r‖z-z₁‖ / (π(r-‖z-c‖)(r-‖z₁-c‖)) · ∫|Im G - m|`.
* `ne_zero_of_anchored_boundaryArgOscillation_bounded`: let the zero-free approximants `exp ∘ G k`
  converge to `f` on an open anchor where `f ≢ 0`, with boundary arguments bounded in `L¹` modulo
  constants.  Then `f` is zero-free in the whole disc (Vitali, plus the lower bound
  `|exp(G k z - G k z₁)| ≥ exp(-bound)`).
* `riemannHypothesis_of_gaussianPassage_boundaryArgOscillation_bounded`: on circles `C(1+iγ,r)`,
  bounded boundary argument of the Gaussian potential `Lₓ + Aₓ` along one sequence `x_k → 0⁺`
  implies RH.

By Bourgain–Brezis–Mironescu, bounded `H^(1/2)(S¹;S¹)` phase energy gives the `L¹` lift bound used
here.  So along anchored holomorphic passages the chiral losses always balance (`κ₋ = κ₊`).
Degree is never lost at finite energy, and the budget `B_base` cannot enter.  Route 1 therefore
reduces to boundedness of the passage itself, which the Gaussian explicit formula shows is
equivalent to RH.  This is a reduction and a no-go for the route, not a proof of its hypothesis.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-- Schwarz difference kernel on `C(c,r)`: `w(z-z₁)/((ζ-z)(ζ-z₁))` with `ζ=c+w`. -/
def schwarzDifferenceKernel (c z z₁ : ℂ) (r θ : ℝ) : ℂ :=
  circleMap 0 r θ * (z - z₁) / ((circleMap c r θ - z) * (circleMap c r θ - z₁))

private theorem circleMap_sub_ne {c z : ℂ} {r : ℝ} (hz : z ∈ ball c r) (θ : ℝ) :
    circleMap c r θ - z ≠ 0 := by
  intro h
  have hr : 0 ≤ r := le_trans dist_nonneg (le_of_lt hz)
  have hmem : circleMap c r θ ∈ sphere c r := circleMap_mem_sphere c hr θ
  rw [sub_eq_zero.mp h] at hmem
  exact (ne_of_lt (mem_ball.mp hz)) (mem_sphere.mp hmem)

private theorem norm_circleMap_sub_ge {c z : ℂ} {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    r - ‖z - c‖ ≤ ‖circleMap c r θ - z‖ := by
  have h1 : ‖circleMap c r θ - c‖ = r := by
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hr]
  have h2 : ‖circleMap c r θ - c‖ ≤ ‖circleMap c r θ - z‖ + ‖z - c‖ := by
    calc ‖circleMap c r θ - c‖ = ‖(circleMap c r θ - z) + (z - c)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  linarith

private theorem continuous_schwarzDifferenceKernel {c z z₁ : ℂ} {r : ℝ}
    (hz : z ∈ ball c r) (hz₁ : z₁ ∈ ball c r) :
    Continuous (schwarzDifferenceKernel c z z₁ r) := by
  unfold schwarzDifferenceKernel
  refine Continuous.div ((continuous_circleMap 0 r).mul continuous_const)
    (((continuous_circleMap c r).sub continuous_const).mul
      ((continuous_circleMap c r).sub continuous_const)) ?_
  intro θ
  exact mul_ne_zero (circleMap_sub_ne hz θ) (circleMap_sub_ne hz₁ θ)

private theorem continuous_comp_circleMap {G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hG : ContinuousOn G (closedBall c r)) :
    Continuous (fun θ : ℝ => G (circleMap c r θ)) :=
  hG.comp_continuous (continuous_circleMap c r)
    (fun θ => sphere_subset_closedBall (circleMap_mem_sphere c hr θ))

/-- **Cauchy difference formula.** -/
theorem integral_schwarzDifferenceKernel_mul {G : ℂ → ℂ} {c z z₁ : ℂ} {r : ℝ}
    (hr : 0 < r) (hG : ContinuousOn G (closedBall c r))
    (hGd : ∀ w ∈ ball c r, DifferentiableAt ℂ G w)
    (hz : z ∈ ball c r) (hz₁ : z₁ ∈ ball c r) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, schwarzDifferenceKernel c z z₁ r θ * G (circleMap c r θ) =
      2 * Real.pi * (G z - G z₁) := by
  have hd : ∀ x ∈ ball c r \ (∅ : Set ℂ), DifferentiableAt ℂ G x := fun x hx => hGd x hx.1
  have h1 := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty hz hG hd
  have h2 := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty hz₁ hG hd
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul] at h1 h2
  have hcG := continuous_comp_circleMap hr.le hG
  have hi1 : IntervalIntegrable (fun θ : ℝ => circleMap 0 r θ * I *
      ((circleMap c r θ - z)⁻¹ * G (circleMap c r θ))) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    refine ((continuous_circleMap 0 r).mul continuous_const).mul
      ((Continuous.inv₀ ((continuous_circleMap c r).sub continuous_const)
        (circleMap_sub_ne hz)).mul hcG)
  have hi2 : IntervalIntegrable (fun θ : ℝ => circleMap 0 r θ * I *
      ((circleMap c r θ - z₁)⁻¹ * G (circleMap c r θ))) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    refine ((continuous_circleMap 0 r).mul continuous_const).mul
      ((Continuous.inv₀ ((continuous_circleMap c r).sub continuous_const)
        (circleMap_sub_ne hz₁)).mul hcG)
  have hsub := intervalIntegral.integral_sub hi1 hi2
  rw [h1, h2] at hsub
  have hpt : ∀ θ : ℝ, schwarzDifferenceKernel c z z₁ r θ * G (circleMap c r θ) =
      (-I) * (circleMap 0 r θ * I * ((circleMap c r θ - z)⁻¹ * G (circleMap c r θ)) -
        circleMap 0 r θ * I * ((circleMap c r θ - z₁)⁻¹ * G (circleMap c r θ))) := by
    intro θ
    have h1' := circleMap_sub_ne hz θ
    have h2' := circleMap_sub_ne hz₁ θ
    unfold schwarzDifferenceKernel
    field_simp
    ring_nf
    rw [I_sq]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, hsub]
  ring_nf
  rw [I_sq]
  ring

/-- **The anti-holomorphic half is invisible to the difference kernel.** -/
theorem integral_schwarzDifferenceKernel_mul_conj {G : ℂ → ℂ} {c z z₁ : ℂ} {r : ℝ}
    (hr : 0 < r) (hG : ContinuousOn G (closedBall c r))
    (hGd : ∀ w ∈ ball c r, DifferentiableAt ℂ G w)
    (hz : z ∈ ball c r) (hz₁ : z₁ ∈ ball c r) :
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      schwarzDifferenceKernel c z z₁ r θ * (starRingEnd ℂ) (G (circleMap c r θ)) = 0 := by
  set a : ℂ := z - c
  set b : ℂ := z₁ - c
  have ha : ‖a‖ < r := by simpa [a, dist_eq_norm] using mem_ball.mp hz
  have hb : ‖b‖ < r := by simpa [b, dist_eq_norm] using mem_ball.mp hz₁
  -- the holomorphic reflected integrand
  set H : ℂ → ℂ := fun ζ => (r : ℂ) ^ 2 * G ζ /
    (((r : ℂ) ^ 2 - (starRingEnd ℂ) a * (ζ - c)) * ((r : ℂ) ^ 2 - (starRingEnd ℂ) b * (ζ - c)))
  have hden : ∀ ζ ∈ closedBall c r, ∀ e : ℂ, ‖e‖ < r →
      (r : ℂ) ^ 2 - (starRingEnd ℂ) e * (ζ - c) ≠ 0 := by
    intro ζ hζ e he h
    have hζ' : ‖ζ - c‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hζ
    have heq : (starRingEnd ℂ) e * (ζ - c) = (r : ℂ) ^ 2 := (sub_eq_zero.mp h).symm
    have hn : ‖(starRingEnd ℂ) e * (ζ - c)‖ = r ^ 2 := by
      rw [heq]; simp [norm_pow, abs_of_pos hr]
    rw [norm_mul, Complex.norm_conj] at hn
    have : ‖e‖ * ‖ζ - c‖ < r ^ 2 := by
      calc ‖e‖ * ‖ζ - c‖ ≤ ‖e‖ * r := mul_le_mul_of_nonneg_left hζ' (norm_nonneg _)
        _ < r * r := mul_lt_mul_of_pos_right he hr
        _ = r ^ 2 := by ring
    linarith
  have hHc : ContinuousOn H (closedBall c r) := by
    refine ContinuousOn.div (continuousOn_const.mul hG) ?_ ?_
    · exact ((continuousOn_const.sub (continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const))).mul
        (continuousOn_const.sub (continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const))))
    · intro ζ hζ
      exact mul_ne_zero (hden ζ hζ a ha) (hden ζ hζ b hb)
  have hHd : ∀ ζ ∈ ball c r \ (∅ : Set ℂ), DifferentiableAt ℂ H ζ := by
    intro ζ hζ
    have hζc : ζ ∈ closedBall c r := ball_subset_closedBall hζ.1
    refine DifferentiableAt.div ((differentiableAt_const _).mul (hGd ζ hζ.1)) ?_
      (mul_ne_zero (hden ζ hζc a ha) (hden ζ hζc b hb))
    fun_prop
  have hzero := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hr.le Set.countable_empty hHc hHd
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul] at hzero
  -- conjugated pointwise identity
  have hpt : ∀ θ : ℝ, (starRingEnd ℂ) (schwarzDifferenceKernel c z z₁ r θ *
        (starRingEnd ℂ) (G (circleMap c r θ))) =
      ((starRingEnd ℂ) a - (starRingEnd ℂ) b) * (-I) *
        (circleMap 0 r θ * I * H (circleMap c r θ)) := by
    intro θ
    set w : ℂ := circleMap 0 r θ with hw
    have hwn : ‖w‖ = r := by rw [hw, norm_circleMap_zero, abs_of_pos hr]
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hwn; linarith
    have hwconj : (starRingEnd ℂ) w = (r : ℂ) ^ 2 / w := by
      rw [eq_div_iff hw0, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hwn]
      push_cast; ring
    have hζ : circleMap c r θ = c + w := by rw [hw, ← circleMap_sub_center c r θ]; ring
    have hζc : circleMap c r θ ∈ closedBall c r :=
      sphere_subset_closedBall (circleMap_mem_sphere c hr.le θ)
    have hA := hden _ hζc a ha
    have hB := hden _ hζc b hb
    rw [hζ] at hA hB
    have hA' : (r : ℂ) ^ 2 - (starRingEnd ℂ) a * w ≠ 0 := by simpa using hA
    have hB' : (r : ℂ) ^ 2 - (starRingEnd ℂ) b * w ≠ 0 := by simpa using hB
    have hza : circleMap c r θ - z = w - a := by rw [hζ]; simp [a]; ring
    have hzb : circleMap c r θ - z₁ = w - b := by rw [hζ]; simp [b]; ring
    have hwa : w - a ≠ 0 := by rw [← hza]; exact circleMap_sub_ne hz θ
    have hwb : w - b ≠ 0 := by rw [← hzb]; exact circleMap_sub_ne hz₁ θ
    have hzz : z - z₁ = a - b := by simp [a, b]
    unfold schwarzDifferenceKernel
    simp only [H]
    rw [hza, hzb, hzz, ← hw, hζ, add_sub_cancel_left]
    simp only [map_mul, map_div₀, map_sub, Complex.conj_conj, hwconj]
    have hwc : (starRingEnd ℂ) w - (starRingEnd ℂ) a ≠ 0 := by
      rw [← map_sub]; exact (map_ne_zero _).mpr hwa
    have hwcb : (starRingEnd ℂ) w - (starRingEnd ℂ) b ≠ 0 := by
      rw [← map_sub]; exact (map_ne_zero _).mpr hwb
    rw [hwconj] at hwc hwcb
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hint : ∫ θ in (0 : ℝ)..2 * Real.pi, (starRingEnd ℂ) (schwarzDifferenceKernel c z z₁ r θ *
        (starRingEnd ℂ) (G (circleMap c r θ))) = 0 := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, hzero, mul_zero]
  rw [intervalIntegral.intervalIntegral_conj] at hint
  exact (map_eq_zero _).mp hint

/-- **Schwarz difference formula.**  The holomorphic increment `G z - G z₁` is determined by the
boundary imaginary part alone, modulo any real constant. -/
theorem schwarz_difference_formula {G : ℂ → ℂ} {c z z₁ : ℂ} {r : ℝ}
    (hr : 0 < r) (hG : ContinuousOn G (closedBall c r))
    (hGd : ∀ w ∈ ball c r, DifferentiableAt ℂ G w)
    (hz : z ∈ ball c r) (hz₁ : z₁ ∈ ball c r) (m : ℝ) :
    G z - G z₁ = I / Real.pi * ∫ θ in (0 : ℝ)..2 * Real.pi,
      schwarzDifferenceKernel c z z₁ r θ * (((G (circleMap c r θ)).im - m : ℝ) : ℂ) := by
  have hK := continuous_schwarzDifferenceKernel hz hz₁
  have hcG := continuous_comp_circleMap hr.le hG
  have h1 := integral_schwarzDifferenceKernel_mul hr hG hGd hz hz₁
  have h2 := integral_schwarzDifferenceKernel_mul_conj hr hG hGd hz hz₁
  -- the kernel has zero mean (apply the Cauchy formula to a constant)
  have h0 : ∫ θ in (0 : ℝ)..2 * Real.pi, schwarzDifferenceKernel c z z₁ r θ = 0 := by
    have := integral_schwarzDifferenceKernel_mul (G := fun _ => (1 : ℂ)) hr continuousOn_const
      (fun w _ => differentiableAt_const _) hz hz₁
    simpa using this
  have hiG : IntervalIntegrable (fun θ => schwarzDifferenceKernel c z z₁ r θ *
      G (circleMap c r θ)) volume 0 (2 * Real.pi) := (hK.mul hcG).intervalIntegrable _ _
  have hiC : IntervalIntegrable (fun θ => schwarzDifferenceKernel c z z₁ r θ *
      (starRingEnd ℂ) (G (circleMap c r θ))) volume 0 (2 * Real.pi) :=
    (hK.mul (Complex.continuous_conj.comp hcG)).intervalIntegrable _ _
  have hiK : IntervalIntegrable (fun θ => schwarzDifferenceKernel c z z₁ r θ * (m : ℂ))
      volume 0 (2 * Real.pi) := (hK.mul continuous_const).intervalIntegrable _ _
  have hpt : ∀ θ : ℝ, schwarzDifferenceKernel c z z₁ r θ *
      (((G (circleMap c r θ)).im - m : ℝ) : ℂ) =
      (-I / 2) * (schwarzDifferenceKernel c z z₁ r θ * G (circleMap c r θ) -
        schwarzDifferenceKernel c z z₁ r θ * (starRingEnd ℂ) (G (circleMap c r θ))) -
        schwarzDifferenceKernel c z z₁ r θ * (m : ℂ) := by
    intro θ
    have him : (((G (circleMap c r θ)).im : ℝ) : ℂ) =
        (G (circleMap c r θ) - (starRingEnd ℂ) (G (circleMap c r θ))) / (2 * I) := by
      rw [Complex.sub_conj]; push_cast; field_simp
    push_cast
    rw [him]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub ((hiG.sub hiC).const_mul _) hiK,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hiG hiC,
    intervalIntegral.integral_mul_const, h1, h2, h0]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **Schwarz difference inequality.**  An `L¹` bound on the boundary imaginary part, modulo a
real constant, bounds every interior increment of a holomorphic function. -/
theorem norm_sub_le_of_boundary_im_oscillation {G : ℂ → ℂ} {c z z₁ : ℂ} {r : ℝ}
    (hr : 0 < r) (hG : ContinuousOn G (closedBall c r))
    (hGd : ∀ w ∈ ball c r, DifferentiableAt ℂ G w)
    (hz : z ∈ ball c r) (hz₁ : z₁ ∈ ball c r) (m : ℝ) :
    ‖G z - G z₁‖ ≤ r * ‖z - z₁‖ / (Real.pi * ((r - ‖z - c‖) * (r - ‖z₁ - c‖))) *
      ∫ θ in (0 : ℝ)..2 * Real.pi, |(G (circleMap c r θ)).im - m| := by
  have hK := continuous_schwarzDifferenceKernel hz hz₁
  have hcG := continuous_comp_circleMap hr.le hG
  have ha : ‖z - c‖ < r := by simpa [dist_eq_norm] using mem_ball.mp hz
  have hb : ‖z₁ - c‖ < r := by simpa [dist_eq_norm] using mem_ball.mp hz₁
  set B : ℝ := r * ‖z - z₁‖ / ((r - ‖z - c‖) * (r - ‖z₁ - c‖)) with hB
  have hkern : ∀ θ : ℝ, ‖schwarzDifferenceKernel c z z₁ r θ‖ ≤ B := by
    intro θ
    unfold schwarzDifferenceKernel
    rw [norm_div, norm_mul, norm_mul, norm_circleMap_zero, abs_of_pos hr, hB]
    have h1 := norm_circleMap_sub_ge (z := z) (c := c) hr.le θ
    have h2 := norm_circleMap_sub_ge (z := z₁) (c := c) hr.le θ
    have hpa : 0 < r - ‖z - c‖ := by linarith
    have hpb : 0 < r - ‖z₁ - c‖ := by linarith
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul h1 h2 hpb.le (by linarith)
  rw [schwarz_difference_formula hr hG hGd hz hz₁ m, norm_mul]
  have hIpi : ‖I / (Real.pi : ℂ)‖ = 1 / Real.pi := by
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hIpi]
  have hint : ‖∫ θ in (0 : ℝ)..2 * Real.pi,
      schwarzDifferenceKernel c z z₁ r θ * (((G (circleMap c r θ)).im - m : ℝ) : ℂ)‖ ≤
      ∫ θ in (0 : ℝ)..2 * Real.pi, B * |(G (circleMap c r θ)).im - m| := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans ?_
    refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ ?_
    · exact (hK.mul (Complex.continuous_ofReal.comp
        ((Complex.continuous_im.comp hcG).sub continuous_const))).norm.intervalIntegrable _ _
    · exact (continuous_const.mul ((Complex.continuous_im.comp hcG).sub
        continuous_const).abs).intervalIntegrable _ _
    · intro θ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hkern θ) (abs_nonneg _)
  rw [intervalIntegral.integral_const_mul] at hint
  calc 1 / Real.pi * ‖∫ θ in (0 : ℝ)..2 * Real.pi,
        schwarzDifferenceKernel c z z₁ r θ * (((G (circleMap c r θ)).im - m : ℝ) : ℂ)‖
      ≤ 1 / Real.pi * (B * ∫ θ in (0 : ℝ)..2 * Real.pi, |(G (circleMap c r θ)).im - m|) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by rw [hB]; field_simp

/-- **Anchored bubbling exclusion.**  Let `exp ∘ G k` be zero-free holomorphic approximants on a
neighbourhood of the closed disc `closedBall c r`, converging to `f` on an open anchor `V` inside the
disc where `f` does not vanish identically.  If the boundary arguments `Im (G k)` on `C(c,r)` are
bounded in `L¹` modulo real constants, uniformly in `k`, then `f` has no zero in the disc.

No chiral splitting, energy quantum or sub-unit budget enters: a bounded boundary-argument family
of holomorphic approximants cannot lose degree at all. -/
theorem ne_zero_of_anchored_boundaryArgOscillation_bounded
    {G : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {c z₁ : ℂ} {r R M : ℝ} {V : Set ℂ}
    (hr : 0 < r) (hrR : r < R)
    (hG : ∀ k, DifferentiableOn ℂ (G k) (ball c R))
    (hosc : ∀ k, ∃ m : ℝ, ∫ θ in (0 : ℝ)..2 * Real.pi, |(G k (circleMap c r θ)).im - m| ≤ M)
    (hf : DifferentiableOn ℂ f (ball c r))
    (hV : IsOpen V) (hVsub : V ⊆ ball c r) (hz₁ : z₁ ∈ V) (hfz₁ : f z₁ ≠ 0)
    (hconv : ∀ z ∈ V, Tendsto (fun k => Complex.exp (G k z)) atTop (𝓝 (f z))) :
    ∀ z ∈ ball c r, f z ≠ 0 := by
  have hcb : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hGc : ∀ k, ContinuousOn (G k) (closedBall c r) := fun k =>
    (hG k).continuousOn.mono hcb
  have hGd : ∀ k, ∀ w ∈ ball c r, DifferentiableAt ℂ (G k) w := fun k w hw =>
    (hG k).differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hw))
  have hz₁b : z₁ ∈ ball c r := hVsub hz₁
  have hb : ‖z₁ - c‖ < r := by simpa [dist_eq_norm] using mem_ball.mp hz₁b
  have hM : 0 ≤ M := by
    obtain ⟨m, hm⟩ := hosc 0
    exact le_trans (intervalIntegral.integral_nonneg (by positivity)
      (fun θ _ => abs_nonneg _)) hm
  set bnd : ℂ → ℝ := fun z =>
    r * ‖z - z₁‖ / (Real.pi * ((r - ‖z - c‖) * (r - ‖z₁ - c‖))) * M with hbnd
  have hinc : ∀ k, ∀ z ∈ ball c r, ‖G k z - G k z₁‖ ≤ bnd z := by
    intro k z hz
    obtain ⟨m, hm⟩ := hosc k
    have hmain := norm_sub_le_of_boundary_im_oscillation hr (hGc k) (hGd k) hz hz₁b m
    refine hmain.trans (mul_le_mul_of_nonneg_left hm ?_)
    have ha : ‖z - c‖ < r := by simpa [dist_eq_norm] using mem_ball.mp hz
    have h1 : 0 < r - ‖z - c‖ := by linarith
    have h2 : 0 < r - ‖z₁ - c‖ := by linarith
    positivity
  set F : ℕ → ℂ → ℂ := fun k z => Complex.exp (G k z - G k z₁) with hFdef
  have hFd : ∀ k, DifferentiableOn ℂ (F k) (ball c r) := fun k z hz =>
    ((hGd k z hz).sub (differentiableAt_const _)).cexp.differentiableWithinAt
  have hnormF : ∀ k z, ‖F k z‖ = Real.exp (G k z - G k z₁).re := fun k z => by
    simp [hFdef, Complex.norm_exp]
  have hloc : ∀ z ∈ ball c r, ∃ ρ : ℝ, 0 < ρ ∧ ball z ρ ⊆ ball c r ∧ ∃ C : ℝ,
      ∀ k, ∀ w ∈ ball z ρ, ‖F k w‖ ≤ C := by
    intro z hz
    have ha : ‖z - c‖ < r := by simpa [dist_eq_norm] using mem_ball.mp hz
    set ρ : ℝ := (r - ‖z - c‖) / 2 with hρdef
    have hρ : 0 < ρ := by rw [hρdef]; linarith
    have hwc : ∀ w ∈ ball z ρ, ‖w - c‖ < ‖z - c‖ + ρ := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw
      calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
        _ < ρ + ‖z - c‖ := by linarith
        _ = ‖z - c‖ + ρ := by ring
    have hsub : ball z ρ ⊆ ball c r := by
      intro w hw
      rw [mem_ball, dist_eq_norm]
      have := hwc w hw
      rw [hρdef] at this
      linarith
    refine ⟨ρ, hρ, hsub, Real.exp (r * (2 * r) / (Real.pi * (ρ * (r - ‖z₁ - c‖))) * M), ?_⟩
    intro k w hw
    rw [hnormF]
    apply Real.exp_le_exp.mpr
    have hre : (G k w - G k z₁).re ≤ ‖G k w - G k z₁‖ := Complex.re_le_norm _
    refine hre.trans ((hinc k w (hsub hw)).trans ?_)
    have hw1 : ‖w - c‖ < ‖z - c‖ + ρ := hwc w hw
    have hden1 : ρ ≤ r - ‖w - c‖ := by rw [hρdef] at hw1 ⊢; linarith
    have hnum : ‖w - z₁‖ ≤ 2 * r := by
      have hwr : ‖w - c‖ < r := by rw [hρdef] at hw1; linarith
      calc ‖w - z₁‖ = ‖(w - c) - (z₁ - c)‖ := by ring_nf
        _ ≤ ‖w - c‖ + ‖z₁ - c‖ := norm_sub_le _ _
        _ ≤ 2 * r := by linarith
    have h2 : 0 < r - ‖z₁ - c‖ := by linarith
    simp only [hbnd]
    gcongr
  have hT : DifferentiableOn ℂ (fun z => f z / f z₁) (ball c r) := hf.div_const _
  have hacc : ∃ᶠ z in 𝓝[≠] z₁, z ∈ V :=
    (eventually_nhdsWithin_of_eventually_nhds (hV.mem_nhds hz₁)).frequently
  have hconvF : ∀ z ∈ V, Tendsto (fun k => F k z) atTop (𝓝 (f z / f z₁)) := by
    intro z hz
    have heq : (fun k => F k z) = fun k => Complex.exp (G k z) / Complex.exp (G k z₁) := by
      funext k; simp [hFdef, Complex.exp_sub]
    rw [heq]
    exact (hconv z hz).div (hconv z₁ hz₁) hfz₁
  have hlim := GaloisForLFunctions.HTGeometry.tendstoLocallyUniformlyOn_of_pointwise_on_uniquenessSet
    isOpen_ball (convex_ball c r).isPreconnected hFd hloc hT hVsub hz₁b hacc hconvF
  intro z hz hfz
  have hlow : ∀ k, Real.exp (-bnd z) ≤ ‖F k z‖ := by
    intro k
    rw [hnormF]
    apply Real.exp_le_exp.mpr
    have h1 : -‖G k z - G k z₁‖ ≤ (G k z - G k z₁).re := by
      have := Complex.abs_re_le_norm (G k z - G k z₁)
      linarith [neg_abs_le (G k z - G k z₁).re]
    linarith [hinc k z hz]
  have htend : Tendsto (fun k => ‖F k z‖) atTop (𝓝 ‖f z / f z₁‖) :=
    (continuous_norm.tendsto _).comp (hlim.tendsto_at hz)
  have hge : Real.exp (-bnd z) ≤ ‖f z / f z₁‖ :=
    ge_of_tendsto htend (Eventually.of_forall hlow)
  rw [hfz, zero_div, norm_zero] at hge
  exact absurd hge (not_le.mpr (Real.exp_pos _))

/-- **Route 1, step 2 alone closes: the chiral budget is idle.**  If along some sequence
`x_k → 0⁺` the boundary argument of the Gaussian Euler–continuum potential `Lₓ + Aₓ` on every
circle `C(1+iγ, r)`, `0<r<1/2`, is bounded in `L¹` modulo constants, then the Riemann hypothesis
holds.  No negative-chirality loss, Möbius quantum or budget `B_base` is used: bounded passage
through the strip already forbids every strict-right zero. -/
theorem riemannHypothesis_of_gaussianPassage_boundaryArgOscillation_bounded
    (h : ∀ γ r : ℝ, 0 < r → r < 1 / 2 → ∃ x : ℕ → ℝ, (∀ k, 0 < x k) ∧
      Tendsto x atTop (𝓝 0) ∧ ∃ M : ℝ, ∀ k, ∃ m : ℝ,
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          |(gaussianRelativePotential (x k) (circleMap (1 + γ * I) r θ)).im - m| ≤ M) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  have hhalf : 1 / 2 < ρ.re := mem_rightHalf.mp hρ
  have hre : ρ.re < 1 := by
    by_contra hge
    push Not at hge
    exact xi_ne_zero_of_one_le_re hge hzero
  set c : ℂ := 1 + (ρ.im : ℂ) * I with hc
  set r : ℝ := (1 - ρ.re + 1 / 2) / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hr : r < 1 / 2 := by rw [hrdef]; linarith
  have hcre : c.re = 1 := by simp [hc]
  have hcim : c.im = ρ.im := by simp [hc]
  have hρc : ‖ρ - c‖ = 1 - ρ.re := by
    have hdiff : ρ - c = ((ρ.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have hρball : ρ ∈ ball c r := by
    rw [mem_ball, dist_eq_norm, hρc, hrdef]
    linarith
  have hball_re : ∀ s ∈ ball c (1 / 2), 1 / 2 < s.re := by
    intro s hs
    rw [mem_ball, dist_eq_norm] at hs
    have h1 := Complex.abs_re_le_norm (s - c)
    rw [Complex.sub_re, hcre] at h1
    linarith [neg_abs_le (s.re - 1)]
  obtain ⟨x, hxpos, hx0, M, hosc⟩ := h ρ.im r hr0 hr
  have hcomm : circleMap (1 + (ρ.im : ℂ) * I) r = circleMap c r := by rw [hc]
  -- a holomorphic logarithm of the archimedean half-factor on the ball
  have hhd : DifferentiableOn ℂ gaussianArchimedeanHalfFactor (ball c (1 / 2)) := fun s hs =>
    (differentiableAt_gaussianArchimedeanHalfFactor
      (by linarith [hball_re s hs])).differentiableWithinAt
  have hhne : ∀ s ∈ ball c (1 / 2), gaussianArchimedeanHalfFactor s ≠ 0 := fun s hs =>
    gaussianArchimedeanHalfFactor_ne_zero (by linarith [hball_re s hs])
  obtain ⟨g, hgd, -, hgeq⟩ :=
    GaloisForLFunctions.HTGeometry.exists_log_on_ball (by norm_num) hhd hhne
  set ℓ : ℂ := Complex.log (gaussianArchimedeanHalfFactor c) with hℓ
  have hℓexp : Complex.exp ℓ = gaussianArchimedeanHalfFactor c :=
    Complex.exp_log (hhne c (mem_ball_self (by norm_num)))
  set G : ℕ → ℂ → ℂ := fun k s => ℓ + g s + gaussianRelativePotential (x k) s with hGdef
  have hGd : ∀ k, DifferentiableOn ℂ (G k) (ball c (1 / 2)) := fun k =>
    (differentiableOn_const _).add hgd |>.add
      (differentiable_gaussianRelativePotential (hxpos k)).differentiableOn
  have hcbr : closedBall c r ⊆ ball c (1 / 2) := closedBall_subset_ball hr
  have hgcont : Continuous (fun θ : ℝ => (g (circleMap c r θ)).im) :=
    Complex.continuous_im.comp (continuous_comp_circleMap hr0.le (hgd.continuousOn.mono hcbr))
  set Mg : ℝ := ∫ θ in (0 : ℝ)..2 * Real.pi, |(g (circleMap c r θ)).im| with hMg
  have hoscG : ∀ k, ∃ m : ℝ,
      ∫ θ in (0 : ℝ)..2 * Real.pi, |(G k (circleMap c r θ)).im - m| ≤ M + Mg := by
    intro k
    obtain ⟨m, hm⟩ := hosc k
    rw [hcomm] at hm
    refine ⟨m + ℓ.im, ?_⟩
    have hPcont : Continuous (fun θ : ℝ =>
        (gaussianRelativePotential (x k) (circleMap c r θ)).im) :=
      Complex.continuous_im.comp
        ((differentiable_gaussianRelativePotential (hxpos k)).continuous.comp
          (continuous_circleMap c r))
    have hi1 : IntervalIntegrable (fun θ : ℝ =>
        |(gaussianRelativePotential (x k) (circleMap c r θ)).im - m|) volume 0
        (2 * Real.pi) := ((hPcont.sub continuous_const).abs).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun θ : ℝ => |(g (circleMap c r θ)).im|) volume 0
        (2 * Real.pi) := hgcont.abs.intervalIntegrable _ _
    have hle : ∫ θ in (0 : ℝ)..2 * Real.pi, |(G k (circleMap c r θ)).im - (m + ℓ.im)| ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (|(gaussianRelativePotential (x k) (circleMap c r θ)).im - m| +
            |(g (circleMap c r θ)).im|) := by
      refine intervalIntegral.integral_mono_on (by positivity) ?_ (hi1.add hi2) ?_
      · exact ((Complex.continuous_im.comp (((continuous_const.add
          (hgd.continuousOn.mono hcbr |> fun h => continuous_comp_circleMap hr0.le h)).add
          ((differentiable_gaussianRelativePotential (hxpos k)).continuous.comp
            (continuous_circleMap c r))))).sub continuous_const).abs.intervalIntegrable _ _
      · intro θ _
        have heq : (G k (circleMap c r θ)).im - (m + ℓ.im) =
            ((gaussianRelativePotential (x k) (circleMap c r θ)).im - m) +
              (g (circleMap c r θ)).im := by
          simp only [hGdef, Complex.add_im]
          ring
        rw [heq]
        exact abs_add_le _ _
    rw [intervalIntegral.integral_add hi1 hi2] at hle
    linarith
  set z₁ : ℂ := c + ((r / 2 : ℝ) : ℂ) with hz₁def
  set V : Set ℂ := ball c r ∩ {s : ℂ | 1 < s.re} with hVdef
  have hVopen : IsOpen V := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hz₁V : z₁ ∈ V := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, hz₁def, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · show 1 < z₁.re
      simp [hz₁def, hcre]
      linarith
  have hxin : Tendsto x atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx0, Eventually.of_forall hxpos⟩
  have hconv : ∀ z ∈ V, Tendsto (fun k => Complex.exp (G k z)) atTop (𝓝 (xi z)) := by
    intro z hz
    have hzb : z ∈ ball c (1 / 2) := ball_subset_ball hr.le hz.1
    have heq : ∀ k, Complex.exp (G k z) = gaussianEulerContinuumFormation (x k) z := by
      intro k
      simp only [hGdef, gaussianEulerContinuumFormation, Complex.exp_add, hℓexp]
      rw [← hgeq z hzb]
    simp_rw [heq]
    exact (tendstoLocallyUniformlyOn_gaussianEulerContinuumFormation.tendsto_at
      (show z ∈ gaussianSafeEulerChart from hz.2)).comp hxin
  exact ne_zero_of_anchored_boundaryArgOscillation_bounded hr0 hr hGd hoscG
    xi_differentiable.differentiableOn hVopen inter_subset_left hz₁V
    (xi_ne_zero_of_one_le_re (le_of_lt hz₁V.2)) hconv ρ hρball hzero

end

end RHTower
