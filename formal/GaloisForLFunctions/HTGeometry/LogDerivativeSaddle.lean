import GaloisForLFunctions.HTGeometry.DiscHolomorphicFixedPoint
import GaloisForLFunctions.HTGeometry.LogLinearGronwallModel
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Saddles determined by a logarithmic derivative

A bounded logarithmic derivative yields a nearby saddle for a small
Gaussian time. Controlling its derivative makes the function, after
removing the saddle's linear exponential, quadratically close to one.
-/

open Complex Set Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A holomorphic disk map supplies the Gaussian saddle within the smaller disk. -/
theorem exists_logDeriv_saddle {f : ℂ → ℂ} {z : ℂ} {r t K : ℝ}
    (hr : 0 < r) (ht : 0 ≤ t) (htK : 2 * t * K ≤ r)
    (hf : DifferentiableOn ℂ f (ball z (2 * r)))
    (hne : ∀ w ∈ ball z (2 * r), f w ≠ 0)
    (hq : ∀ w ∈ ball z (2 * r), ‖deriv f w / f w‖ ≤ K) :
    ∃ s : ℂ, ‖s - z‖ ≤ r ∧ s = z + 2 * (t : ℂ) * (deriv f s / f s) := by
  let ψ : ℂ → ℂ := fun w => z + 2 * (t : ℂ) * (deriv f w / f w)
  have han := hf.analyticOnNhd isOpen_ball
  have hd : DifferentiableOn ℂ ψ (ball z (2 * r)) := by
    intro w hw
    have hqdiff := ((han w hw).deriv.div (han w hw) (hne w hw)).differentiableAt
    exact ((hqdiff.const_mul (2 * (t : ℂ))).const_add z).differentiableWithinAt
  have hm : MapsTo ψ (ball z (2 * r)) (closedBall z ((1 / 2) * (2 * r))) := by
    intro w hw
    rw [mem_closedBall_iff_norm]
    change ‖z + 2 * (t : ℂ) * (deriv f w / f w) - z‖ ≤ _
    rw [add_sub_cancel_left, norm_mul]
    have hnorm : ‖(2 : ℂ) * (t : ℂ)‖ = 2 * t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
      norm_num
    rw [hnorm]
    have h := (mul_le_mul_of_nonneg_left (hq w hw) (show 0 ≤ 2 * t by positivity)).trans htK
    nlinarith only [h]
  obtain ⟨s, hs, hfix, _, _⟩ := DiscFixedPoint.exists_unique_fixedPoint
    (by positivity : 0 < 2 * r) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hd hm
  exact ⟨s, by have h := mem_closedBall_iff_norm.mp hs; nlinarith only [h], hfix.symm⟩

/-- Removing the logarithmic slope leaves a quadratic error on a real segment. -/
theorem norm_exp_logDeriv_normalized_sub_one_le {f : ℂ → ℂ} {z s : ℂ} {r K : ℝ}
    (hr : 0 < r) (hK : 0 < K) (hf : Differentiable ℂ f)
    (hne : ∀ w : ℂ, ‖w - z‖ ≤ 4 * r → f w ≠ 0)
    (hq' : ∀ w : ℂ, ‖w - z‖ ≤ 4 * r →
      ‖deriv (fun v => deriv f v / f v) w‖ ≤ K)
    (hs : ‖s - z‖ ≤ r) {u : ℝ} (hu : |u| ≤ r) :
    ‖Complex.exp (-(u : ℂ) * (deriv f s / f s)) * f (s + u) / f s - 1‖ ≤
      Real.exp (K * u ^ 2) - 1 := by
  let q : ℂ → ℂ := fun w => deriv f w / f w
  let a := q s
  have hfs : f s ≠ 0 := hne s (by linarith only [hs, hr])
  by_cases hu0 : u = 0
  · subst u
    simp [hfs]
  have huabs : 0 < |u| := abs_pos.mpr hu0
  have han := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hqa : ∀ w ∈ closedBall z (4 * r), DifferentiableAt ℂ q w := by
    intro w hw
    exact ((han w (mem_univ w)).deriv.div (han w (mem_univ w))
      (hne w (mem_closedBall_iff_norm.mp hw))).differentiableAt
  have hvabs : ∀ v ∈ uIcc (0 : ℝ) u, |v| ≤ |u| := by
    intro v hv
    exact abs_le.mpr (uIcc_subset_Icc
      ⟨by linarith only [abs_nonneg u], abs_nonneg u⟩ ⟨neg_abs_le u, le_abs_self u⟩ hv)
  have hvnear : ∀ v ∈ uIcc (0 : ℝ) u, ‖s + (v : ℂ) - z‖ ≤ 4 * r := by
    intro v hv
    have htri : ‖s + (v : ℂ) - z‖ ≤ ‖s - z‖ + |v| := by
      calc
        _ = ‖(s - z) + (v : ℂ)‖ := by congr 1; ring
        _ ≤ ‖s - z‖ + ‖(v : ℂ)‖ := norm_add_le _ _
        _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]
    linarith only [htri, hs, hvabs v hv, hu, hr]
  have hqnear : ∀ v ∈ uIcc (0 : ℝ) u, ‖q (s + v) - a‖ ≤ K * |u| := by
    intro v hv
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (x := s) (y := s + (v : ℂ)) hqa
      (fun w hw => hq' w (mem_closedBall_iff_norm.mp hw)) (convex_closedBall z (4 * r))
      (mem_closedBall_iff_norm.mpr (by linarith only [hs, hr]))
      (mem_closedBall_iff_norm.mpr (hvnear v hv))
    have hvnorm : ‖s + (v : ℂ) - s‖ = |v| := by
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    rw [hvnorm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hvabs v hv) hK.le)
  have hF : ∀ v ∈ uIcc (0 : ℝ) u,
      HasDerivAt (fun v : ℝ => f (s + v)) (deriv f (s + v)) v := by
    intro v _
    have hin : HasDerivAt (fun w : ℂ => s + w) 1 (v : ℂ) :=
      (hasDerivAt_id' (v : ℂ)).const_add s
    have h := (hf (s + v)).hasDerivAt.comp (v : ℂ) hin
    simpa only [Function.comp_def, mul_one] using h.comp_ofReal
  have hres : ∀ v ∈ uIcc (0 : ℝ) u,
      ‖deriv f (s + v) - a * f (s + v)‖ ≤ (K * |u|) * ‖f (s + v)‖ := by
    intro v hv
    have heq : deriv f (s + v) = q (s + v) * f (s + v) :=
      (div_mul_cancel₀ _ (hne _ (hvnear v hv))).symm
    rw [heq, ← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hqnear v hv) (norm_nonneg _)
  have hmodel := norm_sub_mul_exp_le (mul_pos hK huabs) hF hres
  simp only [Complex.ofReal_zero, add_zero, sub_zero] at hmodel
  have he : Complex.exp (-((u : ℂ) * a)) * Complex.exp ((u : ℂ) * a) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hrewrite : Complex.exp (-(u : ℂ) * a) * f (s + u) / f s - 1 =
      (Complex.exp (-(u : ℂ) * a) / f s) * (f (s + u) - f s * Complex.exp ((u : ℂ) * a)) := by
    field_simp [hfs]
    linear_combination f s * he
  have hcancel : ‖Complex.exp (-(u : ℂ) * a) / f s‖ *
      (‖f s‖ * Real.exp (u * a.re)) = 1 := by
    rw [norm_div, Complex.norm_exp]
    have heR : Real.exp ((-(u : ℂ) * a).re) * Real.exp (u * a.re) = 1 := by
      rw [← Real.exp_add]
      have hre : (-(u : ℂ) * a).re + u * a.re = 0 := by simp
      rw [hre, Real.exp_zero]
    calc
      _ = Real.exp ((-(u : ℂ) * a).re) * Real.exp (u * a.re) := by
        field_simp [norm_ne_zero_iff.mpr hfs]
      _ = 1 := heR
  change ‖Complex.exp (-(u : ℂ) * a) * f (s + u) / f s - 1‖ ≤ _
  rw [hrewrite, norm_mul]
  calc
    _ ≤ ‖Complex.exp (-(u : ℂ) * a) / f s‖ *
        (‖f s‖ * Real.exp (u * a.re) * (Real.exp ((K * |u|) * |u|) - 1)) :=
      mul_le_mul_of_nonneg_left hmodel (norm_nonneg _)
    _ = _ := by
      rw [← mul_assoc, hcancel, one_mul]
      congr 2
      calc (K * |u|) * |u| = K * |u| ^ 2 := by ring
        _ = K * u ^ 2 := by rw [sq_abs]

end

end GaloisForLFunctions.HTGeometry
