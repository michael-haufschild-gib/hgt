import GaloisForLFunctions.IncommensurableGaborPinching.CosineKernelAdditiveRigidity

/-!
# An explicit cosine triple floor

The cotangent-line residual cannot be small at both gaps and their sum.
A weighted circle identity makes this obstruction uniform in the line slope
and the frequencies, replacing a compactness argument by an explicit constant.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-- Residual of the cotangent-line equation governing cosine-transform zeros. -/
def cotangentLineResidual (c t : ℝ) : ℝ := c * t * Real.sin t - Real.cos t

private theorem residual_sine_energy {c t : ℝ}
    (h : |cotangentLineResidual c t| ≤ 1 / 10) :
    (2 / 5 : ℝ) ≤ (1 + (c * t) ^ 2) * Real.sin t ^ 2 := by
  have hr : cotangentLineResidual c t ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg _) h
  have hs := Real.sin_sq_add_cos_sq t
  have hp := sq_nonneg (c * t * Real.sin t + cotangentLineResidual c t)
  dsimp only [cotangentLineResidual] at hr hp
  nlinarith only [hr, hs, hp]

private theorem weighted_mixed_bound {Y v Q : ℝ}
    (hQ : 3 / 4 * (1 + Y ^ 2) ≤ Q)
    (hv : (2 / 5 : ℝ) ≤ (1 + Y ^ 2) * v ^ 2) :
    |Y| ≤ 3 * Q * |v| := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ
  have hQsq := mul_self_le_mul_self (by positivity : 0 ≤ (3 / 4 : ℝ) * (1 + Y ^ 2)) hQ
  have h1 := mul_le_mul_of_nonneg_right hQsq (sq_nonneg v)
  have h2 := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ (9 / 16 : ℝ) * (1 + Y ^ 2))
  have hsq : |Y| ^ 2 ≤ (3 * Q * |v|) ^ 2 := by
    rw [sq_abs, mul_pow, sq_abs]
    nlinarith only [h1, h2, sq_nonneg Y]
  have hp : 0 ≤ 3 * Q * |v| := by positivity
  nlinarith only [hsq, hp, abs_nonneg Y]

private theorem weighted_sine_product_floor {X Y u v : ℝ}
    (hu : (2 / 5 : ℝ) ≤ (1 + X ^ 2) * u ^ 2)
    (hv : (2 / 5 : ℝ) ≤ (1 + Y ^ 2) * v ^ 2) :
    (2 / 5 : ℝ) ≤ (1 + X ^ 2 + X * Y + Y ^ 2) * |u * v| := by
  let Q := 1 + X ^ 2 + X * Y + Y ^ 2
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    nlinarith only [sq_nonneg (X + Y), sq_nonneg X, sq_nonneg Y]
  have hQQ : (1 + X ^ 2) * (1 + Y ^ 2) ≤ Q ^ 2 := by
    have h := mul_nonneg (sq_nonneg (X + Y))
      (by positivity : 0 ≤ 1 + X ^ 2 + Y ^ 2)
    dsimp [Q]
    nlinarith only [h]
  have hprod := mul_le_mul hu hv (by norm_num : (0 : ℝ) ≤ 2 / 5)
    (by positivity : 0 ≤ (1 + X ^ 2) * u ^ 2)
  have hcomp := mul_le_mul_of_nonneg_right hQQ
    (mul_nonneg (sq_nonneg u) (sq_nonneg v))
  have hsq : (2 / 5 : ℝ) ^ 2 ≤ (Q * |u * v|) ^ 2 := by
    rw [mul_pow, sq_abs]
    nlinarith only [hprod, hcomp]
  have hp : 0 ≤ Q * |u * v| := mul_nonneg hQ0 (abs_nonneg _)
  nlinarith only [hsq, hp]

/-- Every slope and every additive triple have a residual larger than `1/10`. -/
theorem cotangentLineResidual_triple_floor (c x y : ℝ) :
    (1 / 10 : ℝ) < max |cotangentLineResidual c x|
      (max |cotangentLineResidual c y| |cotangentLineResidual c (x + y)|) := by
  by_contra h
  obtain ⟨hx, hy, hxy⟩ :=
    (show |cotangentLineResidual c x| ≤ 1 / 10 ∧
      |cotangentLineResidual c y| ≤ 1 / 10 ∧
      |cotangentLineResidual c (x + y)| ≤ 1 / 10 by
      simpa only [max_le_iff] using le_of_not_gt h)
  let X := c * x
  let Y := c * y
  let u := Real.sin x
  let v := Real.sin y
  let Q := 1 + X ^ 2 + X * Y + Y ^ 2
  let A := Q * |u * v|
  have hu : (2 / 5 : ℝ) ≤ (1 + X ^ 2) * u ^ 2 := residual_sine_energy hx
  have hv : (2 / 5 : ℝ) ≤ (1 + Y ^ 2) * v ^ 2 := residual_sine_energy hy
  have hA : (2 / 5 : ℝ) ≤ A := weighted_sine_product_floor hu hv
  have hQY : 3 / 4 * (1 + Y ^ 2) ≤ Q := by
    dsimp [Q]
    nlinarith only [sq_nonneg (X + Y / 2)]
  have hQX : 3 / 4 * (1 + X ^ 2) ≤ Q := by
    dsimp [Q]
    nlinarith only [sq_nonneg (Y + X / 2)]
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQY
  have hY := mul_le_mul_of_nonneg_right (weighted_mixed_bound hQY hv) (abs_nonneg u)
  have hX := mul_le_mul_of_nonneg_right (weighted_mixed_bound hQX hu) (abs_nonneg v)
  have hYu : |Y * u| ≤ 3 * A := by
    dsimp only [A]
    rw [abs_mul Y u, abs_mul u v]
    nlinarith only [hY]
  have hXv : |X * v| ≤ 3 * A := by
    dsimp only [A]
    rw [abs_mul X v, abs_mul u v]
    nlinarith only [hX]
  have heq : Q * (u * v) = cotangentLineResidual c (x + y) +
      Y * u * cotangentLineResidual c y + X * v * cotangentLineResidual c x +
        cotangentLineResidual c x * cotangentLineResidual c y := by
    dsimp [Q, X, Y, u, v, cotangentLineResidual]
    rw [Real.sin_add, Real.cos_add]
    ring
  have hab : A ≤ |cotangentLineResidual c (x + y)| +
      |Y * u| * |cotangentLineResidual c y| + |X * v| * |cotangentLineResidual c x| +
        |cotangentLineResidual c x| * |cotangentLineResidual c y| := by
    have h1 := abs_add_le (cotangentLineResidual c (x + y))
      (Y * u * cotangentLineResidual c y)
    have h2 := abs_add_le
      (cotangentLineResidual c (x + y) + Y * u * cotangentLineResidual c y)
      (X * v * cotangentLineResidual c x)
    have h3 := abs_add_le
      (cotangentLineResidual c (x + y) + Y * u * cotangentLineResidual c y +
        X * v * cotangentLineResidual c x)
      (cotangentLineResidual c x * cotangentLineResidual c y)
    rw [← heq, abs_mul, abs_of_nonneg hQ0] at h3
    dsimp only [A]
    simp only [abs_mul] at h1 h2 h3 ⊢
    linarith only [h1, h2, h3]
  have heY := mul_le_mul hYu hy (abs_nonneg _) (by linarith only [hA] : 0 ≤ 3 * A)
  have heX := mul_le_mul hXv hx (abs_nonneg _) (by linarith only [hA] : 0 ≤ 3 * A)
  have her := mul_le_mul hx hy (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 10)
  linarith only [hab, heY, heX, her, hxy, hA]

private theorem normalized_kernel_residual {κ : ℝ}
    (hθ : Zeta23.ThmD.theta κ * Real.sin (Zeta23.ThmD.theta κ) ≠ 0) (t : ℝ) :
    ((Real.pi * t) ^ 2 - Zeta23.ThmD.theta κ ^ 2) * mtKernel κ t =
      Zeta23.ThmD.theta κ ^ 2 * cotangentLineResidual
        (Real.cos (Zeta23.ThmD.theta κ) /
          (Zeta23.ThmD.theta κ * Real.sin (Zeta23.ThmD.theta κ))) (Real.pi * t) := by
  let θ := Zeta23.ThmD.theta κ
  have hzero := mtKernelNum_closed_form_global κ 0
  have hnum0 : mtKernelNum κ 0 = Zeta23.ThmD.aStar κ := by
    simp only [mtKernelNum, Zeta23.ThmD.aStar, mul_zero, zero_mul, Real.cos_zero, mul_one]
  rw [hnum0] at hzero
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_sub, Real.sin_zero,
    Real.cos_zero, zero_mul, mul_one] at hzero
  have hmean : θ ^ 2 * Zeta23.ThmD.aStar κ = θ * Real.sin θ := by
    dsimp [θ]
    linarith only [hzero]
  have ha : Zeta23.ThmD.aStar κ ≠ 0 := by
    intro ha
    rw [ha, mul_zero] at hmean
    exact hθ hmean.symm
  have h := mtKernelNum_closed_form_global κ t
  have hres : (θ * Real.sin θ) * cotangentLineResidual
      (Real.cos θ / (θ * Real.sin θ)) (Real.pi * t) =
        (Real.pi * t) * Real.cos θ * Real.sin (Real.pi * t) -
          θ * Real.sin θ * Real.cos (Real.pi * t) := by
    unfold cotangentLineResidual
    have hθ0 : θ ≠ 0 := (mul_ne_zero_iff.mp hθ).1
    have hs0 : Real.sin θ ≠ 0 := (mul_ne_zero_iff.mp hθ).2
    field_simp [hθ0, hs0]
  apply mul_left_cancel₀ ha
  rw [show Zeta23.ThmD.aStar κ *
      (((Real.pi * t) ^ 2 - Zeta23.ThmD.theta κ ^ 2) * mtKernel κ t) =
      ((Real.pi * t) ^ 2 - θ ^ 2) * mtKernelNum κ t by
        unfold mtKernel
        dsimp [θ]
        field_simp]
  calc
    _ = (θ * Real.sin θ) * cotangentLineResidual
        (Real.cos θ / (θ * Real.sin θ)) (Real.pi * t) := h.trans hres.symm
    _ = _ := by rw [← hmean]; ring

/-- Explicit normalized kernel floor on any bounded additive triple.
The mean identity cancels the trigonometric normalizer, leaving only `θ²`. -/
theorem mtKernel_explicit_triple_floor {κ S : ℝ}
    (hθ : Zeta23.ThmD.theta κ * Real.sin (Zeta23.ThmD.theta κ) ≠ 0)
    (x y : ℝ) (hx : |x| ≤ S) (hy : |y| ≤ S) (hxy : |x + y| ≤ S) :
    Zeta23.ThmD.theta κ ^ 2 / (10 * ((Real.pi * S) ^ 2 + Zeta23.ThmD.theta κ ^ 2)) ≤
      max |mtKernel κ x| (max |mtKernel κ y| |mtKernel κ (x + y)|) := by
  let θ := Zeta23.ThmD.theta κ
  let D := (Real.pi * S) ^ 2 + θ ^ 2
  let M := max |mtKernel κ x| (max |mtKernel κ y| |mtKernel κ (x + y)|)
  let c := Real.cos θ / (θ * Real.sin θ)
  have hθ0 : θ ≠ 0 := (mul_ne_zero_iff.mp hθ).1
  have hD : 0 < D := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hθ0)
  have hbound (t : ℝ) (ht : |t| ≤ S) (htM : |mtKernel κ t| ≤ M) :
      θ ^ 2 * |cotangentLineResidual c (Real.pi * t)| ≤ D * M := by
    have hs : t ^ 2 ≤ S ^ 2 := by
      simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg t) ht
    have hp := mul_le_mul_of_nonneg_left hs (sq_nonneg Real.pi)
    have hd : |(Real.pi * t) ^ 2 - θ ^ 2| ≤ D := by
      apply abs_le.mpr
      constructor <;> dsimp [D] <;>
        nlinarith only [hp, sq_nonneg (Real.pi * t), sq_nonneg (Real.pi * S), sq_nonneg θ]
    have heq := congrArg abs (normalized_kernel_residual hθ t)
    simp only [abs_mul, abs_of_nonneg (sq_nonneg (Zeta23.ThmD.theta κ))] at heq
    calc
      _ = |(Real.pi * t) ^ 2 - θ ^ 2| * |mtKernel κ t| := heq.symm
      _ ≤ D * M := mul_le_mul hd htM (abs_nonneg _) hD.le
  have hxM : |mtKernel κ x| ≤ M := le_max_left _ _
  have hyM : |mtKernel κ y| ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hxyM : |mtKernel κ (x + y)| ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hf := (cotangentLineResidual_triple_floor c (Real.pi * x) (Real.pi * y)).le
  rw [← mul_add] at hf
  have hpay : θ ^ 2 / 10 ≤ D * M := by
    rcases le_max_iff.mp hf with h | h
    · have hm := mul_le_mul_of_nonneg_left h (sq_nonneg θ)
      linarith only [hm, hbound x hx hxM]
    · rcases le_max_iff.mp h with h | h
      · have hm := mul_le_mul_of_nonneg_left h (sq_nonneg θ)
        linarith only [hm, hbound y hy hyM]
      · have hm := mul_le_mul_of_nonneg_left h (sq_nonneg θ)
        linarith only [hm, hbound (x + y) hxy hxyM]
  rw [div_le_iff₀ (by positivity : 0 < 10 * D)]
  linarith only [hpay]

/-- Shape-one specialization: the explicit floor decays quadratically in the gap bound. -/
theorem mtKernel_shapeOne_explicit_triple_floor {S : ℝ}
    (x y : ℝ) (hx : |x| ≤ S) (hy : |y| ≤ S) (hxy : |x + y| ≤ S) :
    1 / (10 + 20 * Real.pi ^ 2 * S ^ 2) ≤
      max |mtKernel 1 x| (max |mtKernel 1 y| |mtKernel 1 (x + y)|) := by
  have hs : Zeta23.ThmD.theta 1 ^ 2 = (1 / 2 : ℝ) := by
    unfold Zeta23.ThmD.theta
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hθ : Zeta23.ThmD.theta 1 * Real.sin (Zeta23.ThmD.theta 1) ≠ 0 := by
    have ha := Zeta23.ThmD.theta_pos (show (0 : ℝ) < 1 by norm_num)
    have hb : Zeta23.ThmD.theta 1 < Real.pi := by
      nlinarith only [hs, Real.pi_gt_three]
    exact mul_ne_zero ha.ne' (Real.sin_pos_of_pos_of_lt_pi ha hb).ne'
  have h := mtKernel_explicit_triple_floor hθ x y hx hy hxy
  rw [hs] at h
  have heq : (1 / 2 : ℝ) / (10 * ((Real.pi * S) ^ 2 + 1 / 2)) =
      1 / (10 + 20 * Real.pi ^ 2 * S ^ 2) := by
    field_simp
    ring
  rw [heq] at h
  exact h

end GaloisForLFunctions.IncommensurableGaborPinching
