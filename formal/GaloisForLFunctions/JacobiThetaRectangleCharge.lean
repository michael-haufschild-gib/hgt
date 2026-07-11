import GaloisForLFunctions.JacobiThetaParallelogramCharge
import GaloisForLFunctions.JacobiThetaBoundaryRegular
import GaloisForLFunctions.RHTower.RectangleResidue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open Complex Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions

noncomputable section

open Metric

def ThetaRectangleBoundaryRegular (τ z₁ : ℂ) : Prop :=
  (∀ x : ℝ, x ∈ uIcc z₁.re (z₁.re + 1) →
      jacobiTheta₂ ((x : ℂ) + z₁.im * I) τ ≠ 0) ∧
    ∀ y : ℝ, y ∈ uIcc z₁.im (z₁.im + τ.im) →
      jacobiTheta₂ ((z₁.re : ℂ) + y * I) τ ≠ 0

def thetaRectangleUpperRight (τ z₁ : ℂ) : ℂ :=
  (z₁.re + 1 : ℝ) + (z₁.im + τ.im : ℝ) * I

theorem thetaRectangleUpperRight_re (τ z₁ : ℂ) :
    (thetaRectangleUpperRight τ z₁).re = z₁.re + 1 := by simp [thetaRectangleUpperRight]

theorem thetaRectangleUpperRight_im (τ z₁ : ℂ) :
    (thetaRectangleUpperRight τ z₁).im = z₁.im + τ.im := by simp [thetaRectangleUpperRight]

theorem thetaRectangle_bottom_ne_zero_all {z₁ τ : ℂ}
    (h : ThetaRectangleBoundaryRegular τ z₁) (x : ℝ) :
    jacobiTheta₂ ((x : ℂ) + z₁.im * I) τ ≠ 0 := by
  intro hx
  let n : ℤ := -⌊(x - z₁.re : ℝ)⌋
  let t : ℝ := x + n
  have ht0 : z₁.re ≤ t := by
    dsimp [t, n]
    push_cast
    have hfloor := Int.floor_le (x - z₁.re)
    linarith
  have ht1 : t ≤ z₁.re + 1 := by
    dsimp [t, n]
    push_cast
    have hfloor := Int.lt_floor_add_one (x - z₁.re)
    linarith
  have htmem : t ∈ uIcc z₁.re (z₁.re + 1) := by
    rw [uIcc_of_le (by linarith : z₁.re ≤ z₁.re + 1)]
    exact ⟨ht0, ht1⟩
  have hzero := jacobiTheta₂_eq_zero_add_int hx n
  apply h.1 t htmem
  convert hzero using 1
  dsimp [t]
  push_cast
  ring

theorem thetaRectangle_top_ne_zero {z₁ τ : ℂ}
    (h : ThetaRectangleBoundaryRegular τ z₁) (x : ℝ) :
    jacobiTheta₂ ((x : ℂ) + (z₁.im + τ.im : ℝ) * I) τ ≠ 0 := by
  let z : ℂ := ((x - τ.re : ℝ) : ℂ) + z₁.im * I
  have hz : jacobiTheta₂ z τ ≠ 0 := thetaRectangle_bottom_ne_zero_all h (x - τ.re)
  have harg : z + τ = (x : ℂ) + (z₁.im + τ.im : ℝ) * I := by
    apply Complex.ext
    · simp [z]
    · simp [z]
  rw [← harg, jacobiTheta₂_add_left']
  exact mul_ne_zero (Complex.exp_ne_zero _) hz

theorem thetaRectangle_right_ne_zero {z₁ τ : ℂ}
    (h : ThetaRectangleBoundaryRegular τ z₁) (y : ℝ)
    (hy : y ∈ uIcc z₁.im (z₁.im + τ.im)) :
    jacobiTheta₂ ((z₁.re + 1 : ℝ) + y * I) τ ≠ 0 := by
  have hl := h.2 y hy
  rw [show ((z₁.re + 1 : ℝ) : ℂ) + y * I =
      ((z₁.re : ℂ) + y * I) + 1 by push_cast; ring, jacobiTheta₂_add_left]
  exact hl

theorem thetaRectangleIntegral_eq_two_pi_I {z₁ τ : ℂ} (hτ : 0 < τ.im)
    (hregular : ThetaRectangleBoundaryRegular τ z₁) :
    RHTower.rectIntegral (fun z => thetaLogDeriv z τ) z₁ (thetaRectangleUpperRight τ z₁) =
      2 * Real.pi * I := by
  let f : ℝ → ℂ := fun x => thetaLogDeriv ((x : ℂ) + z₁.im * I) τ
  have hfper : Function.Periodic f 1 := by
    intro x
    dsimp [f]
    convert thetaLogDeriv_add_one ((x : ℂ) + z₁.im * I) τ using 1
    push_cast
    ring
  have hfc : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hedge : ContinuousAt (fun s : ℝ => (s : ℂ) + z₁.im * I) x := by fun_prop
    have hθp : ContinuousAt (jacobiTheta₂' · τ) ((x : ℂ) + z₁.im * I) :=
      ((jacobiTheta₂'_analyticOnNhd_fst τ hτ) _ (mem_univ _)).continuousAt
    have hθ : ContinuousAt (jacobiTheta₂ · τ) ((x : ℂ) + z₁.im * I) :=
      ((jacobiTheta₂_analyticOnNhd_fst τ hτ) _ (mem_univ _)).continuousAt
    exact (hθp.comp_of_eq hedge rfl).div (hθ.comp_of_eq hedge rfl)
      (thetaRectangle_bottom_ne_zero_all hregular x)
  have hright :
      (∫ y : ℝ in z₁.im..z₁.im + τ.im,
        thetaLogDeriv (((z₁.re + 1 : ℝ) : ℂ) + y * I) τ) =
      ∫ y : ℝ in z₁.im..z₁.im + τ.im,
        thetaLogDeriv ((z₁.re : ℂ) + y * I) τ := by
    apply integral_congr
    intro y _
    convert thetaLogDeriv_add_one ((z₁.re : ℂ) + y * I) τ using 1
    push_cast
    ring
  have htopPoint (x : ℝ) :
      thetaLogDeriv ((x : ℂ) + (z₁.im + τ.im : ℝ) * I) τ =
        f (x - τ.re) - 2 * Real.pi * I := by
    have hz := thetaRectangle_bottom_ne_zero_all hregular (x - τ.re)
    have h := thetaLogDeriv_add_tau hz
    dsimp [f]
    have harg : ((x - τ.re : ℝ) : ℂ) + z₁.im * I + τ =
        (x : ℂ) + (z₁.im + τ.im : ℝ) * I := by
      apply Complex.ext <;> simp
    rw [← harg]
    exact h
  have htop :
      (∫ x : ℝ in z₁.re..z₁.re + 1,
        thetaLogDeriv ((x : ℂ) + (z₁.im + τ.im : ℝ) * I) τ) =
      (∫ x : ℝ in z₁.re..z₁.re + 1, f x) - 2 * Real.pi * I := by
    have hshiftc : Continuous (fun x => f (x - τ.re)) :=
      hfc.comp (continuous_id.sub continuous_const)
    rw [integral_congr (fun x _ => htopPoint x),
      integral_sub (hshiftc.intervalIntegrable _ _) intervalIntegrable_const]
    rw [intervalIntegral.integral_comp_sub_right f τ.re]
    have hperiod := hfper.intervalIntegral_add_eq (z₁.re - τ.re) z₁.re
    rw [show z₁.re - τ.re + 1 = z₁.re + 1 - τ.re by ring] at hperiod
    rw [hperiod, intervalIntegral.integral_const]
    norm_num
  rw [RHTower.rectIntegral, thetaRectangleUpperRight_re, thetaRectangleUpperRight_im,
    htop, hright]
  change (∫ x : ℝ in z₁.re..z₁.re + 1, f x) -
      ((∫ x : ℝ in z₁.re..z₁.re + 1, f x) - 2 * Real.pi * I) +
      I • (∫ y : ℝ in z₁.im..z₁.im + τ.im,
        thetaLogDeriv ((z₁.re : ℂ) + y * I) τ) -
      I • (∫ y : ℝ in z₁.im..z₁.im + τ.im,
        thetaLogDeriv ((z₁.re : ℂ) + y * I) τ) = 2 * Real.pi * I
  abel

end
end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

open Metric

theorem exists_thetaRectangleBoundaryRegular {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ z₁ : ℂ, ThetaRectangleBoundaryRegular τ z₁ := by
  let R : ℝ := 4 + 2 * ‖τ‖
  let Z : Set ℂ := {z ∈ closedBall 0 R | jacobiTheta₂ z τ = 0}
  have hZ : Z.Finite := jacobiTheta₂_zeros_closedBall_finite hτ 0 R
  let BadX : Set ℝ := (fun z : ℂ => z.re) '' Z
  let BadY : Set ℝ := (fun z : ℂ => z.im) '' Z
  have hBadX : BadX.Finite := hZ.image _
  have hBadY : BadY.Finite := hZ.image _
  have hI : (Ioo ((1 : ℝ) / 4) (1 / 3)).Infinite := Set.Ioo_infinite (by norm_num)
  obtain ⟨x₀, hxI, hxBad⟩ := (hI.diff hBadX).nonempty
  obtain ⟨y₀, hyI, hyBad⟩ := (hI.diff hBadY).nonempty
  have hx0 : 0 ≤ x₀ := by linarith [hxI.1]
  have hx1 : x₀ ≤ 1 := by linarith [hxI.2]
  have hy0 : 0 ≤ y₀ := by linarith [hyI.1]
  have hy1 : y₀ ≤ 1 := by linarith [hyI.2]
  let z₁ : ℂ := (x₀ : ℂ) + (y₀ : ℂ) * I
  refine ⟨z₁, ?_, ?_⟩
  · intro x hx hzero
    have hzre : z₁.re = x₀ := by simp [z₁]
    have hzim : z₁.im = y₀ := by simp [z₁]
    rw [hzre, uIcc_of_le (by linarith : x₀ ≤ x₀ + 1), mem_Icc] at hx
    let z : ℂ := (x : ℂ) + z₁.im * I
    have hx0' : 0 ≤ x := le_trans hx0 hx.1
    have hx2 : x ≤ 2 := by linarith
    have hzball : z ∈ closedBall 0 R := by
      rw [mem_closedBall, dist_zero_right]
      calc
        ‖z‖ ≤ ‖(x : ℂ)‖ + ‖(z₁.im : ℂ) * I‖ := norm_add_le _ _
        _ = |x| + |z₁.im| := by simp
        _ = x + y₀ := by rw [hzim, abs_of_nonneg hx0', abs_of_nonneg hy0]
        _ ≤ R := by dsimp [R]; nlinarith [norm_nonneg τ]
    have hzZ : z ∈ Z := ⟨hzball, hzero⟩
    apply hyBad
    exact ⟨z, hzZ, by simp [z, hzim]⟩
  · intro y hy hzero
    have hzre : z₁.re = x₀ := by simp [z₁]
    have hzim : z₁.im = y₀ := by simp [z₁]
    rw [hzim, uIcc_of_le (by linarith : y₀ ≤ y₀ + τ.im), mem_Icc] at hy
    let z : ℂ := (z₁.re : ℂ) + (y : ℂ) * I
    have hy0' : 0 ≤ y := le_trans hy0 hy.1
    have hybound : y ≤ 1 + ‖τ‖ := by
      have himle : τ.im ≤ ‖τ‖ := abs_im_le_norm τ |>.trans' (le_abs_self τ.im)
      linarith
    have hzball : z ∈ closedBall 0 R := by
      rw [mem_closedBall, dist_zero_right]
      calc
        ‖z‖ ≤ ‖(z₁.re : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
        _ = |z₁.re| + |y| := by simp
        _ = x₀ + y := by rw [hzre, abs_of_nonneg hx0, abs_of_nonneg hy0']
        _ ≤ R := by dsimp [R]; nlinarith [norm_nonneg τ]
    have hzZ : z ∈ Z := ⟨hzball, hzero⟩
    apply hxBad
    exact ⟨z, hzZ, by simp [z, hzre]⟩

end
end GaloisForLFunctions
