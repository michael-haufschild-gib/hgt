import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthModularSeam
import Mathlib.Analysis.Calculus.MeanValue

/-!
# An exact compact tube for the actual theta modular orbit

First-contact differential bounds give -S <= 13x, W <= 14x, and
A >= A(0)-300x^2-x on [0,137/2000]. The arithmetic seam bounds then place
the literal full theta trajectory inside the compact D1 certificate region.
No numerical trajectory or finite theta truncation enters the proof.
-/

noncomputable section
open Set
namespace RHTower
private def u (x : ℝ) : ℝ := -(thetaCuspModularDrift x).re
private def a (x : ℝ) : ℝ := thetaCuspModularGapAmplitude x
private def w (x : ℝ) : ℝ := thetaCuspModularTransverseShear x
private theorem du (x : ℝ) : HasDerivAt u (-3+u x^2/3+3*a x/4) x := by
  convert (hasDerivAt_thetaCuspModularDrift_re x).neg using 1 <;>
    first | rfl | (try dsimp [u,a,thetaCuspModularGapAmplitude]; ring)
private theorem da (x : ℝ) : HasDerivAt a (-2*a x*w x) x :=
  hasDerivAt_thetaCuspModularGapAmplitude x
private theorem dw (x : ℝ) : HasDerivAt w (2+a x/2+2*u x^2/9+2*u x*w x/3) x := by
  convert hasDerivAt_thetaCuspModularTransverseShear x using 1 <;>
    first | rfl | (try dsimp [u,a,w]; ring)
private theorem u_zero : u 0=0 := by simp [u,thetaCuspModularDrift_re_zero]
private theorem w_zero : w 0=0 := by
  simp [w,thetaCuspModularTransverseShear,thetaCuspModularDrift_re_zero,
    thetaCuspModularODEState_Z_zero]
private theorem a_zero : a 0=thetaCuspSelfDualModularScale^2 :=
  thetaCuspModularGapAmplitude_zero
private theorem u_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ u x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [u_zero]
  · exact (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)).le
private theorem w_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ w x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [w_zero]
  · exact (thetaCuspModularTransverseShear_pos_of_pos hx).le
private theorem a_pos (x : ℝ) : 0 < a x := thetaCuspModularGapAmplitude_pos x
private theorem a_lt_twenty {x : ℝ} (hx : 0 ≤ x) : a x < 20 := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [a_zero]; exact thetaCuspSelfDualModularScale_sq_lt_twenty
  · exact (thetaCuspModularGapAmplitude_lt_selfDual_of_pos hx).trans
      thetaCuspSelfDualModularScale_sq_lt_twenty

private theorem u_le_linear {x : ℝ} (hx : x ∈ Icc (0:ℝ) (137/2000)) : u x ≤ 13*x := by
  apply image_le_of_deriv_right_lt_deriv_boundary
    (f:=u) (f':=fun t => -3+u t^2/3+3*a t/4)
    (a:=0) (b:=137/2000)
    (fun t _ => (du t).continuousAt.continuousWithinAt)
    (fun t _ => (du t).hasDerivWithinAt)
    (B:=fun t => 13*t) (B':=fun _ => 13)
    (by rw [u_zero]; norm_num)
    (fun t => by simpa using (hasDerivAt_id t).const_mul (13:ℝ)) ?_ hx
  intro t ht heq
  have ha := a_lt_twenty ht.1
  have hut : 0 ≤ u t := u_nonneg ht.1
  have hu1 : u t ≤ 1 := by rw [heq]; linarith [ht.2]
  have husq : u t^2 ≤ 1 := by nlinarith
  nlinarith

private theorem w_le_linear {x : ℝ} (hx : x ∈ Icc (0:ℝ) (137/2000)) : w x ≤ 14*x := by
  apply image_le_of_deriv_right_lt_deriv_boundary
    (f:=w) (f':=fun t => 2+a t/2+2*u t^2/9+2*u t*w t/3)
    (a:=0) (b:=137/2000)
    (fun t _ => (dw t).continuousAt.continuousWithinAt)
    (fun t _ => (dw t).hasDerivWithinAt)
    (B:=fun t => 14*t) (B':=fun _ => 14)
    (by rw [w_zero]; norm_num)
    (fun t => by simpa using (hasDerivAt_id t).const_mul (14:ℝ)) ?_ hx
  intro t ht heq
  have ha := a_lt_twenty ht.1
  have hu0 := u_nonneg ht.1
  have hut := u_le_linear ⟨ht.1,ht.2.le⟩
  have hu1 : u t ≤ 1 := by linarith [ht.2]
  have husq : u t^2 ≤ 1 := by nlinarith
  have hw0 := w_nonneg ht.1
  have hw1 : w t ≤ 1 := by rw [heq]; linarith [ht.2]
  have huw : u t*w t ≤ 1 := (mul_le_mul_of_nonneg_right hu1 hw0).trans (by simpa using hw1)
  nlinarith

private theorem a_lower {x : ℝ} (hx : x ∈ Icc (0:ℝ) (137/2000)) : 17 ≤ a x := by
  have hf : -a x ≤ 300*x^2+x-a 0 := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f:=fun t => -a t) (f':=fun t => 2*a t*w t)
      (a:=0) (b:=137/2000)
      (fun t _ => (da t).neg.continuousAt.continuousWithinAt)
      (fun t _ => by
        have h := (da t).neg
        have he : -(-2 * a t * w t) = 2 * a t * w t := by ring
        rw [he] at h
        exact h.hasDerivWithinAt)
      (B:=fun t => 300*t^2+t-a 0) (B':=fun t => 600*t+1)
      (by norm_num)
      (fun t => by convert (((hasDerivAt_id t).pow 2).const_mul 300 |>.add (hasDerivAt_id t) |>.sub_const (a 0)) using 1 <;> first | rfl | (try simp only [id_eq]; ring)) ?_ hx
    intro t ht _
    have ha := a_lt_twenty ht.1
    have hw := w_le_linear ⟨ht.1,ht.2.le⟩
    have hw0 := w_nonneg ht.1
    have haw : a t*w t ≤ 20*(14*t) :=
      (mul_le_mul_of_nonneg_right ha.le hw0).trans
        (mul_le_mul_of_nonneg_left hw (by norm_num))
    nlinarith
  have ha0 : 191/10 < a 0 := by
    rw [a_zero]; exact thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  have hx0 := hx.1
  have hx1 := hx.2
  have hxsq : x^2 ≤ (137/2000:ℝ)^2 := by nlinarith
  nlinarith

/-- The actual theta trajectory stays in the D1 certificate box throughout the compact gap. -/
theorem thetaCuspModularLyapunovState_compact_box {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) (137/2000)) :
    -1 ≤ (thetaCuspModularDrift x).re ∧ (thetaCuspModularDrift x).re ≤ 0 ∧
    17 ≤ thetaCuspModularGapAmplitude x ∧ thetaCuspModularGapAmplitude x ≤ 20 ∧
    0 ≤ thetaCuspModularTransverseShear x ∧ thetaCuspModularTransverseShear x ≤ 6/5 := by
  have hu := u_le_linear hx
  have hu0 := u_nonneg hx.1
  have hw := w_le_linear hx
  have hw0 := w_nonneg hx.1
  have ha := a_lower hx
  have ha20 := a_lt_twenty hx.1
  dsimp [u,a,w] at *
  refine ⟨?_,by linarith,ha,ha20.le,hw0,?_⟩ <;> linarith [hx.2]
end RHTower
