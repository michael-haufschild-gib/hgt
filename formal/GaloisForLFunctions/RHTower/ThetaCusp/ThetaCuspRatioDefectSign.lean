import Mathlib.Tactic

/-! # Negative acceleration at nonpositive ratio-defect speed

An exact polynomial identity gives a strict sign throughout the actual-source
ratio cone. The complete-source consequence is proved in the companion leaf.
-/

namespace RHTower.ThetaRatioDefectSlope
noncomputable section

def speed (u k z : ℝ) : ℝ :=
  k^2*(9-u^2)-6*k-4+2*u^2*(k+2/3)*z

def acceleration (u k z : ℝ) : ℝ := u*
  ((9-u^2)*k*z*(6*k+8/3)-2*k^3*(9-u^2)-12*(k+1/3)*z+
    4*u^2*(k+1/3)*z^2+2*(k+2/3)*speed u k z)

private def B (k z : ℝ) : ℝ := k^2-2*(k+2/3)*z
private def C (k z : ℝ) : ℝ := -k^2*(3*k+2)+z*(6*k^2+9*k+8/3)
private def L (k z : ℝ) : ℝ :=
  4*k^2/3+(2*k^2-8*k/3-16/9)*z-4*(k+1/3)*z^2

private theorem base_pos {k : ℝ} (hk : 5/4<k) : 0<k^2-2*k/3-4/9 := by
  have hs : 0<k-5/4 := by linarith only [hk]
  have h : 0<(k-5/4)^2+(11/6)*(k-5/4)+41/144 := by positivity
  nlinarith only [h]

private theorem B_pos {k z : ℝ} (hk : 5/4<k) (hz : z≤1/3) : 0<B k z := by
  have hm := mul_le_mul_of_nonneg_left hz (show 0≤2*(k+2/3) by linarith only [hk])
  have hb := base_pos hk
  unfold B
  nlinarith only [hm,hb]

private theorem C_neg {k z : ℝ} (hk : 5/4<k) (hz : z≤1/3) : C k z<0 := by
  have hk0 : 0<k := by linarith only [hk]
  have hs : 0<k-5/4 := by linarith only [hk]
  have hc : 0≤6*k^2+9*k+8/3 := by positivity
  have hm := mul_le_mul_of_nonneg_right hz hc
  have hp : 0<3*(k-5/4)^3+(45/4)*(k-5/4)^2+(177/16)*(k-5/4)+703/576 := by positivity
  unfold C
  nlinarith only [hm,hp]

private theorem L_nonneg {k z : ℝ} (hk : 5/4<k) (hz0 : 0≤z) (hz1 : z≤1/3) :
    0≤L k z := by
  have hs : 0<k-5/4 := by linarith only [hk]
  have h1 : 0≤2*k^2-4*k/3-20/27 := by
    have hp : 0<2*(k-5/4)^2+(11/3)*(k-5/4)+155/216 := by positivity
    nlinarith only [hp]
  have he : L k z = (1-3*z)*(4*k^2/3)+3*z*(2*k^2-4*k/3-20/27)+
      4*(k+1/3)*z*(1/3-z) := by unfold L; ring
  rw [he]
  have hza : 0≤1-3*z := by linarith only [hz1]
  have hzb : 0≤1/3-z := by linarith only [hz1]
  have hk0 : 0≤k+1/3 := by linarith only [hk]
  positivity

/-- The entire admissible source cone has inward-negative acceleration at nonpositive speed. -/
theorem acceleration_neg {u k z : ℝ} (hu : 0<u) (ht : 0<9-u^2)
    (hk : 5/4<k) (hz0 : 0≤z) (hz1 : z≤1/3) (hf : speed u k z≤0) :
    acceleration u k z<0 := by
  have hz : z<1/3 := by
    rcases hz1.eq_or_lt with he | he
    · subst z
      have hp := mul_pos ht (base_pos hk)
      unfold speed at hf
      nlinarith only [hp,hf]
    · exact he
  have he : B k z*acceleration u k z =
      u*(4*k*(1-3*z)*C k z+speed u k z*L k z) := by
    unfold B C L acceleration speed
    ring
  have hk0 : 0<k := by linarith only [hk]
  have hza : 0<1-3*z := by linarith only [hz]
  have hc := mul_neg_of_pos_of_neg (show 0<4*k*(1-3*z) by positivity) (C_neg hk hz1)
  have hl := mul_nonpos_of_nonpos_of_nonneg hf (L_nonneg hk hz0 hz1)
  have hp := mul_neg_of_pos_of_neg hu (add_neg_of_neg_of_nonpos hc hl)
  rw [← he] at hp
  have hb := B_pos hk hz1
  nlinarith only [hb,hp]

end
end RHTower.ThetaRatioDefectSlope
