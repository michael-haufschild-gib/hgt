import Mathlib.Tactic

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

def b (h : ℝ) : ℝ := 1/12-7*h/72
def D (h v : ℝ) : ℝ := 4*h^2/27+31*h/72-5/12+v*(1+h/3)*b h/18
def Dh (h v : ℝ) : ℝ := 8*h/27+31/72-v*(5/1296+7*h/1944)
def Dv (h : ℝ) : ℝ := (1+h/3)*b h/18
def G (h v q : ℝ) : ℝ :=
  36*(q-1/12)+3*h+4*h^2/3-5*(9-v)*q+(2/3)*v*q*h-(2/9)*v*q*h^2+
    (2/3)*v*(1+h/3)*q^2*(9-v)-(7/108)*v*h^2*(1+h/3)+
    (7/108)*v*h*(1+h/3)*q*(9-v)
def A (h v q : ℝ) : ℝ :=
  36-5*(9-v)+(2/9)*v*h*(3-h)+
    (2/3)*v*(1+h/3)*(9-v)*(q+b h)+(7/108)*v*h*(1+h/3)*(9-v)
def fieldH (h v q : ℝ) : ℝ := -(4/3)*h*(3+h)*v*(h-q*(9-v))
def fieldV (v : ℝ) : ℝ := 12*v*(9-v)
def fieldD (h v q : ℝ) : ℝ := Dh h v*fieldH h v q+Dv h*fieldV v

theorem G_boundary (h v : ℝ) : G h v (b h)=(9-v)*D h v := by
  unfold G D b
  ring

theorem G_split (h v q : ℝ) : G h v q=(9-v)*D h v+(q-b h)*A h v q := by
  unfold G D A b
  ring

theorem fieldD_boundary (h v : ℝ) :
    fieldD h v (b h)=
      -(2/9)*v*(3+h)*(6*h*(h-b h*(9-v))*Dh h v-(9-v)*b h) := by
  unfold fieldD fieldH fieldV Dv
  ring

theorem b_nonneg {h : ℝ} (hh : h≤4/5) : 0≤b h := by unfold b; linarith
theorem b_le {h : ℝ} (hh : 0≤h) : b h≤1/12 := by unfold b; linarith
theorem b_le_high {h : ℝ} (hh : 2/3≤h) : b h≤1/54 := by unfold b; linarith

/-- The boundary forcing is strictly negative throughout the lower clock interval. -/
theorem D_neg_low {h v : ℝ} (hh0 : 0≤h) (hh : h≤2/3) (hv0 : 0≤v) (hv : v≤9) :
    D h v<0 := by
  have hb0 := b_nonneg (show h≤4/5 by linarith)
  have hb1 := b_le hh0
  have hf0 : 0≤1+h/3 := by linarith
  have hf1 : 1+h/3≤11/9 := by linarith
  have hs : h^2≤4/9 := by nlinarith
  have hprod : v*(1+h/3)*b h≤9*(11/9)*(1/12) := by
    gcongr
  unfold D
  linarith

theorem Dh_pos_high {h v : ℝ} (hh0 : 2/3≤h) (hh : h≤4/5) (hv0 : 0≤v) (hv : v≤9) :
    1/2<Dh h v := by
  have ht0 : 0≤5/1296+7*h/1944 := by linarith
  have ht1 : 5/1296+7*h/1944≤5/1296+7*(4/5)/1944 := by linarith
  have hm : v*(5/1296+7*h/1944)≤9*(5/1296+7*(4/5)/1944) := by gcongr
  unfold Dh
  linarith

/-- While the ratio lies below the affine barrier, the forcing crosses zero only downward. -/
theorem fieldD_neg_high {h v q : ℝ} (hh0 : 2/3≤h) (hh : h≤4/5)
    (hv0 : 0<v) (hv : v≤9) (hq : q≤b h) : fieldD h v q<0 := by
  have hT0 : 0≤9-v := by linarith
  have hT1 : 9-v≤9 := by linarith
  have hb0 := b_nonneg hh
  have hb1 := b_le_high hh0
  have hm : (9-v)*b h≤1/6 := by
    have hm0 := mul_le_mul hT1 hb1 hb0 (show (0:ℝ)≤9 by norm_num)
    norm_num at hm0
    exact hm0
  have hgap : 1/2≤h-b h*(9-v) := by nlinarith only [hh0,hm]
  have hd := Dh_pos_high hh0 hh hv0.le hv
  have hp : 1≤6*h*(h-b h*(9-v))*Dh h v := by
    calc
      _ = 6*(2/3:ℝ)*(1/2)*(1/2) := by norm_num
      _ ≤ _ := by gcongr
  have hs : 0<6*h*(h-b h*(9-v))*Dh h v-(9-v)*b h := by linarith
  have hf : fieldD h v (b h)<0 := by
    rw [fieldD_boundary]
    have hh3 : 0<3+h := by linarith
    have hn : -(2/9)*v*(3+h)<0 := by
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hv0) hh3
    exact mul_neg_of_neg_of_pos hn hs
  have hqT := mul_le_mul_of_nonneg_right hq hT0
  have hcoef : 0≤(4/3)*h*(3+h)*v := by positivity
  have hfH : fieldH h v q≤fieldH h v (b h) := by
    unfold fieldH
    nlinarith only [mul_le_mul_of_nonneg_left hqT hcoef]
  have hle : fieldD h v q≤fieldD h v (b h) := by
    unfold fieldD
    have hd0 : 0≤Dh h v := by linarith only [hd]
    simpa only [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_left hfH hd0) (Dv h*fieldV v)
  exact hle.trans_lt hf

theorem fieldD_neg_at_zero {h v q : ℝ} (hh0 : 0≤h) (hh : h≤4/5)
    (hv0 : 0<v) (hv : v≤9) (hq : q≤b h) (hD : D h v=0) : fieldD h v q<0 := by
  have hh2 : 2/3<h := by
    by_contra hn
    have := D_neg_low hh0 (le_of_not_gt hn) hv0.le hv
    linarith
  exact fieldD_neg_high hh2.le hh hv0 hv hq

theorem A_pos_tail {h v q : ℝ} (hh0 : 0≤h) (hh : h≤2/3)
    (hv0 : 8≤v) (hv : v≤9) (hq : 0≤q) : 30≤A h v q := by
  have hb0 := b_nonneg (show h≤4/5 by linarith)
  have hvn : 0≤v := by linarith
  have hT : 0≤9-v := by linarith
  have hh3 : 0≤3-h := by linarith
  have hh1 : 0≤1+h/3 := by linarith
  have hqb : 0≤q+b h := by linarith
  have hp1 : 0≤(2/9)*v*h*(3-h) := by positivity
  have hp2 : 0≤(2/3)*v*(1+h/3)*(9-v)*(q+b h) := by positivity
  have hp3 : 0≤(7/108)*v*h*(1+h/3)*(9-v) := by positivity
  unfold A
  linarith


end
end HTGeometry.ThetaCriticalBarrier
