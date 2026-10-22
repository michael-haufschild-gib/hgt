import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticBoundaryPolynomial
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticBarrierBranch

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

theorem boundaryPoly_upper {h w : ℝ} (hh0 : 0≤h) (hh : h≤2/3)
    (hw0 : 0≤w) (hw : w≤1/6) : boundaryPoly h w≤pTail h+w*pWUpper h := by
  have hs : h^2≤4/9 := by nlinarith
  have hc : 0≤1/9-h/36-7*h^2/324 := by linarith
  have he : pTail h+w*pWUpper h-boundaryPoly h w=
      w^2*(1/2+7*h^3/324)+w*(1/6-w)*(71*h/108+17*h^2/81)+
        w^3*(1/9-h/36-7*h^2/324) := by
    unfold pTail pWUpper boundaryPoly boundaryC0 boundaryC1 boundaryC2 boundaryC3 b
    ring
  have hp : 0≤w^2*(1/2+7*h^3/324)+w*(1/6-w)*(71*h/108+17*h^2/81)+
        w^3*(1/9-h/36-7*h^2/324) := by positivity
  linarith only [he,hp]

theorem pWUpper_nonneg {h : ℝ} (hh0 : 0≤h) (hh : h≤2/3) : 0≤pWUpper h := by
  have hs : h^2≤4/9 := by nlinarith
  have hc : h^3≤8/27 := by nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg h)]
  unfold pWUpper
  nlinarith only [hh0,hs,hc,sq_nonneg h]

theorem low_clock_certificate {h : ℝ} (hh0 : 0<h) (hh : h≤2/3) :
    pTail h+18*h^2*b h*pWUpper h<0 := by
  let a : ℝ := 3*h/2
  let d : ℝ := 1-a
  have ha : 0<a := by dsimp [a]; positivity
  have hd : 0≤d := by dsimp [d,a]; linarith
  have he : pTail h+18*h^2*b h*pWUpper h =
      -h*((7/16)*d^5+(157/108)*a*d^4+(3071/1944)*a^2*d^3+
        (2347/2916)*a^3*d^2+(103015/314928)*a^4*d+(4195/157464)*a^5) := by
    dsimp [a,d,pTail,pWUpper,b]
    ring
  rw [he]
  have hp : 0<(7/16)*d^5+(157/108)*a*d^4+(3071/1944)*a^2*d^3+
        (2347/2916)*a^3*d^2+(103015/314928)*a^4*d+(4195/157464)*a^5 := by positivity
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hh0) hp

theorem low_boundary_polynomial_neg {h w : ℝ} (hh0 : 0<h) (hh : h≤2/3)
    (hw0 : 0≤w) (hw : w≤1/6)
    (hk : w*(1-w)≤(361/25)*h^2*b h) : boundaryPoly h w<0 := by
  have hb := b_nonneg (show h≤4/5 by linarith)
  have hhb : 0≤h^2*b h := mul_nonneg (sq_nonneg h) hb
  have hl := mul_le_mul_of_nonneg_left (show (5/6:ℝ)≤1-w by linarith) hw0
  have hwb : w≤18*h^2*b h := by nlinarith only [hk,hl,hhb]
  calc
    _ ≤ pTail h+w*pWUpper h := boundaryPoly_upper hh0.le hh hw0 hw
    _ ≤ pTail h+(18*h^2*b h)*pWUpper h := by
      gcongr
      exact pWUpper_nonneg hh0.le hh
    _ < 0 := low_clock_certificate hh0 hh

end
end HTGeometry.ThetaCriticalBarrier
namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

theorem quadratic_boundary_force_neg_low {h v q : ℝ} (hh0 : 0<h) (hh : h≤2/3)
    (hv0 : 0<v) (hv : v≤9) (hq : 0≤q)
    (hy : quadraticError h v q=0) (hg : (9-v)*q<h)
    (hk : 9-v≤(361/25)*h^2) : quadraticBoundaryCore h v q<0 := by
  let w : ℝ := (9-v)*q
  have hw0 : 0≤w := by dsimp [w]; positivity
  have hw : w<1/6 := failure_small_branch hh0.le (by linarith) hv0 hv hq hy.le hg hk
  have hw1 : 0<1-w := by linarith
  have hqw : q*(1-w)=b h := by
    dsimp [w]
    unfold quadraticError at hy
    nlinarith only [hy]
  have hb : 0<b h := by unfold b; linarith
  have hqeq : q=b h/(1-w) := (eq_div_iff hw1.ne').2 hqw
  have hwkin : w*(1-w)=(9-v)*b h := by
    dsimp [w]
    linear_combination (9-v)*hqw
  have hveq : v=9-w*(1-w)/b h := by
    rw [hwkin]
    field_simp [hb.ne']
    ring
  have hpb : w*(1-w)≤(361/25)*h^2*b h := by
    rw [hwkin]
    exact mul_le_mul_of_nonneg_right hk hb.le
  have hp := low_boundary_polynomial_neg hh0 hh hw0 hw.le hpb
  have he := boundary_core_polynomial h w hb.ne' hw1.ne'
  rw [←hveq,←hqeq] at he
  have hsq : 0<(1-w)^2 := by positivity
  by_contra hn
  have hn0 : 0≤quadraticBoundaryCore h v q := le_of_not_gt hn
  have hn1 := mul_nonneg hsq.le hn0
  linarith only [he,hp,hn1]

theorem quadratic_boundary_field_neg_low {h v q : ℝ} (hh0 : 0<h) (hh : h≤2/3)
    (hv0 : 0<v) (hv : v<9) (hq : 0≤q)
    (hy : quadraticError h v q=0) (hg : (9-v)*q<h)
    (hk : 9-v≤(361/25)*h^2) : quadraticField h v q<0 := by
  rw [quadraticField_split,hy,mul_zero,add_zero]
  have hr := quadratic_boundary_force_neg_low hh0 hh hv0 hv.le hq hy hg hk
  exact mul_neg_of_pos_of_neg (by linarith) hr

end
end HTGeometry.ThetaCriticalBarrier
