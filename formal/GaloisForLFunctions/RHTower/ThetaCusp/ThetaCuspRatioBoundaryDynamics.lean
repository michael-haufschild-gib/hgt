import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioDefectMonotonicity
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # Complete-source selection of the critical third-slope boundary direction. -/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology


theorem k_tendsto_atTop : Tendsto k atTop atTop := by
  let c : ℝ := 2*(k 1+1/3)*J 1
  have hc : 0<c := by
    have hk := k_gt (show (0:ℝ)≤1 by norm_num)
    have hj := J_pos (show (0:ℝ)<1 by norm_num)
    dsimp [c]
    positivity
  have hderiv (x : ℝ) (hx : 1≤x) : c≤2*(k x+1/3)*J x := by
    have hx0 : 0≤x := by linarith
    have hk := k_mono (show (0:ℝ)≤1 by norm_num) hx0 hx
    have hj := J_strictMonoOn.monotoneOn (show (1:ℝ)∈Ici 0 by norm_num) hx0 hx
    have hj0 := J_nonneg (show (0:ℝ)≤1 by norm_num)
    dsimp [c]
    gcongr
    linarith [k_gt (show (0:ℝ)≤1 by norm_num)]
  have hm : MonotoneOn (fun x => k x-c*x) (Ici 1) := by
    have hd (x : ℝ) (hx : 1≤x) : HasDerivAt (fun y => k y-c*y)
        (2*(k x+1/3)*J x-c) x := by
      convert (dk (show 0≤x by linarith)).sub ((hasDerivAt_id x).const_mul c) using 1 <;>
        first | rfl | simp
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (show 1≤x from
        (show 1<x by simpa only [interior_Ici,mem_Ioi] using hx).le)).differentiableAt.differentiableWithinAt)
    intro x hx
    have h1 : 1≤x := (show 1<x by simpa only [interior_Ici,mem_Ioi] using hx).le
    rw [(hd x h1).deriv]
    exact sub_nonneg.mpr (hderiv x h1)
  apply tendsto_atTop_atTop.2
  intro B
  refine ⟨max 1 (1+(B-k 1)/c),?_⟩
  intro x hx
  have hx1 : 1≤x := (le_max_left _ _).trans hx
  have hxB := (le_max_right 1 (1+(B-k 1)/c)).trans hx
  have hdiv : (B-k 1)/c≤x-1 := by linarith only [hxB]
  have he := (div_le_iff₀ hc).mp hdiv
  have hi := hm (show (1:ℝ)∈Ici 1 by simp) hx1 hx1
  nlinarith only [he,hi]

theorem inverse_k_tendsto_zero : Tendsto (fun x => (k x)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp k_tendsto_atTop

theorem t_tendsto_zero : Tendsto t atTop (𝓝 0) := by
  have hlim : Tendsto (fun x => (361/25:ℝ)*((k x)⁻¹)^2) atTop (𝓝 0) := by
    simpa using inverse_k_tendsto_zero.pow 2 |>.const_mul (361/25:ℝ)
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact (t_pos hx).le
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    have hk : 0<k x := lt_trans (by norm_num) (k_gt hx)
    have he := mul_le_mul_of_nonneg_right (kineticGap_lt hx).le
      (sq_nonneg ((k x)⁻¹))
    have hi : k x^2*t x*((k x)⁻¹)^2=t x := by field_simp [hk.ne']
    rwa [hi] at he

/-- The quotient of the two vanishing compactified source coordinates. -/
def boundaryRatio (x : ℝ) : ℝ := (u x-3*J x)/(u x*k x*t x)

def boundaryError (x : ℝ) : ℝ :=
  3/k x+4/(3*k x^2)-5*t x*boundaryRatio x+
  (2/3)*u x^2*boundaryRatio x/k x-
  (2/9)*u x^2*boundaryRatio x/k x^2+
  (2/3)*u x^2*(1+1/(3*k x))*boundaryRatio x^2*t x

theorem boundaryRatio_nonneg {x : ℝ} (hx : 0<x) : 0≤boundaryRatio x := by
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hk : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
  have ht := t_pos hx.le
  have hj := J_le_third_drift hx.le
  exact div_nonneg (by linarith) (by positivity)

theorem boundaryRatio_velocity {x : ℝ} (hx : 0<x) :
    defectVelocity x=t x*(k x^2-2*k x/3-4/9-
      (2/3)*u x^2*k x*(k x+2/3)*boundaryRatio x) := by
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have ht : t x≠0 := (t_pos hx.le).ne'
  unfold defectVelocity boundaryRatio
  field_simp [hu,hk,ht]
  dsimp [t]
  ring

theorem boundaryRatio_lt {x : ℝ} (hx : 0<x) : boundaryRatio x<3/(2*u x^2) := by
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hk : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
  have ht := t_pos hx.le
  have hq := boundaryRatio_nonneg hx
  have hF := defectVelocity_pos hx
  rw [boundaryRatio_velocity hx] at hF
  have hinner := (mul_pos_iff_of_pos_left ht).mp hF
  have hp : 0≤(4/9)*u x^2*k x*boundaryRatio x := by positivity
  have hproduct : k x^2*((2/3)*u x^2*boundaryRatio x)<k x^2 := by
    nlinarith only [hinner,hp,hk]
  have hratio : (2/3)*u x^2*boundaryRatio x<1 := by
    nlinarith only [hproduct,sq_pos_of_pos hk]
  apply (lt_div_iff₀ (show 0<2*u x^2 by positivity)).mpr
  nlinarith only [hratio]

theorem dBoundaryRatio {x : ℝ} (hx : 0<x) :
    HasDerivAt boundaryRatio ((k x/u x)*(36*(boundaryRatio x-1/12)+boundaryError x)) x := by
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have ht : t x≠0 := (t_pos hx.le).ne'
  have hd := ((du hx.le).sub ((dJ hx.le).const_mul 3)).div
    (((du hx.le).mul (dk hx.le)).mul (dt hx.le)) (mul_ne_zero (mul_ne_zero hu hk) ht)
  convert hd using 1 <;> first | rfl | skip
  simp only [Pi.mul_apply,Pi.sub_apply,Pi.div_apply,boundaryError,boundaryRatio,D]
  field_simp [hu,hk,ht]
  simp only [t]
  ring

end
end RHTower.ThetaCuspModularRatio
