import GaloisForLFunctions.RHTower.ThetaFinitePairCurrentCoefficients
import GaloisForLFunctions.RHTower.ThetaTailCenterSourceConvexity

/-! Exact packet limits at the coupled node/source-time boundary. The joint
kernel expansion follows from the continuous divided Schur kernel. -/

noncomputable section
open Set Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "I" => ThetaConfluent.derivativeMass

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

def centerBoundaryMass : ℝ := I/J-c 0/2

theorem centerBoundaryMass_pos : 0 < centerBoundaryMass := by
  have h := div_pos ThetaJoint.center_source_gap_pos ThetaJoint.centerMass_pos
  have he : (2*I-c 0*J)/J=2*centerBoundaryMass := by
    unfold centerBoundaryMass
    field_simp [ThetaJoint.centerMass_pos.ne']
  rw [he] at h
  linarith only [h]

private theorem quadratic_limit {f g : ℝ → ℝ} {d : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : HasDerivAt g d 0) (hz : g 0=0) :
    Tendsto (fun x => (f x-f 0)/x^2) (𝓝[>] 0) (𝓝 (d/2)) := by
  have hq : Tendsto (fun x => g x/x) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add,hz,sub_zero,smul_eq_mul,inv_mul_eq_div] using
      hg.tendsto_slope_zero_right
  have hq' : Tendsto (fun x => g x/(2*x)) (𝓝[>] 0) (𝓝 (d/2)) := by
    convert! hq.div_const 2 using 1
    funext x; ring
  apply HasDerivAt.lhopital_zero_nhdsGT
    (Eventually.of_forall fun x => (hf x).sub_const (f 0))
    (Eventually.of_forall fun x => by
      convert! (hasDerivAt_id x).pow 2 using 1; simp only [id_eq]; ring)
    ?_ ?_ ?_ hq'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (ne_of_gt hx)
  · simpa only [sub_self] using ((hf 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).sub_const (f 0)
  · simpa using (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝[>] 0)).mono_right
      nhdsWithin_le_nhds |>.pow 2

private theorem source_scaled_limit (a : ℝ) :
    Tendsto (fun x => k (a*x)) (𝓝[>] 0) (𝓝 (k 0)) := by
  have hc : Continuous (fun x : ℝ => k (a*x)) :=
    thetaCuspSchwartzReal.continuous.comp (continuous_const.mul continuous_id)
  simpa only [mul_zero] using
    (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

private theorem kernel_scaled_limit (a b : ℝ) :
    Tendsto (fun x => H (a*x) (b*x)) (𝓝[>] 0) (𝓝 J) := by
  have hc : Continuous (fun x : ℝ => H (a*x) (b*x)) :=
    ThetaJoint.source_kernel_continuous.comp
      ((continuous_const.mul continuous_id).prodMk (continuous_const.mul continuous_id))
  simpa only [mul_zero] using
    (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

theorem source_scaled_second_limit (a : ℝ) :
    Tendsto (fun x => (k (a*x)-k 0)/x^2) (𝓝[>] 0) (𝓝 (-c 0*k 0*a^2/2)) := by
  have hf (x : ℝ) : HasDerivAt (fun z => k (a*z)) (-a*p (a*x)*k (a*x)) x := by
    convert! (actualSource_hasDerivAt (a*x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1
    ring
  have hp : HasDerivAt (fun x => p (a*x)) (c 0*a) 0 := by
    convert! (hasDerivAt_thetaCuspLogDecaySlope (a*0)).comp 0
      ((hasDerivAt_id (0:ℝ)).const_mul a) using 1
    simp only [mul_zero,mul_one]
  have hk : HasDerivAt (fun x => k (a*x)) 0 0 := by
    simpa only [mul_zero,p_zero,zero_mul] using hf 0
  have hg : HasDerivAt (fun x => -a*p (a*x)*k (a*x)) (-c 0*k 0*a^2) 0 := by
    convert! (hp.const_mul (-a)).mul hk using 1
    simp only [mul_zero,add_zero]
    ring
  convert! quadratic_limit hf hg (by simp only [mul_zero,p_zero,zero_mul]) using 1
  simp only [mul_zero]

theorem axis_scaled_second_limit (a : ℝ) :
    Tendsto (fun x => (H 0 (a*x)-J)/x^2) (𝓝[>] 0) (𝓝 (-I*a^2)) := by
  have hf (x : ℝ) : HasDerivAt (fun z => H 0 (a*z))
      (a*ThetaJoint.firstLeft (a*x) 0) x := by
    convert! (ThetaJoint.source_hasDerivAt_right 0 (a*x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1
    ring
  have hg : HasDerivAt (fun x => a*ThetaJoint.firstLeft (a*x) 0) (-2*I*a^2) 0 := by
    convert! ((ThetaJoint.firstLeft_hasDerivAt_left (a*0) 0).comp 0
      ((hasDerivAt_id (0:ℝ)).const_mul a)).const_mul a using 1
    simp only [mul_zero,mul_one,ThetaJoint.secondLeft_origin]
    ring
  have h := quadratic_limit hf hg (by simp only [mul_zero,ThetaJoint.firstLeft_origin])
  have he : -2*I*a^2/2=-I*a^2 := by ring
  simpa only [mul_zero,he] using h

/-- Joint second jets at every fixed pair of scaling directions, including the axes. -/
theorem kernel_scaled_second_limit (a b : ℝ) :
    Tendsto (fun x => (H (a*x) (b*x)-J)/x^2) (𝓝[>] 0)
      (𝓝 (-I*(a-b)^2-k 0^2*a*b)) := by
  have hs : Tendsto (fun x => ThetaJoint.dividedSchur (a*x) (b*x))
      (𝓝[>] 0) (𝓝 ThetaConfluent.centerEntry) := by
    have hpath : Continuous (fun x : ℝ => (a*x,b*x)) :=
      (continuous_const.mul continuous_id).prodMk (continuous_const.mul continuous_id)
    have hc := ThetaJoint.dividedSchur_continuous.comp hpath
    convert! (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds using 1
    simp only [Function.comp_apply,mul_zero,ThetaJoint.dividedSchur_origin]
  have h := (((axis_scaled_second_limit a).mul
    ((kernel_scaled_limit 0 b).div_const J)).add (axis_scaled_second_limit b)).add
      (hs.const_mul (a*b))
  have he : (-I*a^2)*(J/J)+(-I*b^2)+(a*b)*ThetaConfluent.centerEntry=
      -I*(a-b)^2-k 0^2*a*b := by
    unfold ThetaConfluent.centerEntry
    field_simp [ThetaJoint.centerMass_pos.ne']
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  have hS := ThetaJoint.dividedSchur_product (a*x) (b*x)
  unfold ThetaJoint.centerSchur at hS
  have hK : H (a*x) (b*x)=H 0 (a*x)*H 0 (b*x)/J+
      (a*x)*(b*x)*ThetaJoint.dividedSchur (a*x) (b*x) := by linarith only [hS]
  simp only [zero_mul]
  rw [hK]
  field_simp [hx0.ne',ThetaJoint.centerMass_pos.ne']
  ring

theorem normalizedPacket_boundary_ratio_limit (r : ℝ) :
    Tendsto (fun x => normalizedPacket x (r*x)/x) (𝓝[>] 0)
      (𝓝 (centerBoundaryMass-c 0*r)) := by
  have hr := source_scaled_limit r
  have hr1 := source_scaled_limit (r+1)
  have hn := ((((source_scaled_second_limit r).mul hr1).add
    ((source_scaled_second_limit (r+1)).const_mul (k 0))).sub
      ((axis_scaled_second_limit 1).mul ((hr.pow 2).div_const J))).sub
        ((source_scaled_second_limit r).mul (hr.add_const (k 0)))
  have h := hn.div (hr.mul hr1) (mul_ne_zero (thetaCuspFullSource_pos_all 0).ne'
        (thetaCuspFullSource_pos_all 0).ne')
  have he : (((-c 0*k 0*r^2/2)*k 0+k 0*(-c 0*k 0*(r+1)^2/2))-
      (-I*(1:ℝ)^2)*(k 0^2/J)-(-c 0*k 0*r^2/2)*(k 0+k 0))/(k 0*k 0)=
        centerBoundaryMass-c 0*r := by
    unfold centerBoundaryMass
    field_simp [ThetaJoint.centerMass_pos.ne',(thetaCuspFullSource_pos_all 0).ne']
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  unfold normalizedPacket
  simp only [Pi.div_apply,one_mul,add_mul]
  rw [add_comm x (r*x)]
  have hk := (thetaCuspFullSource_pos_all (r*x)).ne'
  have hl := (thetaCuspFullSource_pos_all (r*x+x)).ne'
  generalize k (r*x)=K at hk ⊢
  generalize k (r*x+x)=L at hl ⊢
  field_simp [hx0.ne',ThetaJoint.centerMass_pos.ne',hk,hl]
  ring

theorem transportPrimitive_boundary_ratio_limit (r : ℝ) :
    Tendsto (fun x => transportPrimitive x (r*x)/x) (𝓝[>] 0) (𝓝 r) := by
  have hr := source_scaled_limit r
  have hr1 := source_scaled_limit (r+1)
  have hn := ((((axis_scaled_second_limit 1).div_const J).mul (kernel_scaled_limit r r)).add
    (kernel_scaled_second_limit r r)).sub (kernel_scaled_second_limit r (r+1))
  have h := hn.div (hr.mul hr1) (mul_ne_zero (thetaCuspFullSource_pos_all 0).ne'
        (thetaCuspFullSource_pos_all 0).ne')
  have he : ((-I*(1:ℝ)^2/J)*J+(-I*(r-r)^2-k 0^2*r*r)-
      (-I*(r-(r+1))^2-k 0^2*r*(r+1)))/(k 0*k 0)=r := by
    field_simp [ThetaJoint.centerMass_pos.ne',(thetaCuspFullSource_pos_all 0).ne']
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  unfold transportPrimitive
  rw [prefixBalance_eq_tail]
  simp only [Pi.div_apply,one_mul,add_mul]
  rw [add_comm x (r*x)]
  field_simp [hx0.ne',ThetaJoint.centerMass_pos.ne',
    (thetaCuspFullSource_pos_all (r*x)).ne',(thetaCuspFullSource_pos_all (r*x+x)).ne']
  ring

end RHTower.ThetaFiniteTransport
