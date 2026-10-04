import GaloisForLFunctions.RHTower.ThetaFinitePairBoundaryPackets

/-! The actual canonical current has a negative boundary layer when source time
and node spacing approach zero together. No interchange of improper limits is
asserted by the fixed-scaling theorem. -/

noncomputable section
open Set MeasureTheory Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]
private theorem v_zero : v 0=0 := by
  simp only [thetaCuspLogCurvatureJet,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1,rfl⟩,neg_zero]

private theorem cont_p : Continuous p := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
private theorem cont_c : Continuous c := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvature t).continuousAt
private theorem cont_v : Continuous v := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvatureJet t).continuousAt

private theorem average_boundary_limit (n : ℕ) {f : ℝ → ℝ} (hf : Continuous f) (r : ℝ) :
    Tendsto (fun x => ∫ u in (0:ℝ)..1, u^n*f (r*x+u*x))
      (𝓝[>] 0) (𝓝 (f 0/(n+1))) := by
  have hc : Continuous (fun x : ℝ => ∫ u in (0:ℝ)..1, u^n*f (r*x+u*x)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (continuous_snd.pow n).mul
      (hf.comp ((continuous_const.mul continuous_fst).add
        (continuous_snd.mul continuous_fst)))
  have he : (∫ u in (0:ℝ)..1, u^n*f (r*0+u*0))=f 0/(n+1) := by
    simp only [mul_zero,add_zero,intervalIntegral.integral_mul_const,integral_pow,
      one_pow,zero_pow (Nat.succ_ne_zero _),sub_zero]
    ring
  simpa only [he] using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

private theorem secant_boundary_limit (r : ℝ) :
    Tendsto (fun x => smoothSecant x (r*x)) (𝓝[>] 0) (𝓝 (c 0)) := by
  change Tendsto (fun x => ∫ u in (0:ℝ)..1, u^0*c (r*x+u*x)) _ _
  simpa only [Nat.cast_zero,zero_add,div_one] using average_boundary_limit 0 cont_c r

private theorem secantTime_boundary_limit (r : ℝ) :
    Tendsto (fun x => smoothSecantTimeJet x (r*x)) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
  change Tendsto (fun x => ∫ u in (0:ℝ)..1, u^0*v (r*x+u*x)) _ _
  simpa only [v_zero,zero_div] using average_boundary_limit 0 cont_v r

private theorem secantNode_boundary_limit (r : ℝ) :
    Tendsto (fun x => smoothSecantNodeJet x (r*x)) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
  change Tendsto (fun x => ∫ u in (0:ℝ)..1, u^1*v (r*x+u*x)) _ _
  simpa only [v_zero,zero_div] using average_boundary_limit 1 cont_v r

private theorem p_linear_limit (a : ℝ) :
    Tendsto (fun x => p (a*x)/x) (𝓝[>] 0) (𝓝 (c 0*a)) := by
  have hp : HasDerivAt (fun x => p (a*x)) (c 0*a) 0 := by
    convert! (hasDerivAt_thetaCuspLogDecaySlope (a*0)).comp 0
      ((hasDerivAt_id (0:ℝ)).const_mul a) using 1
    simp only [mul_zero,mul_one]
  simpa only [zero_add,mul_zero,p_zero,sub_zero,smul_eq_mul,inv_mul_eq_div] using
    hp.tendsto_slope_zero_right

private theorem p_boundary_limit (a : ℝ) :
    Tendsto (fun x => p (a*x)) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
  have hc : Continuous (fun x : ℝ => p (a*x)) :=
    cont_p.comp (continuous_const.mul continuous_id)
  simpa only [mul_zero,p_zero] using
    (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

private theorem c_boundary_limit (a : ℝ) :
    Tendsto (fun x => c (a*x)) (𝓝[>] 0) (𝓝 (c 0)) := by
  have hc : Continuous (fun x : ℝ => c (a*x)) :=
    cont_c.comp (continuous_const.mul continuous_id)
  simpa only [mul_zero] using
    (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

private theorem speed_boundary_limit {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun x => diagonalSpeed x (r*x)) (𝓝[>] 0) (𝓝 (r/(2*(r+1)))) := by
  have hp : 0 < r+1 := by linarith only [hr]
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1/2:ℝ)) (𝓝[>] 0) (𝓝 (1/2))).sub
    ((p_linear_limit 1).div ((p_linear_limit (r+1)).const_mul 2)
      (mul_pos (by norm_num : (0:ℝ)<2) (mul_pos (thetaCuspLogCurvature_pos 0) hp)).ne')
  have he : (1/2:ℝ)-(c 0*1)/(2*(c 0*(r+1)))=r/(2*(r+1)) := by
    field_simp [(thetaCuspLogCurvature_pos 0).ne',hp.ne']
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  unfold diagonalSpeed
  simp only [Pi.div_apply,one_mul]
  rw [show r*x+x=(r+1)*x by ring]
  field_simp [hx0.ne',(ThetaSturmCrossing.slope_pos (mul_pos hp hx0)).ne']

private theorem speedTime_boundary_limit {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun x => x*diagonalSpeedTimeJet x (r*x)) (𝓝[>] 0)
      (𝓝 (1/(2*(r+1)^2))) := by
  have hp : 0 < r+1 := by linarith only [hr]
  have h := ((p_linear_limit 1).mul (c_boundary_limit (r+1))).div
    (((p_linear_limit (r+1)).pow 2).const_mul 2)
      (mul_pos (by norm_num : (0:ℝ)<2)
        (sq_pos_of_pos (mul_pos (thetaCuspLogCurvature_pos 0) hp))).ne'
  have he : (c 0*1)*c 0/(2*(c 0*(r+1))^2)=1/(2*(r+1)^2) := by
    field_simp [(thetaCuspLogCurvature_pos 0).ne',hp.ne']
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  unfold diagonalSpeedTimeJet
  simp only [Pi.div_apply,one_mul]
  rw [show r*x+x=(r+1)*x by ring]
  field_simp [hx0.ne',(ThetaSturmCrossing.slope_pos (mul_pos hp hx0)).ne']

private theorem packetCoefficient_boundary_limit {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun x => x*diagonalPacketCoefficient x (r*x)) (𝓝[>] 0)
      (𝓝 (-1/(2*(r+1)^2))) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have h := ((((speed_boundary_limit hr).neg.mul
    ((hx.pow 2).const_mul (1+2*r))).mul (secant_boundary_limit r))).sub
      (speedTime_boundary_limit hr)
  have he : -(r/(2*(r+1)))*((1+2*r)*(0:ℝ)^2)*c 0-1/(2*(r+1)^2)=
      -1/(2*(r+1)^2) := by ring
  rw [he] at h
  apply h.congr'
  exact Eventually.of_forall fun x => by
    unfold diagonalPacketCoefficient
    ring

private theorem primitiveCoefficient_boundary_limit {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun x => x*diagonalPrimitiveCoefficient x (r*x)) (𝓝[>] 0)
      (𝓝 (-c 0/(2*(r+1)^2))) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have h := ((hx.mul (secantNode_boundary_limit r)).sub
    ((speed_boundary_limit hr).mul (hx.mul (secantTime_boundary_limit r)))).sub
      ((((speed_boundary_limit hr).mul (hx.mul
        ((p_boundary_limit r).add (p_boundary_limit (r+1))))).add
          (speedTime_boundary_limit hr)).mul (secant_boundary_limit r))
  have he : ((0:ℝ)*0-r/(2*(r+1))*(0*0))-
      (r/(2*(r+1))*(0*(0+0))+1/(2*(r+1)^2))*c 0=-c 0/(2*(r+1)^2) := by ring
  rw [he] at h
  apply h.congr'
  exact Eventually.of_forall fun x => by
    unfold diagonalPrimitiveCoefficient
    dsimp only
    rw [show r*x+x=(r+1)*x by ring]
    ring

/-- The complete matched moment retains its strictly positive first boundary coefficient. -/
theorem transportMoment_boundary_ratio_limit (r : ℝ) :
    Tendsto (fun x => transportMoment x x (r*x)/x) (𝓝[>] 0) (𝓝 centerBoundaryMass) := by
  have h := (normalizedPacket_boundary_ratio_limit r).add
    ((secant_boundary_limit r).mul (transportPrimitive_boundary_ratio_limit r))
  have he : centerBoundaryMass-c 0*r+c 0*r=centerBoundaryMass := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  rw [smoothSecant_eq hx0.ne']
  unfold transportMoment ThetaSturmCrossing.secant
  rw [add_comm x (r*x)]
  ring

/-- The full actual current has a negative boundary profile at every fixed nonnegative scaling. -/
theorem finiteCanonicalCurrent_boundary_limit {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun x => finiteCanonicalCurrent x x (r*x)) (𝓝[>] 0)
      (𝓝 (-centerBoundaryMass/(2*(r+1)^2))) := by
  have h := ((packetCoefficient_boundary_limit hr).mul
    (normalizedPacket_boundary_ratio_limit r)).add
      ((primitiveCoefficient_boundary_limit hr).mul (transportPrimitive_boundary_ratio_limit r))
  have he : (-1/(2*(r+1)^2))*(centerBoundaryMass-c 0*r)+
      (-c 0/(2*(r+1)^2))*r=-centerBoundaryMass/(2*(r+1)^2) := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  rw [finiteCanonicalCurrent_diagonal hx0 (mul_nonneg hr hx0.le)]
  field_simp [hx0.ne']

theorem finiteCanonicalCurrent_boundary_eventually_neg {r : ℝ} (hr : 0 ≤ r) :
    ∀ᶠ x in 𝓝[>] (0:ℝ), finiteCanonicalCurrent x x (r*x) < 0 := by
  have hp : 0 < r+1 := by linarith only [hr]
  have hneg : -centerBoundaryMass/(2*(r+1)^2) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos centerBoundaryMass_pos)
      (mul_pos (by norm_num) (sq_pos_of_pos hp))
  exact (tendsto_order.1 (finiteCanonicalCurrent_boundary_limit hr)).2 0 hneg

end RHTower.ThetaFiniteTransport
