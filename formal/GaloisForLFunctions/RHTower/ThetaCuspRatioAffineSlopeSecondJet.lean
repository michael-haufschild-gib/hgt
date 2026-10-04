import GaloisForLFunctions.RHTower.ThetaCuspRatioAffineCriticalFlow
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

@[simp] private theorem pd_nat73 (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n
private theorem univ73 : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

private theorem flow_expand73 (P : Poly) : flow affineField P=
    pderiv Coord.U P*affineField .U+
      (pderiv Coord.K P*affineField .K+pderiv Coord.J P*affineField .J) := by
  simp [flow,univ73]

def planeValue (r : ℂ) (P : Poly) : ℂ := eval (basePoint 0 r 0) P
def planeJet1 (r : ℂ) (P : Poly) : ℂ := planeValue r (pderiv Coord.U P)
def planeJet2 (r : ℂ) (P : Poly) : ℂ := planeValue r (pderiv Coord.U (pderiv Coord.U P))
def affineMinor : Poly := affineShift scaledMinor

@[simp] theorem planeValue_mul (r : ℂ) (P Q : Poly) :
    planeValue r (P*Q)=planeValue r P*planeValue r Q := by simp [planeValue]

@[simp] theorem planeJet1_mul (r : ℂ) (P Q : Poly) :
    planeJet1 r (P*Q)=planeJet1 r P*planeValue r Q+planeValue r P*planeJet1 r Q := by
  simp [planeJet1,planeValue,pderiv_mul]
  ring
@[simp] theorem planeJet2_mul (r : ℂ) (P Q : Poly) :
    planeJet2 r (P*Q)=planeJet2 r P*planeValue r Q+
      2*planeJet1 r P*planeJet1 r Q+planeValue r P*planeJet2 r Q := by
  simp [planeJet2,planeJet1,planeValue,pderiv_mul]
  ring
@[simp] theorem planeJet1_add (r : ℂ) (P Q : Poly) :
    planeJet1 r (P+Q)=planeJet1 r P+planeJet1 r Q := by simp [planeJet1,planeValue]
@[simp] theorem planeJet2_add (r : ℂ) (P Q : Poly) :
    planeJet2 r (P+Q)=planeJet2 r P+planeJet2 r Q := by simp [planeJet2,planeValue]

theorem criticalMinor_J (r : ℂ) : criticalValue r (pderiv Coord.J scaledMinor)=12*principalMass := by
  have hd := critical_partial_J scaledMinor r (r/12)
  simp_rw [scaledMinor_zero] at hd
  have hc := ((hasDerivAt_const (r/12) r).sub ((hasDerivAt_id (r/12)).const_mul 12)).const_mul
    (-principalMass)
  convert hd.unique hc using 1 <;> first | rfl | simp [criticalValue] <;> ring

theorem affineMinor_first (r : ℂ) : affineJet1 r scaledMinor=0 := by
  have hU := criticalMinorFirst_eq r
  have hJ := criticalMinor_J r
  simp only [affineJet1,affineD,criticalValue,map_sub,map_mul,eval_C]
  rw [hU]
  change (7/6)*principalMass*r-(7*r/72)*criticalValue r (pderiv Coord.J scaledMinor)=0
  rw [hJ]
  ring

theorem planeMinor_zero (r : ℂ) : planeValue r affineMinor=0 := by
  unfold planeValue affineMinor
  rw [affineShift_eval,scaledMinor_zero]
  ring

theorem planeMinor_first (r : ℂ) : planeJet1 r affineMinor=0 := by
  exact (affineShift_first scaledMinor r).trans (affineMinor_first r)

theorem planeMinor_second (r : ℂ) :
    planeJet2 r affineMinor=2*axisMinorMass-(principalMass/6)*r^2 := by
  exact (affineShift_second scaledMinor r).trans (affineMinor_second r)

theorem plane_partial_K (P : Poly) (r : ℂ) :
    HasDerivAt (fun s => planeValue s P) (planeValue r (pderiv Coord.K P)) r := by
  have hd : HasDerivAt (fun s => basePoint 0 s 0)
      (fun i => if i=Coord.K then (1:ℂ) else 0) r := by
    apply hasDerivAt_pi.mpr
    intro i
    cases i with
    | U => simpa [basePoint] using hasDerivAt_const r (0:ℂ)
    | J => simpa [basePoint] using hasDerivAt_const r (0:ℂ)
    | K => convert hasDerivAt_id r using 1 <;> first | rfl | simp [basePoint]
  have he := GaloisForLFunctions.HTGeometry.hasDerivAt_mvPolynomial_eval_comp P hd
  simpa [planeValue,Finset.sum_ite_eq'] using he

theorem planeMinor_K (r : ℂ) : planeValue r (pderiv Coord.K affineMinor)=0 := by
  have hd := plane_partial_K affineMinor r
  simp_rw [planeMinor_zero] at hd
  exact hd.unique (hasDerivAt_const r 0)

theorem planeMinor_UK (r : ℂ) : planeJet1 r (pderiv Coord.K affineMinor)=0 := by
  have hd := plane_partial_K (pderiv Coord.U affineMinor) r
  change HasDerivAt (fun s => planeJet1 s affineMinor)
    (planeValue r (pderiv Coord.K (pderiv Coord.U affineMinor))) r at hd
  simp_rw [planeMinor_first] at hd
  have he := hd.unique (hasDerivAt_const r 0)
  simpa only [planeJet1,partials_commute Coord.U Coord.K] using he

theorem planeMinor_UUK (r : ℂ) :
    planeJet2 r (pderiv Coord.K affineMinor)= -(principalMass/3)*r := by
  have hd := plane_partial_K (pderiv Coord.U (pderiv Coord.U affineMinor)) r
  change HasDerivAt (fun s => planeJet2 s affineMinor)
    (planeValue r (pderiv Coord.K (pderiv Coord.U (pderiv Coord.U affineMinor)))) r at hd
  simp_rw [planeMinor_second] at hd
  have hc := (hasDerivAt_const r (2*axisMinorMass)).sub
    (((hasDerivAt_id r).pow 2).const_mul (principalMass/6))
  have he := hd.unique hc
  simp only [planeJet2,partials_commute Coord.U Coord.K]
  rw [he]
  simp only [id_eq]
  ring

theorem planeMinor_J (r : ℂ) : planeValue r (pderiv Coord.J affineMinor)=12*principalMass := by
  simpa [planeValue,affineMinor,affineShift_J,affineShift_eval,criticalValue,div_eq_mul_inv] using criticalMinor_J r

theorem affineFlow_zero (r : ℂ) : planeValue r (flow affineField affineMinor)=0 := by
  have h0 := affineField_zero r
  change planeValue r (affineField .U)=0 ∧ planeValue r (affineField .K)= -108*r ∧
    planeValue r (affineField .J)=0 at h0
  have hK := planeMinor_K r
  unfold planeValue at h0 hK ⊢
  simp [flow,univ73,h0.1,h0.2.1,h0.2.2,hK]

theorem affineFlow_first (r : ℂ) : planeJet1 r (flow affineField affineMinor)=0 := by
  have h0 := affineField_zero r
  have hU := affineField_first_U r
  have hJ := affineField_first_J r
  change planeValue r (affineField .U)=0 ∧ planeValue r (affineField .K)= -108*r ∧
    planeValue r (affineField .J)=0 at h0
  change planeJet1 r (affineField .U)=0 at hU
  change planeJet1 r (affineField .J)=0 at hJ
  rw [flow_expand73]
  simp only [planeJet1_add,planeJet1_mul,h0.1,h0.2.1,h0.2.2,hU,hJ,
    planeMinor_K,planeMinor_UK,zero_mul,mul_zero,add_zero,zero_add]

theorem affineFlow_second (r : ℂ) :
    planeJet2 r (flow affineField affineMinor)= -18*principalMass*r^2 := by
  have h0 := affineField_zero r
  have hU := affineField_first_U r
  have hJ := affineField_first_J r
  have hJJ := affineField_second_J r
  change planeValue r (affineField .U)=0 ∧ planeValue r (affineField .K)= -108*r ∧
    planeValue r (affineField .J)=0 at h0
  change planeJet1 r (affineField .U)=0 at hU
  change planeJet1 r (affineField .J)=0 at hJ
  change planeJet2 r (affineField .J)= -(9/2:ℂ)*r^2 at hJJ
  have hPU : planeValue r (pderiv Coord.U affineMinor)=0 := planeMinor_first r
  rw [flow_expand73]
  simp only [planeJet2_add,planeJet2_mul,h0.1,h0.2.1,h0.2.2,hU,hJ,hJJ,hPU,
    planeMinor_K,planeMinor_UK,planeMinor_UUK,planeMinor_J,zero_mul,mul_zero,add_zero,zero_add]
  ring

theorem affineSlope_eq : affineShift scaledSlope=
    (6-X Coord.U)*flow affineField affineMinor+
      (17*X Coord.U-66)*affineShift clockLinear*affineMinor := by
  simp only [scaledSlope,map_add,map_sub,map_mul,map_ofNat,affineShift_X,affineCoord]
  rw [← affineShift_flow]
  rfl

theorem affineSlope_zero (r : ℂ) : planeValue r (affineShift scaledSlope)=0 := by
  unfold planeValue
  rw [affineShift_eval,scaledSlope_zero]
  ring

theorem affineSlope_first (r : ℂ) : planeJet1 r (affineShift scaledSlope)=0 := by
  have hv : planeValue r (affineShift clockLinear)=0 := by
    norm_num [planeValue,affineShift_eval,clockLinear,affineCoord,basePoint]
  rw [affineSlope_eq]
  simp only [planeJet1_add,planeJet1_mul,affineFlow_zero,affineFlow_first,
    planeMinor_zero,planeMinor_first,hv,zero_mul,mul_zero,add_zero,zero_add]

theorem affineSlope_second (r : ℂ) :
    planeJet2 r (affineShift scaledSlope)= -108*principalMass*r^2 := by
  have hv : planeValue r (affineShift clockLinear)=0 := by
    norm_num [planeValue,affineShift_eval,clockLinear,affineCoord,basePoint]
  have hc1 : planeJet1 r ((6:Poly)-X Coord.U)= -1 := by
    simp [planeJet1,planeValue,pderiv_X,basePoint]
  have hc2 : planeJet2 r ((6:Poly)-X Coord.U)=0 := by
    simp [planeJet2,planeValue,pderiv_X,basePoint]
  have hc0 : planeValue r ((6:Poly)-X Coord.U)=6 := by simp [planeValue,basePoint]
  rw [affineSlope_eq]
  simp only [planeJet2_add,planeJet2_mul,planeJet1_mul,hc1,hc2,hc0,
    affineFlow_first,affineFlow_second,planeMinor_zero,planeMinor_first,hv,
    zero_mul,mul_zero,add_zero,zero_add]
  simp only [planeValue_mul,hv,mul_zero]
  ring

end
end HTGeometry.ThetaRatioInfinity
