import GaloisForLFunctions.RHTower.ThetaCuspRatioCubicMinorJets
import GaloisForLFunctions.RHTower.ThetaCuspRatioCubicFieldCoefficients
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

@[simp] private theorem pd_nat73s (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n
private theorem univ73s : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp
private theorem nonlinearFlow_expand (P : Poly) : flow nonlinearField P=
    pderiv Coord.U P*nonlinearField .U+
      (pderiv Coord.K P*nonlinearField .K+pderiv Coord.J P*nonlinearField .J) := by
  simp [flow,univ73s]

private theorem planeValue_add73 (r : ℂ) (P Q : Poly) :
    planeValue r (P+Q)=planeValue r P+planeValue r Q := by simp [planeValue]

theorem nonlinearFlow_zero (r : ℂ) : planeValue r (flow nonlinearField nonlinearMinor)=0 := by
  have hf := nonlinearField_zero r
  have hj := nonlinearField_J_jets r
  have hp : planeValue r (pderiv Coord.U nonlinearMinor)=0 := nonlinearMinor_first r
  rw [nonlinearFlow_expand]
  simp only [planeValue_add73,planeValue_mul,hf.1,hf.2,hj.1,hp,nonlinearMinor_K,
    zero_mul,mul_zero,add_zero,zero_add]

theorem nonlinearFlow_first (r : ℂ) : planeJet1 r (flow nonlinearField nonlinearMinor)=0 := by
  have hf := nonlinearField_zero r
  have hh := nonlinearField_h_jets r
  have hj := nonlinearField_J_jets r
  have hp : planeValue r (pderiv Coord.U nonlinearMinor)=0 := nonlinearMinor_first r
  rw [nonlinearFlow_expand]
  simp only [planeJet1_add,planeJet1_mul,hf.1,hf.2,hh.1,hj.1,hj.2.1,hp,
    nonlinearMinor_K,nonlinearMinor_UK,zero_mul,mul_zero,add_zero,zero_add]

theorem nonlinearFlow_second (r : ℂ) : planeJet2 r (flow nonlinearField nonlinearMinor)=0 := by
  have hf := nonlinearField_zero r
  have hh := nonlinearField_h_jets r
  have hj := nonlinearField_J_jets r
  have hp : planeValue r (pderiv Coord.U nonlinearMinor)=0 := nonlinearMinor_first r
  rw [nonlinearFlow_expand]
  simp only [planeJet2_add,planeJet2_mul,hf.1,hf.2,hh.1,hj.1,hj.2.1,hj.2.2.1,hp,
    nonlinearMinor_K,nonlinearMinor_UK,nonlinearMinor_UUK,zero_mul,mul_zero,add_zero,zero_add]

theorem nonlinearFlow_third (r : ℂ) :
    planeJet3 r (flow nonlinearField nonlinearMinor)= -432*axisMinorMass-63*principalMass*r^2 := by
  have hf := nonlinearField_zero r
  have hh := nonlinearField_h_jets r
  have hj := nonlinearField_J_jets r
  have hp : planeValue r (pderiv Coord.U nonlinearMinor)=0 := nonlinearMinor_first r
  have hp2 : planeJet1 r (pderiv Coord.U nonlinearMinor)=2*axisMinorMass := nonlinearMinor_second r
  rw [nonlinearFlow_expand]
  simp only [planeJet3_add,planeJet3_mul,hf.1,hf.2,hh.1,hh.2,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2,hp,hp2,
    nonlinearMinor_K,nonlinearMinor_UK,nonlinearMinor_UUK,nonlinearMinor_UUUK,nonlinearMinor_J,
    zero_mul,mul_zero,add_zero,zero_add]
  ring

theorem nonlinearSlope_eq : nonlinearShift scaledSlope=
    (6-X Coord.U)*flow nonlinearField nonlinearMinor+
      ((17*X Coord.U-66)*nonlinearShift clockLinear)*nonlinearMinor := by
  simp only [scaledSlope,map_add,map_sub,map_mul,map_ofNat,nonlinearShift_X,nonlinearCoord]
  rw [←nonlinearShift_flow]
  rfl

theorem nonlinearSlope_low_jets (r : ℂ) :
    planeValue r (nonlinearShift scaledSlope)=0 ∧
    planeJet1 r (nonlinearShift scaledSlope)=0 ∧
    planeJet2 r (nonlinearShift scaledSlope)=0 := by
  have hl := nonlinearClock_jets r
  have hw0 : planeValue r ((17*X Coord.U-66)*nonlinearShift clockLinear)=0 := by
    rw [planeValue_mul,hl.1,mul_zero]
  have hc0 : planeValue r ((6:Poly)-X Coord.U)=6 := by simp [planeValue,basePoint]
  rw [nonlinearSlope_eq]
  refine ⟨?_,?_,?_⟩
  · simp only [planeValue_add73,planeValue_mul,nonlinearFlow_zero,nonlinearMinor_zero,
      mul_zero,add_zero]
  · simp only [planeJet1_add,planeJet1_mul,nonlinearFlow_zero,nonlinearFlow_first,
      nonlinearMinor_zero,nonlinearMinor_first,hw0,zero_mul,mul_zero,add_zero,zero_add]
  · simp only [planeJet2_add,planeJet2_mul,nonlinearFlow_zero,nonlinearFlow_first,nonlinearFlow_second,
      nonlinearMinor_zero,nonlinearMinor_first,nonlinearMinor_second,hw0,zero_mul,mul_zero,add_zero,zero_add]

theorem nonlinearSlope_third (r : ℂ) :
    planeJet3 r (nonlinearShift scaledSlope)=11664*axisMinorMass-378*principalMass*r^2 := by
  have hl := nonlinearClock_jets r
  have hw0 : planeValue r ((17*X Coord.U-66)*nonlinearShift clockLinear)=0 := by
    rw [planeValue_mul,hl.1,mul_zero]
  have hw1 : planeJet1 r ((17*X Coord.U-66)*nonlinearShift clockLinear)=2376 := by
    rw [planeJet1_mul,hl.1,hl.2,mul_zero,zero_add]
    norm_num [planeValue,basePoint]
  have hc0 : planeValue r ((6:Poly)-X Coord.U)=6 := by simp [planeValue,basePoint]
  rw [nonlinearSlope_eq]
  simp only [planeJet3_add,planeJet3_mul,nonlinearFlow_zero,nonlinearFlow_first,nonlinearFlow_second,
    nonlinearFlow_third,nonlinearMinor_zero,nonlinearMinor_first,nonlinearMinor_second,
    hw0,hw1,hc0,zero_mul,mul_zero,add_zero,zero_add]
  ring

theorem nonlinearSlope_coeff_three (r : ℂ) :
    (affineLine r (nonlinearShift scaledSlope)).coeff 3=1944*axisMinorMass-63*principalMass*r^2 := by
  have he := nonlinearSlope_third r
  simp only [planeJet3,planeValue,←affineLine_eval,←affineLine_derivative] at he
  norm_num [←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative] at he
  linear_combination he/6

end
end HTGeometry.ThetaRatioInfinity
