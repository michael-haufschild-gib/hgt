import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCubicSourceJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCubicMinorFormula
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

@[simp] private theorem pd_nat73a (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

theorem nonlinearMinor_third (r : ℂ) :
    planeJet3 r nonlinearMinor=principalMass*(28160/9-(7/12)*r^2) := by
  unfold nonlinearMinor
  rw [nonlinearShift_third]
  have hp : principalMass≠0 := by norm_num [principalMass]
  have he := congrArg (fun z : ℂ => z*principalMass) (nonlinearMinorThirdRatioNorm r).property
  rw [div_mul_cancel₀ _ hp] at he
  convert he using 1
  norm_num [nonlinearMinorThirdRatioNorm,NNRat.rawCast,Nat.rawCast,Rat.rawCast]
  ring

theorem nonlinearMinor_K (r : ℂ) : planeValue r (pderiv Coord.K nonlinearMinor)=0 := by
  have hd := plane_partial_K nonlinearMinor r
  simp_rw [nonlinearMinor_zero] at hd
  exact hd.unique (hasDerivAt_const r 0)
theorem nonlinearMinor_UK (r : ℂ) : planeJet1 r (pderiv Coord.K nonlinearMinor)=0 := by
  have hd := plane_partial_K (pderiv Coord.U nonlinearMinor) r
  change HasDerivAt (fun s => planeJet1 s nonlinearMinor)
    (planeValue r (pderiv Coord.K (pderiv Coord.U nonlinearMinor))) r at hd
  simp_rw [nonlinearMinor_first] at hd
  have he := hd.unique (hasDerivAt_const r 0)
  simpa only [planeJet1,partials_commute Coord.U Coord.K] using he
theorem nonlinearMinor_UUK (r : ℂ) : planeJet2 r (pderiv Coord.K nonlinearMinor)=0 := by
  have hd := plane_partial_K (pderiv Coord.U (pderiv Coord.U nonlinearMinor)) r
  change HasDerivAt (fun s => planeJet2 s nonlinearMinor)
    (planeValue r (pderiv Coord.K (pderiv Coord.U (pderiv Coord.U nonlinearMinor)))) r at hd
  simp_rw [nonlinearMinor_second] at hd
  have he := hd.unique (hasDerivAt_const r (2*axisMinorMass))
  simpa only [planeJet2,partials_commute Coord.U Coord.K] using he
theorem nonlinearMinor_UUUK (r : ℂ) :
    planeJet3 r (pderiv Coord.K nonlinearMinor)= -(7/6)*principalMass*r := by
  have hd := plane_partial_K (pderiv Coord.U (pderiv Coord.U (pderiv Coord.U nonlinearMinor))) r
  change HasDerivAt (fun s => planeJet3 s nonlinearMinor)
    (planeValue r (pderiv Coord.K (pderiv Coord.U (pderiv Coord.U (pderiv Coord.U nonlinearMinor))))) r at hd
  simp_rw [nonlinearMinor_third] at hd
  have hc := ((hasDerivAt_const r (28160/9:ℂ)).sub
    (((hasDerivAt_id r).pow 2).const_mul (7/12))).const_mul principalMass
  have he := hd.unique hc
  simp only [planeJet3,partials_commute Coord.U Coord.K]
  rw [he]
  simp only [id_eq]
  ring

theorem nonlinearMinor_J (r : ℂ) :
    planeValue r (pderiv Coord.J nonlinearMinor)=12*principalMass := by
  have hk : Coord.K≠Coord.J := by intro h; cases h
  have hu : Coord.U≠Coord.J := by intro h; cases h
  simp [nonlinearMinor,nonlinearShift_partial,planeValue,nonlinearShift_eval,
    nonlinearB,affineB,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hk,hu]
  exact criticalMinor_J r

theorem nonlinearField_zero (r : ℂ) :
    planeValue r (nonlinearField .U)=0 ∧ planeValue r (nonlinearField .K)= -108*r := by
  norm_num [planeValue,nonlinearField,nonlinearShift_eval,nonlinearCoord,infinityField,basePoint,driftSquare,deficit]

theorem nonlinearField_h_jets (r : ℂ) :
    planeJet1 r (nonlinearField .U)=0 ∧ planeJet2 r (nonlinearField .U)= -72 := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  have hj : Coord.J≠Coord.U := by intro h; cases h
  have hk' : Coord.K≠Coord.J := by intro h; cases h
  have hu' : Coord.U≠Coord.J := by intro h; cases h
  simp only [nonlinearField,nonlinearShift_first,nonlinearShift_second]
  norm_num [affineJet1,affineJet2,affineD,criticalValue,infinityField,driftSquare,deficit,
    pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hk,hj,hk',hu',basePoint]

theorem nonlinearClock_jets (r : ℂ) :
    planeValue r (nonlinearShift clockLinear)=0 ∧ planeJet1 r (nonlinearShift clockLinear)= -36 := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  have hj : Coord.J≠Coord.U := by intro h; cases h
  have hk' : Coord.K≠Coord.J := by intro h; cases h
  have hu' : Coord.U≠Coord.J := by intro h; cases h
  constructor
  · norm_num [planeValue,nonlinearShift_eval,nonlinearCoord,clockLinear,basePoint]
  · rw [nonlinearShift_first]
    norm_num [affineJet1,affineD,criticalValue,clockLinear,driftSquare,deficit,
      pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hk,hj,hk',hu',basePoint]

end
end HTGeometry.ThetaRatioInfinity
