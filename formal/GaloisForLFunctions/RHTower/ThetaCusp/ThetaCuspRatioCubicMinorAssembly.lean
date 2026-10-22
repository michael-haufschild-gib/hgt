import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCubicMomentJets
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

@[simp] private theorem pd_nat73p (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

theorem criticalMoment2_J (r : ℂ) : criticalValue r (pderiv Coord.J scaledMoment2)=0 := by
  have hd := critical_partial_J scaledMoment2 r (r/12)
  simp_rw [scaledMoment2_zero] at hd
  exact hd.unique (hasDerivAt_const (r/12) (-(6:ℂ)^4*24))
theorem criticalMoment4_J (r : ℂ) : criticalValue r (pderiv Coord.J scaledMoment4)=0 := by
  have hd := critical_partial_J scaledMoment4 r (r/12)
  simp_rw [scaledMoment4_zero] at hd
  exact hd.unique (hasDerivAt_const (r/12) ((6:ℂ)^6*1728))
theorem criticalMoment6_J (r : ℂ) :
    criticalValue r (pderiv Coord.J scaledMoment6)= -(12:ℂ)*6^8*1296 := by
  have hd := critical_partial_J scaledMoment6 r (r/12)
  simp_rw [scaledMoment6_zero] at hd
  have hc := ((((hasDerivAt_const (r/12) r).sub ((hasDerivAt_id (r/12)).const_mul 12)).const_mul
    1296).const_add (-207360)).const_mul ((6:ℂ)^8)
  convert hd.unique hc using 1 <;> first | rfl | simp [criticalValue] <;> ring

def affineMoment10MixedNorm (r : ℂ) :
    {c : ℂ // affineJet1 r (pderiv Coord.J scaledMoment10)=c} := by
  have he : affineJet1 r (pderiv Coord.J scaledMoment10)=
      jet10UJ r-(7*r/72)*jet10JJ r := by
    simp [affineJet1,affineD,criticalValue,jet10UJ,jet10JJ]
  simp only [(jet10UJNorm r).property,(jet10JJNorm r).property] at he
  norm_num [jet10UJNorm,jet10JJNorm] at he
  exact ⟨_,he⟩

def affineMinorMixedNorm (r : ℂ) :
    {c : ℂ // affineJet1 r (pderiv Coord.J scaledMinor)=c} := by
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have hz : r-12*(r/12)=0 := by ring
  have he : affineJet1 r (pderiv Coord.J scaledMinor)=
      affineJet1 r (pderiv Coord.J scaledMinor) := rfl
  conv at he =>
    rhs
    simp only [scaledMinor,pow_succ,pderiv_mul,map_add,map_sub,map_neg,pderiv_X,
      Pi.single_apply,huj,if_false,affineJet1_add,affineJet1_sub,affineJet1_neg,
      affineJet1_mul,affineJet1_h,affineJet1_nat,criticalMoment2_J,criticalMoment4_J,
      criticalMoment6_J,criticalMoment8_J,criticalMoment10_J,
      affineMoment10_first,affineMoment8_first]
    simp only [(affineMoment2Jet1Norm r).property,(affineMoment4Jet1Norm r).property,
      (affineMoment6Jet1Norm r).property,(affineMoment10MixedNorm r).property]
    norm_num [criticalValue,basePoint,scaledMoment2_zero,scaledMoment4_zero,
      scaledMoment6_zero,scaledMoment8_zero,scaledMoment10_zero,hz,
      affineMoment2Jet1Norm,affineMoment4Jet1Norm,affineMoment6Jet1Norm,affineMoment10MixedNorm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def affineMinorThirdNorm (r : ℂ) : {c : ℂ // affineJet3 r scaledMinor=c} := by
  have hz : r-12*(r/12)=0 := by ring
  have he : affineJet3 r scaledMinor=affineJet3 r scaledMinor := rfl
  conv at he =>
    rhs
    simp only [scaledMinor,pow_succ,affineJet3_add,affineJet3_sub,affineJet3_neg,
      affineJet3_mul,affineJet2_neg,affineJet2_mul,affineJet1_neg,affineJet1_mul,
      affineMoment10_first,affineMoment10_second,affineMoment8_first,
      affineJet1_h,affineJet2_h,affineJet3_h,affineJet1_nat,affineJet2_nat,affineJet3_nat]
    norm_num [criticalValue,basePoint,scaledMoment2_zero,scaledMoment4_zero,
      scaledMoment6_zero,scaledMoment8_zero,scaledMoment10_zero,hz]
    simp only [(affineMoment2Jet1Norm r).property,(affineMoment4Jet1Norm r).property,
      (affineMoment6Jet1Norm r).property,(affineMoment8Jet2Norm r).property,
      (affineMoment10Jet3Norm r).property]
    norm_num [affineMoment2Jet1Norm,affineMoment4Jet1Norm,affineMoment6Jet1Norm,
      affineMoment8Jet2Norm,affineMoment10Jet3Norm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def nonlinearMinorThirdNorm (r : ℂ) :
    {c : ℂ // affineJet3 r scaledMinor+(r^2/24)*affineJet1 r (pderiv Coord.J scaledMinor)-
      (7*r^2/72)*criticalValue r (pderiv Coord.J scaledMinor)=c} := by
  have he : affineJet3 r scaledMinor+(r^2/24)*affineJet1 r (pderiv Coord.J scaledMinor)-
      (7*r^2/72)*criticalValue r (pderiv Coord.J scaledMinor)=
      affineJet3 r scaledMinor+(r^2/24)*affineJet1 r (pderiv Coord.J scaledMinor)-
      (7*r^2/72)*criticalValue r (pderiv Coord.J scaledMinor) := rfl
  conv at he =>
    rhs
    rw [(affineMinorThirdNorm r).property,(affineMinorMixedNorm r).property,criticalMinor_J]
    norm_num [affineMinorThirdNorm,affineMinorMixedNorm,principalMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
