import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioInfinityMinor

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare


@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

def criticalMoment10First (r : ℂ) : ℂ :=
  eval (basePoint 0 r (r/12)) (pderiv Coord.U scaledMoment10)

def criticalMoment10FirstNorm (r : ℂ) : {c : ℂ // criticalMoment10First r=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have he : criticalMoment10First r=criticalMoment10First r := rfl
  conv at he =>
    rhs
    norm_num [criticalMoment10First,scaledMoment10,low10,midScaled10,upperScaled10,
      driftSquare,deficit,scaled10Part0Low,scaled10Part1Low,scaled10Part2Low,scaled10Part3Low,scaled10Part4Low,scaled10Part5Low,scaled10Part6Low,scaled10Part7Low,scaled10Part8Low,scaled10Part9Low,scaled10Part10Low,scaled10Part11Low,scaled10Part12Low,scaled10Part13Low,scaled10Part14Low,scaled10Part15Low,scaled10Part16Low,scaled10Part17Low,scaled10Part18Low,scaled10Part19Low,scaled10Part20Low,scaled10Part21Low,scaled10Part22Low,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,
      basePoint,Finset.sum_range_succ,hku,hju]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem criticalMoment10First_eq (r : ℂ) :
    criticalMoment10First r= -(7/6:ℂ)*(6:ℂ)^12*1679616*r := by
  rw [(criticalMoment10FirstNorm r).property]
  norm_num [criticalMoment10FirstNorm]
  ring

theorem criticalMinorFirst_eq (r : ℂ) :
    eval (basePoint 0 r (r/12)) (pderiv Coord.U scaledMinor)=
      (7/6:ℂ)*principalMass*r := by
  have ht : r-12*(r/12)=0 := by ring
  have h10 := criticalMoment10First_eq r
  change eval (basePoint 0 r (r/12)) (pderiv Coord.U scaledMoment10)=_ at h10
  norm_num [scaledMinor,pderiv_mul,pderiv_pow,basePoint,scaledMoment2_zero,
    scaledMoment4_zero,scaledMoment6_zero,scaledMoment8_zero,scaledMoment10_zero,
    ht,h10]
  unfold principalMass
  ring


end
end HTGeometry.ThetaRatioInfinity
