import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCubicJetAlgebra
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

@[simp] private theorem pd_nat73m (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

private def scaled2Part0LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled2Part0Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled2Part0Low=affineJet1 r scaled2Part0Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled2Part0Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled2Part1LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled2Part1Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled2Part1Low=affineJet1 r scaled2Part1Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled2Part1Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def midScaled2Affine1Norm (r : ℂ) : {c : ℂ // affineJet1 r midScaled2=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r midScaled2=affineJet1 r midScaled2 := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,midScaled2,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def upperScaled2Affine1Norm (r : ℂ) : {c : ℂ // affineJet1 r upperScaled2=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r upperScaled2=affineJet1 r upperScaled2 := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,upperScaled2,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def affineMoment2Jet1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaledMoment2=c} := by
  have he : affineJet1 r scaledMoment2=affineJet1 r scaledMoment2 := rfl
  conv at he =>
    rhs
    simp only [scaledMoment2,low2,affineJet1_add,(scaled2Part0LowAffine1Norm r).property,(scaled2Part1LowAffine1Norm r).property,(midScaled2Affine1Norm r).property,(upperScaled2Affine1Norm r).property]
    norm_num [scaled2Part0LowAffine1Norm,scaled2Part1LowAffine1Norm,midScaled2Affine1Norm,upperScaled2Affine1Norm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


private def scaled4Part0LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled4Part0Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled4Part0Low=affineJet1 r scaled4Part0Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled4Part0Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled4Part1LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled4Part1Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled4Part1Low=affineJet1 r scaled4Part1Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled4Part1Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled4Part2LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled4Part2Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled4Part2Low=affineJet1 r scaled4Part2Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled4Part2Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled4Part3LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled4Part3Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled4Part3Low=affineJet1 r scaled4Part3Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled4Part3Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def midScaled4Affine1Norm (r : ℂ) : {c : ℂ // affineJet1 r midScaled4=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r midScaled4=affineJet1 r midScaled4 := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,midScaled4,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def upperScaled4Affine1Norm (r : ℂ) : {c : ℂ // affineJet1 r upperScaled4=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r upperScaled4=affineJet1 r upperScaled4 := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,upperScaled4,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def affineMoment4Jet1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaledMoment4=c} := by
  have he : affineJet1 r scaledMoment4=affineJet1 r scaledMoment4 := rfl
  conv at he =>
    rhs
    simp only [scaledMoment4,low4,affineJet1_add,(scaled4Part0LowAffine1Norm r).property,(scaled4Part1LowAffine1Norm r).property,(scaled4Part2LowAffine1Norm r).property,(scaled4Part3LowAffine1Norm r).property,(midScaled4Affine1Norm r).property,(upperScaled4Affine1Norm r).property]
    norm_num [scaled4Part0LowAffine1Norm,scaled4Part1LowAffine1Norm,scaled4Part2LowAffine1Norm,scaled4Part3LowAffine1Norm,midScaled4Affine1Norm,upperScaled4Affine1Norm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


private def scaled6Part0LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled6Part0Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled6Part0Low=affineJet1 r scaled6Part0Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled6Part0Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled6Part1LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled6Part1Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled6Part1Low=affineJet1 r scaled6Part1Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled6Part1Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled6Part2LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled6Part2Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled6Part2Low=affineJet1 r scaled6Part2Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled6Part2Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled6Part3LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled6Part3Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled6Part3Low=affineJet1 r scaled6Part3Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled6Part3Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled6Part4LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled6Part4Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled6Part4Low=affineJet1 r scaled6Part4Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled6Part4Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled6Part5LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled6Part5Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled6Part5Low=affineJet1 r scaled6Part5Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled6Part5Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled6Part6LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled6Part6Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled6Part6Low=affineJet1 r scaled6Part6Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled6Part6Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled6Part7LowAffine1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaled6Part7Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r scaled6Part7Low=affineJet1 r scaled6Part7Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,scaled6Part7Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def midScaled6Affine1Norm (r : ℂ) : {c : ℂ // affineJet1 r midScaled6=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r midScaled6=affineJet1 r midScaled6 := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,midScaled6,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def upperScaled6Affine1Norm (r : ℂ) : {c : ℂ // affineJet1 r upperScaled6=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet1 r upperScaled6=affineJet1 r upperScaled6 := rfl
  conv at he =>
    rhs
    norm_num [affineJet1,affineD,criticalValue,upperScaled6,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def affineMoment6Jet1Norm (r : ℂ) : {c : ℂ // affineJet1 r scaledMoment6=c} := by
  have he : affineJet1 r scaledMoment6=affineJet1 r scaledMoment6 := rfl
  conv at he =>
    rhs
    simp only [scaledMoment6,low6,affineJet1_add,(scaled6Part0LowAffine1Norm r).property,(scaled6Part1LowAffine1Norm r).property,(scaled6Part2LowAffine1Norm r).property,(scaled6Part3LowAffine1Norm r).property,(scaled6Part4LowAffine1Norm r).property,(scaled6Part5LowAffine1Norm r).property,(scaled6Part6LowAffine1Norm r).property,(scaled6Part7LowAffine1Norm r).property,(midScaled6Affine1Norm r).property,(upperScaled6Affine1Norm r).property]
    norm_num [scaled6Part0LowAffine1Norm,scaled6Part1LowAffine1Norm,scaled6Part2LowAffine1Norm,scaled6Part3LowAffine1Norm,scaled6Part4LowAffine1Norm,scaled6Part5LowAffine1Norm,scaled6Part6LowAffine1Norm,scaled6Part7LowAffine1Norm,midScaled6Affine1Norm,upperScaled6Affine1Norm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


private def scaled8Part0LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part0Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part0Low=affineJet2 r scaled8Part0Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part0Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part1LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part1Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part1Low=affineJet2 r scaled8Part1Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part1Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part2LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part2Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part2Low=affineJet2 r scaled8Part2Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part2Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part3LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part3Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part3Low=affineJet2 r scaled8Part3Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part3Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part4LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part4Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part4Low=affineJet2 r scaled8Part4Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part4Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part5LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part5Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part5Low=affineJet2 r scaled8Part5Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part5Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part6LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part6Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part6Low=affineJet2 r scaled8Part6Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part6Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part7LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part7Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part7Low=affineJet2 r scaled8Part7Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part7Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part8LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part8Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part8Low=affineJet2 r scaled8Part8Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part8Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part9LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part9Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part9Low=affineJet2 r scaled8Part9Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part9Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part10LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part10Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part10Low=affineJet2 r scaled8Part10Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part10Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part11LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part11Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part11Low=affineJet2 r scaled8Part11Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part11Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part12LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part12Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part12Low=affineJet2 r scaled8Part12Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part12Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled8Part13LowAffine2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaled8Part13Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r scaled8Part13Low=affineJet2 r scaled8Part13Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,scaled8Part13Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def midScaled8Affine2Norm (r : ℂ) : {c : ℂ // affineJet2 r midScaled8=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r midScaled8=affineJet2 r midScaled8 := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,midScaled8,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def upperScaled8Affine2Norm (r : ℂ) : {c : ℂ // affineJet2 r upperScaled8=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet2 r upperScaled8=affineJet2 r upperScaled8 := rfl
  conv at he =>
    rhs
    norm_num [affineJet2,affineD,criticalValue,upperScaled8,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def affineMoment8Jet2Norm (r : ℂ) : {c : ℂ // affineJet2 r scaledMoment8=c} := by
  have he : affineJet2 r scaledMoment8=affineJet2 r scaledMoment8 := rfl
  conv at he =>
    rhs
    simp only [scaledMoment8,low8,affineJet2_add,(scaled8Part0LowAffine2Norm r).property,(scaled8Part1LowAffine2Norm r).property,(scaled8Part2LowAffine2Norm r).property,(scaled8Part3LowAffine2Norm r).property,(scaled8Part4LowAffine2Norm r).property,(scaled8Part5LowAffine2Norm r).property,(scaled8Part6LowAffine2Norm r).property,(scaled8Part7LowAffine2Norm r).property,(scaled8Part8LowAffine2Norm r).property,(scaled8Part9LowAffine2Norm r).property,(scaled8Part10LowAffine2Norm r).property,(scaled8Part11LowAffine2Norm r).property,(scaled8Part12LowAffine2Norm r).property,(scaled8Part13LowAffine2Norm r).property,(midScaled8Affine2Norm r).property,(upperScaled8Affine2Norm r).property]
    norm_num [scaled8Part0LowAffine2Norm,scaled8Part1LowAffine2Norm,scaled8Part2LowAffine2Norm,scaled8Part3LowAffine2Norm,scaled8Part4LowAffine2Norm,scaled8Part5LowAffine2Norm,scaled8Part6LowAffine2Norm,scaled8Part7LowAffine2Norm,scaled8Part8LowAffine2Norm,scaled8Part9LowAffine2Norm,scaled8Part10LowAffine2Norm,scaled8Part11LowAffine2Norm,scaled8Part12LowAffine2Norm,scaled8Part13LowAffine2Norm,midScaled8Affine2Norm,upperScaled8Affine2Norm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


private def scaled10Part0LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part0Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part0Low=affineJet3 r scaled10Part0Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part0Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part1LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part1Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part1Low=affineJet3 r scaled10Part1Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part1Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part2LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part2Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part2Low=affineJet3 r scaled10Part2Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part2Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part3LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part3Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part3Low=affineJet3 r scaled10Part3Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part3Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part4LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part4Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part4Low=affineJet3 r scaled10Part4Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part4Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part5LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part5Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part5Low=affineJet3 r scaled10Part5Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part5Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part6LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part6Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part6Low=affineJet3 r scaled10Part6Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part6Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part7LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part7Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part7Low=affineJet3 r scaled10Part7Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part7Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part8LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part8Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part8Low=affineJet3 r scaled10Part8Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part8Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part9LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part9Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part9Low=affineJet3 r scaled10Part9Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part9Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part10LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part10Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part10Low=affineJet3 r scaled10Part10Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part10Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part11LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part11Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part11Low=affineJet3 r scaled10Part11Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part11Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part12LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part12Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part12Low=affineJet3 r scaled10Part12Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part12Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part13LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part13Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part13Low=affineJet3 r scaled10Part13Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part13Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part14LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part14Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part14Low=affineJet3 r scaled10Part14Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part14Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part15LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part15Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part15Low=affineJet3 r scaled10Part15Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part15Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part16LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part16Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part16Low=affineJet3 r scaled10Part16Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part16Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part17LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part17Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part17Low=affineJet3 r scaled10Part17Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part17Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part18LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part18Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part18Low=affineJet3 r scaled10Part18Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part18Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part19LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part19Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part19Low=affineJet3 r scaled10Part19Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part19Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part20LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part20Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part20Low=affineJet3 r scaled10Part20Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part20Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part21LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part21Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part21Low=affineJet3 r scaled10Part21Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part21Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def scaled10Part22LowAffine3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaled10Part22Low=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r scaled10Part22Low=affineJet3 r scaled10Part22Low := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,scaled10Part22Low,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def midScaled10Affine3Norm (r : ℂ) : {c : ℂ // affineJet3 r midScaled10=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r midScaled10=affineJet3 r midScaled10 := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,midScaled10,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

private def upperScaled10Affine3Norm (r : ℂ) : {c : ℂ // affineJet3 r upperScaled10=c} := by
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have hju : Coord.J≠Coord.U := by intro h; cases h
  have hkj : Coord.K≠Coord.J := by intro h; cases h
  have huj : Coord.U≠Coord.J := by intro h; cases h
  have he : affineJet3 r upperScaled10=affineJet3 r upperScaled10 := rfl
  conv at he =>
    rhs
    norm_num [affineJet3,affineD,criticalValue,upperScaled10,driftSquare,deficit,pderiv_mul,pderiv_pow,
      pderiv_X,Pi.single_apply,basePoint,Finset.sum_range_succ,hku,hju,hkj,huj]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def affineMoment10Jet3Norm (r : ℂ) : {c : ℂ // affineJet3 r scaledMoment10=c} := by
  have he : affineJet3 r scaledMoment10=affineJet3 r scaledMoment10 := rfl
  conv at he =>
    rhs
    simp only [scaledMoment10,low10,affineJet3_add,(scaled10Part0LowAffine3Norm r).property,(scaled10Part1LowAffine3Norm r).property,(scaled10Part2LowAffine3Norm r).property,(scaled10Part3LowAffine3Norm r).property,(scaled10Part4LowAffine3Norm r).property,(scaled10Part5LowAffine3Norm r).property,(scaled10Part6LowAffine3Norm r).property,(scaled10Part7LowAffine3Norm r).property,(scaled10Part8LowAffine3Norm r).property,(scaled10Part9LowAffine3Norm r).property,(scaled10Part10LowAffine3Norm r).property,(scaled10Part11LowAffine3Norm r).property,(scaled10Part12LowAffine3Norm r).property,(scaled10Part13LowAffine3Norm r).property,(scaled10Part14LowAffine3Norm r).property,(scaled10Part15LowAffine3Norm r).property,(scaled10Part16LowAffine3Norm r).property,(scaled10Part17LowAffine3Norm r).property,(scaled10Part18LowAffine3Norm r).property,(scaled10Part19LowAffine3Norm r).property,(scaled10Part20LowAffine3Norm r).property,(scaled10Part21LowAffine3Norm r).property,(scaled10Part22LowAffine3Norm r).property,(midScaled10Affine3Norm r).property,(upperScaled10Affine3Norm r).property]
    norm_num [scaled10Part0LowAffine3Norm,scaled10Part1LowAffine3Norm,scaled10Part2LowAffine3Norm,scaled10Part3LowAffine3Norm,scaled10Part4LowAffine3Norm,scaled10Part5LowAffine3Norm,scaled10Part6LowAffine3Norm,scaled10Part7LowAffine3Norm,scaled10Part8LowAffine3Norm,scaled10Part9LowAffine3Norm,scaled10Part10LowAffine3Norm,scaled10Part11LowAffine3Norm,scaled10Part12LowAffine3Norm,scaled10Part13LowAffine3Norm,scaled10Part14LowAffine3Norm,scaled10Part15LowAffine3Norm,scaled10Part16LowAffine3Norm,scaled10Part17LowAffine3Norm,scaled10Part18LowAffine3Norm,scaled10Part19LowAffine3Norm,scaled10Part20LowAffine3Norm,scaled10Part21LowAffine3Norm,scaled10Part22LowAffine3Norm,midScaled10Affine3Norm,upperScaled10Affine3Norm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


end
end HTGeometry.ThetaRatioInfinity
