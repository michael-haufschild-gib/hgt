import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioAxisSlope

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def axisMoment2CompleteNorm : {P : Polynomial ℂ // axis scaledMoment2=P} := by
  have he : axis scaledMoment2=axis scaledMoment2 := rfl
  conv at he =>
    rhs
    norm_num [axis,axisCoord,scaledMoment2,low2,midScaled2,upperScaled2,driftSquare,deficit,scaled2Part0Low,scaled2Part1Low,Finset.sum_range_succ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def axisMoment4CompleteNorm : {P : Polynomial ℂ // axis scaledMoment4=P} := by
  have he : axis scaledMoment4=axis scaledMoment4 := rfl
  conv at he =>
    rhs
    norm_num [axis,axisCoord,scaledMoment4,low4,midScaled4,upperScaled4,driftSquare,deficit,scaled4Part0Low,scaled4Part1Low,scaled4Part2Low,scaled4Part3Low,Finset.sum_range_succ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def axisMoment6CompleteNorm : {P : Polynomial ℂ // axis scaledMoment6=P} := by
  have he : axis scaledMoment6=axis scaledMoment6 := rfl
  conv at he =>
    rhs
    norm_num [axis,axisCoord,scaledMoment6,low6,midScaled6,upperScaled6,driftSquare,deficit,scaled6Part0Low,scaled6Part1Low,scaled6Part2Low,scaled6Part3Low,scaled6Part4Low,scaled6Part5Low,scaled6Part6Low,scaled6Part7Low,Finset.sum_range_succ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def axisMoment2ValueNorm (h : ℂ) : {c : ℂ // (axis scaledMoment2).eval h=c} := by
  have he : (axis scaledMoment2).eval h=(axis scaledMoment2).eval h := rfl
  conv at he =>
    rhs
    rw [axisMoment2CompleteNorm.property]
    norm_num [axisMoment2CompleteNorm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def axisMoment4ValueNorm (h : ℂ) : {c : ℂ // (axis scaledMoment4).eval h=c} := by
  have he : (axis scaledMoment4).eval h=(axis scaledMoment4).eval h := rfl
  conv at he =>
    rhs
    rw [axisMoment4CompleteNorm.property]
    norm_num [axisMoment4CompleteNorm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def axisMoment6ValueNorm (h : ℂ) : {c : ℂ // (axis scaledMoment6).eval h=c} := by
  have he : (axis scaledMoment6).eval h=(axis scaledMoment6).eval h := rfl
  conv at he =>
    rhs
    rw [axisMoment6CompleteNorm.property]
    norm_num [axisMoment6CompleteNorm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def axisMoment8ValueNorm (h : ℂ) : {c : ℂ // (axis scaledMoment8).eval h=c} := by
  have he : (axis scaledMoment8).eval h=(axis scaledMoment8).eval h := rfl
  conv at he =>
    rhs
    rw [axisMoment8Norm.property]
    norm_num [axisMoment8Norm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def axisMoment10ValueNorm (h : ℂ) : {c : ℂ // (axis scaledMoment10).eval h=c} := by
  have he : (axis scaledMoment10).eval h=(axis scaledMoment10).eval h := rfl
  conv at he =>
    rhs
    rw [axisMoment10Norm.property]
    norm_num [axisMoment10Norm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
