import GaloisForLFunctions.RHTower.ThetaCuspRatioNonlinearBoundaryParameter
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.SplitRe
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.SplitIm
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryLowValue76 (h s : ℂ) : ℂ :=
  boundaryReLow76 h (nonlinearBoundaryR h s)+
    h*nonlinearBoundaryZ h s*boundaryImLow76 h (nonlinearBoundaryR h s)

def boundaryLowValue76Norm (h s : ℂ) : {c : ℂ // boundaryLowValue76 h s=c} := by
  have he : boundaryLowValue76 h s=boundaryLowValue76 h s := rfl
  conv at he =>
    rhs
    norm_num [boundaryLowValue76,boundaryReLow76,boundaryReLowColumn76_0,boundaryReLowColumn76_1,boundaryReLowColumn76_2,boundaryReLowColumn76_3,boundaryReLowColumn76_4,boundaryReLowColumn76_5,boundaryReLowColumn76_6,boundaryReLowColumn76_7,boundaryReLowColumn76_8,boundaryReLowColumn76_9,boundaryReLowColumn76_10,boundaryReLowColumn76_11,boundaryReLowColumn76_12,boundaryReLowColumn76_13,boundaryReLowColumn76_14,boundaryReLowColumn76_15,boundaryReLowColumn76_16,boundaryReLowColumn76_17,boundaryReLowColumn76_18,boundaryReLowColumn76_19,boundaryReLowColumn76_20,boundaryReLowColumn76_21,boundaryReLowColumn76_22,boundaryImLow76,boundaryImLowColumn76_0,boundaryImLowColumn76_1,boundaryImLowColumn76_2,boundaryImLowColumn76_3,boundaryImLowColumn76_4,boundaryImLowColumn76_5,boundaryImLowColumn76_6,boundaryImLowColumn76_7,boundaryImLowColumn76_8,boundaryImLowColumn76_9,boundaryImLowColumn76_10,boundaryImLowColumn76_11,boundaryImLowColumn76_12,boundaryImLowColumn76_13,boundaryImLowColumn76_14,boundaryImLowColumn76_15,boundaryImLowColumn76_16,boundaryImLowColumn76_17,boundaryImLowColumn76_18,boundaryImLowColumn76_19,boundaryImLowColumn76_20,boundaryImLowColumn76_21,
      nonlinearBoundaryR,nonlinearBoundaryT,nonlinearBoundaryZ,nonlinearBoundarySeed]
    try ring_nf (config := {mode := .raw})
  trace_state
  exact ⟨_,he⟩
end
end HTGeometry.ThetaRatioInfinity
