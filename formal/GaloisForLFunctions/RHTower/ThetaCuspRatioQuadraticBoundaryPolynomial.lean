import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierAlgebra

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

def boundaryC0 (h : ℝ) : ℝ := 1/9-h/36-7*h^2/324
def boundaryC1 (h : ℝ) : ℝ := -5/6+20*h/27+89*h^2/324-7*h^3/324
def boundaryC2 (h : ℝ) : ℝ := 32/3-193*h/36-37*h^2/12
def boundaryC3 (h : ℝ) : ℝ := -24-8*h+2*h^2
def boundaryPoly (h w : ℝ) : ℝ :=
  boundaryC0 h*(1-w)^3+boundaryC1 h*(1-w)^2+
    b h*boundaryC2 h*(1-w)+(b h)^2*boundaryC3 h

theorem boundary_core_polynomial (h w : ℝ) (hb : b h≠0) (hw : 1-w≠0) :
    (1-w)^2*quadraticBoundaryCore h (9-w*(1-w)/b h) (b h/(1-w))=
      boundaryPoly h w := by
  unfold quadraticBoundaryCore D A fieldH boundaryPoly boundaryC0 boundaryC1 boundaryC2 boundaryC3
  field_simp [hb,hw]
  unfold b
  ring

end
end HTGeometry.ThetaCriticalBarrier
namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

def pTail (h : ℝ) : ℝ := -7*h/16+125*h^2/288+49*h^3/288+49*h^4/2592
def pWUpper (h : ℝ) : ℝ :=
  4/9+253*h/1296+(-647/864+17/486)*h^2-665*h^3/2592

end
end HTGeometry.ThetaCriticalBarrier
