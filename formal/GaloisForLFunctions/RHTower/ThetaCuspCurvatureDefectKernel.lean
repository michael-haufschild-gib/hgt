import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSpectralMeasure
/-!
# Coupled point-and-ray kernel for curvature-defect cooling

The normalized fifth-minus-third likelihood response has a sixth-order
cooling kernel. Pointwise spectral support does not give its sign.
After integrating one literal point-and-ray theta component, its cleared
polynomial is strictly positive on the entire source domain.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section
def momentNumeratorTwo (q d : ℝ) : ℝ :=
  (d+1)*d*q^3 + (3/2)*(d^2*q^2+2*d*q+2)
def momentNumeratorThree (q d : ℝ) : ℝ :=
  (d+1)*d^2*q^4 + (3/2)*(d^3*q^3+3*d^2*q^2+6*d*q+6)
def momentNumeratorFour (q d : ℝ) : ℝ :=
  (d+1)*d^3*q^5 + (3/2)*(d^4*q^4+4*d^3*q^3+12*d^2*q^2+24*d*q+24)
def momentNumeratorFive (q d : ℝ) : ℝ :=
  (d+1)*d^4*q^6 + (3/2)*(d^5*q^5+5*d^4*q^4+20*d^3*q^3+60*d^2*q^2+120*d*q+120)
def momentNumeratorSix (q d : ℝ) : ℝ :=
  (d+1)*d^5*q^7 + (3/2)*(d^6*q^6+6*d^5*q^5+30*d^4*q^4+120*d^3*q^3+360*d^2*q^2+720*d*q+720)
def normalizedDefectCoolingKernel (q d : ℝ) : ℝ :=
  (q+3)*((q+3/2)^3*momentNumeratorSix q d-13*q*(q+3/2)^2*momentNumeratorFive q d+
    44*q^2*(q+3/2)*momentNumeratorFour q d-36*q^3*momentNumeratorThree q d)-
  (4*q+15)*((q+3/2)^3*momentNumeratorFive q d-10*q*(q+3/2)^2*momentNumeratorFour q d+
    24*q^2*(q+3/2)*momentNumeratorThree q d-12*q^3*momentNumeratorTwo q d)
private theorem normalizedDefectCoolingKernel_shift_pos (y v : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    0 < normalizedDefectCoolingKernel (3/2+y) (3+v) := by
  unfold normalizedDefectCoolingKernel momentNumeratorTwo momentNumeratorThree momentNumeratorFour momentNumeratorFive momentNumeratorSix
  ring_nf
  positivity
theorem normalizedDefectCoolingKernel_pos {q d : ℝ} (hq : 3/2 ≤ q) (hd : 3 ≤ d) :
    0 < normalizedDefectCoolingKernel q d := by
  have h := normalizedDefectCoolingKernel_shift_pos (q-3/2) (d-3) (by linarith) (by linarith)
  simpa only [show 3/2+(q-3/2)=q by ring, show 3+(d-3)=d by ring] using h
end
end RHTower.ThetaCuspDefect
