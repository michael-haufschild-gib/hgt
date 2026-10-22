import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectMoments

/-!
# Ordinary point-and-ray kernel for C5 defect growth

The coefficients are those of (q+9) S - (q+3/2) q S' for a moment or
cumulant chain with derivative m_j' = -m_(j+1). The exact integrated
point-and-ray polynomial is strictly positive for q >= 3/2, d >= 3.
This polynomial sign does not assert the complete cumulant inequality;
nonlinear correction and the exact modular-center cancellation remain.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section

def coolingCoefficientJet (q : ℝ) : ℕ → ℝ
  | 2 => 48
  | 3 => -36*(2*q+3)-24*(4*(q+3/2)+(4*q+15))
  | 4 => 44*((2*q+3)*(q+3/2)+q*(q+3))+40*(q+3/2)^2+20*(4*q+15)*(q+3/2)
  | 5 => -13*((2*q+3)*(q+3/2)^2+2*q*(q+3)*(q+3/2))-4*(q+3/2)^3-3*(4*q+15)*(q+3/2)^2
  | 6 => (2*q+3)*(q+3/2)^3+3*q*(q+3)*(q+3/2)^2
  | _ => 0

def growthCoefficient (q : ℝ) (j : ℕ) : ℝ :=
  (q+9)*coolingCoefficient q j-(q+3/2)*q*coolingCoefficientJet q j+
    (q+3/2)*q*coolingCoefficient q (j-1)

def momentNumeratorSeven (q d : ℝ) : ℝ :=
  (d+1)*d^6*q^8+(3/2)*(d^7*q^7+7*d^6*q^6+42*d^5*q^5+210*d^4*q^4+
    840*d^3*q^3+2520*d^2*q^2+5040*d*q+5040)

def growthKernel (q d : ℝ) : ℝ :=
  growthCoefficient q 2*momentNumeratorTwo q d*q^5+
  growthCoefficient q 3*momentNumeratorThree q d*q^4+
  growthCoefficient q 4*momentNumeratorFour q d*q^3+
  growthCoefficient q 5*momentNumeratorFive q d*q^2+
  growthCoefficient q 6*momentNumeratorSix q d*q+
  growthCoefficient q 7*momentNumeratorSeven q d

theorem growthKernel_shift_pos (y v : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    0 < growthKernel (3/2+y) (3+v) := by
  unfold growthKernel growthCoefficient
  norm_num [coolingCoefficient,coolingCoefficientJet]
  unfold momentNumeratorTwo momentNumeratorThree momentNumeratorFour
    momentNumeratorFive momentNumeratorSix momentNumeratorSeven
  ring_nf
  positivity

theorem growthKernel_pos {q d : ℝ} (hq : 3/2 ≤ q) (hd : 3 ≤ d) :
    0 < growthKernel q d := by
  have h := growthKernel_shift_pos (q-3/2) (d-3) (by linarith) (by linarith)
  simpa only [show 3/2+(q-3/2)=q by ring, show 3+(d-3)=d by ring] using h
end
end RHTower.ThetaCuspDefect
