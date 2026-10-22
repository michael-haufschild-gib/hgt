import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthMoments
/-!
# Dominant binary curvature-defect growth cooling

The exact second-atom self-pair has positive relative-cooling numerator on
q >= 3/2. A stronger fixed one-unit reserve fails at q = 3/2.
The coefficients retain the ordinary moment chain through order eight.
Complete-source nonlinear absorption is a separate open target.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

def coolingCoefficientJetTwo (q : ℝ) : ℕ → ℝ
  | 2 => 0
  | 3 => -264
  | 4 => 504*q+936
  | 5 => -204*q^2-666*q-963/2
  | 6 => 20*q^3+90*q^2+(243/2)*q+189/4
  | _ => 0

def growthCoefficientJet (q : ℝ) (j : ℕ) : ℝ :=
  coolingCoefficient q j+(15/2-q)*coolingCoefficientJet q j-
    (q+3/2)*q*coolingCoefficientJetTwo q j+
    (2*q+3/2)*coolingCoefficient q (j-1)+(q+3/2)*q*coolingCoefficientJet q (j-1)

def growthSlope (q : ℝ) (m : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, (growthCoefficientJet q (j+2)*m (j+2)-growthCoefficient q (j+2)*m (j+3))

def binaryMoment (m n : ℕ → ℝ) : ℕ → ℝ
  | 2 => 2*m 1*n 1
  | 3 => 3*(m 1*n 2+m 2*n 1)
  | 4 => 4*(m 1*n 3+m 3*n 1)+6*m 2*n 2
  | 5 => 5*(m 1*n 4+m 4*n 1)+10*(m 2*n 3+m 3*n 2)
  | 6 => 6*(m 1*n 5+m 5*n 1)+15*(m 2*n 4+m 4*n 2)+20*m 3*n 3
  | 7 => 7*(m 1*n 6+m 6*n 1)+21*(m 2*n 5+m 5*n 2)+35*(m 3*n 4+m 4*n 3)
  | _ => 0

def binaryGrowth (q : ℝ) (m n : ℕ → ℝ) : ℝ := growthFunctional q (binaryMoment m n)
def binaryGrowthSlope (q : ℝ) (m n : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, (growthCoefficientJet q (j+2)*binaryMoment m n (j+2)-
    growthCoefficient q (j+2)*(binaryMoment (fun i=>m (i+1)) n (j+2)+
      binaryMoment m (fun i=>n (i+1)) (j+2)))

def polynomialMoment (q d : ℝ) (j : ℕ) : ℝ :=
  (d+1)*d^j*q^(j+1)+(3/2)*d*∑ i ∈ Finset.range (j+1),
    (j.choose i:ℝ)*d^(j-i)*(i.factorial:ℝ)*q^(j-i)
def binaryGrowthNumerator (q d e : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, growthCoefficient q (j+2)*q^(5-j)*
    binaryMoment (polynomialMoment q d) (polynomialMoment q e) (j+2)
def binarySlopeNumerator (q d e : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, (growthCoefficientJet q (j+2)*q^(6-j)*
    binaryMoment (polynomialMoment q d) (polynomialMoment q e) (j+2)-
    growthCoefficient q (j+2)*q^(5-j)*
      (binaryMoment (fun i=>polynomialMoment q d (i+1)) (polynomialMoment q e) (j+2)+
       binaryMoment (polynomialMoment q d) (fun i=>polynomialMoment q e (i+1)) (j+2)))
def growthNumerator (q d : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, growthCoefficient q (j+2)*q^(5-j)*polynomialMoment q d (j+2)
def slopeNumerator (q d : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, (growthCoefficientJet q (j+2)*q^(6-j)*polynomialMoment q d (j+2)-
    growthCoefficient q (j+2)*q^(5-j)*polynomialMoment q d (j+3))
def anchorCoolingNumerator (q d e : ℝ) : ℝ :=
  binaryGrowthNumerator q d e*slopeNumerator q 3-
    binarySlopeNumerator q d e*growthNumerator q 3
private theorem anchorCoolingNumerator_self_shift_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < anchorCoolingNumerator (3/2+y) 3 3 := by
  unfold anchorCoolingNumerator binaryGrowthNumerator binarySlopeNumerator growthNumerator slopeNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo,binaryMoment]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  apply sub_pos.mp
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem anchorCoolingNumerator_self_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < anchorCoolingNumerator q 3 3 := by
  have h := anchorCoolingNumerator_self_shift_pos (q-3/2) (by linarith)
  simpa only [show (3/2:ℝ)+(q-3/2)=q by ring] using h

/-- The proposed fixed one-unit reserve fails on the enlarged coordinate ray. -/
theorem anchorUnitReserve_threeHalves_neg :
    anchorCoolingNumerator (3/2) 3 3-
      (3/2)*binaryGrowthNumerator (3/2) 3 3*growthNumerator (3/2) 3 < 0 := by
  norm_num [anchorCoolingNumerator,binaryGrowthNumerator,binarySlopeNumerator,
    growthNumerator,slopeNumerator,growthCoefficient,growthCoefficientJet,
    coolingCoefficient,coolingCoefficientJet,coolingCoefficientJetTwo,binaryMoment,
    polynomialMoment,Finset.sum_range_succ,Nat.choose,Nat.factorial]
end
end RHTower.ThetaCuspDefect
