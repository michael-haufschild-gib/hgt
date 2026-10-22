import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCenterEndpoints
import Mathlib.Algebra.Polynomial.Derivative

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity Filter Topology
open RHTower.ThetaCuspModularRatio

def terminalWeightedCoord : Coord → Polynomial ℂ
  | .U => 9
  | .K => Polynomial.X
  | .J => Polynomial.C (1/3)

def terminalWeighted : Poly →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C terminalWeightedCoord

@[simp] theorem terminalWeighted_C (a : ℂ) :
    terminalWeighted (C a)=Polynomial.C a := by simp [terminalWeighted]

@[simp] theorem terminalWeighted_X (i : Coord) :
    terminalWeighted (X i)=terminalWeightedCoord i := by simp [terminalWeighted]

theorem terminalWeighted_eval (P : Poly) (k : ℂ) :
    Polynomial.eval k (terminalWeighted P)=eval (basePoint 9 k (1/3)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,terminalWeightedCoord,basePoint]

theorem terminalWeighted_field (i : Coord) : terminalWeighted (squareField i)=
    match i with
    | .U => 0
    | .K => 36*Polynomial.X+12
    | .J => 0 := by
  cases i <;> apply Polynomial.funext <;> intro k
  all_goals norm_num [squareField,terminalWeighted,terminalWeightedCoord] <;> ring

theorem terminalWeighted_flow (P : Poly) :
    terminalWeighted (squareLie P)=
      (36*Polynomial.X+12)*(terminalWeighted P).derivative := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [flow_C]
  | add p q hp hq =>
      simp only [flow_add,map_add,hp,hq]
      ring
  | mul_X p i hp =>
      simp only [flow_mul,flow_X,map_add,map_mul,Polynomial.derivative_mul,
        hp,terminalWeighted_field,terminalWeighted_X]
      cases i <;> simp [terminalWeightedCoord] <;> ring

def terminalWeightedJet : ℕ → Polynomial ℂ
  | 0 => 6*Polynomial.X-1
  | n+1 => (36*Polynomial.X+12)*(terminalWeightedJet n).derivative+
      9*(1-12*Polynomial.X)*terminalWeightedJet n

theorem terminalWeighted_jet (n : ℕ) :
    terminalWeighted (weightedJet n)=terminalWeightedJet n := by
  induction n with
  | zero =>
      simp only [weightedJet,terminalWeightedJet,map_sub,map_mul,map_ofNat,map_one,
        terminalWeighted_X,terminalWeightedCoord]
  | succ n ih =>
      simp only [weightedJet,map_add,map_sub,map_mul,map_natCast,map_ofNat,map_one,
        terminalWeighted_flow,terminalWeighted_X,terminalWeightedCoord,ih,
        terminalWeightedJet]
      ring

def terminalWeightedSlope (P : Polynomial ℂ) : Polynomial ℂ :=
  9*(36*Polynomial.X+12)*((6*Polynomial.X-1)*P.derivative-36*P)

theorem terminalWeighted_sixthSlope (m : ℕ) (P : Poly) :
    terminalWeighted (weightedSixthSlope m P)=
      terminalWeightedSlope (terminalWeighted P) := by
  simp only [weightedSixthSlope,map_sub,map_mul,map_natCast,map_ofNat,
    terminalWeighted_flow,terminalWeighted_X,terminalWeightedCoord,
    terminalWeighted_jet,terminalWeightedJet]
  norm_num [terminalWeightedSlope]
  ring

def terminalWeightedReflection (n : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i:Polynomial ℂ)*(-1:Polynomial ℂ)^(n-i)*
    terminalWeightedJet i*terminalWeightedJet (n-i)

theorem terminalWeighted_reflection (n : ℕ) :
    terminalWeighted (weightedReflection n)=terminalWeightedReflection n := by
  simp only [weightedReflection,terminalWeightedReflection,map_sum,map_mul,map_pow,
    map_natCast,map_neg,map_one,terminalWeighted_jet]

def terminalWeightedMoment (r : ℕ) : Polynomial ℂ :=
  (-1:Polynomial ℂ)^r*terminalWeightedReflection (2*r)

theorem terminalWeighted_moment (r : ℕ) :
    terminalWeighted (weightedMoment r)=terminalWeightedMoment r := by
  simp only [weightedMoment,terminalWeightedMoment,map_mul,map_pow,map_neg,map_one,
    terminalWeighted_reflection]

end
end HTGeometry.ThetaRatioWeightedSquare
