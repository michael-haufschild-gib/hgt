import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularMasterCurrent

/-! Radial stream profiles through the third derivative and their complete two-jets. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMModularCore
open D4BMVectorStream D4BMScalarLinearEquation
noncomputable section

/-- The two radial factors of the complete forced stream. -/
def streamRadialValue (_w r B : ℂ) (square : Bool) : ℂ :=
  if square then B/r^(2 : ℕ) else B

def streamRadialFirst (w r B : ℂ) (square : Bool) : ℂ :=
  if square then B*(-2/r^(3 : ℕ)+w/(r^(3 : ℕ)*(r^(2 : ℕ)-1))) else B*w/(r*(r^(2 : ℕ)-1))

def streamRadialSecond (w r B : ℂ) (square : Bool) : ℂ :=
  if square then B*(6/r^(4 : ℕ)-4*w/(r^(4 : ℕ)*(r^(2 : ℕ)-1))+
    (w^(2 : ℕ)-w*(3*r^(2 : ℕ)-1))/(r^(4 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ)))
  else B*(w^(2 : ℕ)-w*(3*r^(2 : ℕ)-1))/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ))

/-- The complete third derivative coefficient, required by the reconstructed metric two-jet. -/
def streamRadialThird (w r B : ℂ) (square : Bool) : ℂ :=
  let a := w/(r*(r^(2 : ℕ)-1))
  let b := (w^(2 : ℕ)-w*(3*r^(2 : ℕ)-1))/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ))
  let c := (w^(3 : ℕ)-3*w^(2 : ℕ)*(3*r^(2 : ℕ)-1)+w*(12*r^(4 : ℕ)-6*r^(2 : ℕ)+2))/(r^(3 : ℕ)*(r^(2 : ℕ)-1)^(3 : ℕ))
  if square then B*(c/r^(2 : ℕ)-6*b/r^(3 : ℕ)+18*a/r^(4 : ℕ)-24/r^(5 : ℕ)) else B*c

/-- Full product jet of the two original radial factors. -/
def streamRadialProductJet (w r B : ℂ) (square : Bool) : ScalarTwoJet (Fin 4) ℂ :=
  let E := temporalRadial w r B
  let U := (coord r 1).inv
  if square then E.mul (U.mul U) else E

/-- Full product jet of their explicit first radial derivatives. -/
def streamRadialDerivativeJet (w r B : ℂ) (square : Bool) : ScalarTwoJet (Fin 4) ℂ :=
  let E := temporalRadial w r B
  let R := coord r 1
  let U := R.inv
  let F := (R.mul R).add (constant (-1))
  let D := ((constant w).mul E).mul (U.mul F.inv)
  if square then (D.mul (U.mul U)).add (((constant (-2)).mul E).mul (U.mul (U.mul U))) else D

set_option maxRecDepth 2048 in
/-- The full radial product jet retains the actual first and second coefficient slots. -/
theorem streamRadialProductJet_eq (w r B : ℂ) (square : Bool) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    streamRadialProductJet w r B square = radialJet w (streamRadialValue w r B square)
      (streamRadialFirst w r B square) (streamRadialSecond w r B square) := by
  cases square <;> apply ScalarTwoJet.ext
  all_goals first | (funext i j; fin_cases i <;> fin_cases j) | (funext i; fin_cases i) | skip
  all_goals simp [streamRadialProductJet,temporalRadial,radialJet,streamRadialValue,
    streamRadialFirst,streamRadialSecond,ScalarTwoJet.mul,ScalarTwoJet.inv,coord]
  all_goals try simp only [← pow_two,← sub_eq_add_neg]
  all_goals field_simp [hr,hf]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
private theorem base_derivative_jet (w r B : ℂ) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    streamRadialDerivativeJet w r B false = radialJet w (streamRadialFirst w r B false)
      (streamRadialSecond w r B false) (streamRadialThird w r B false) := by
  apply ScalarTwoJet.ext
  all_goals first | (funext i j; fin_cases i <;> fin_cases j) | (funext i; fin_cases i) | skip
  all_goals simp [streamRadialDerivativeJet,temporalRadial,radialJet,streamRadialFirst,
    streamRadialSecond,streamRadialThird,ScalarTwoJet.mul,ScalarTwoJet.inv,ScalarTwoJet.add,
    constant,coord]
  all_goals try simp only [← pow_two,← sub_eq_add_neg]
  all_goals field_simp [hr,hf]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
/-- The derivative jet contains the full third radial derivative and both mixed time derivatives. -/
theorem streamRadialDerivativeJet_eq (w r B : ℂ) (square : Bool) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    streamRadialDerivativeJet w r B square = radialJet w (streamRadialFirst w r B square)
      (streamRadialSecond w r B square) (streamRadialThird w r B square) := by
  cases square
  · exact base_derivative_jet w r B hr hf
  · change ((streamRadialDerivativeJet w r B false).mul ((coord r 1).inv.mul (coord r 1).inv)).add
      (((constant (-2)).mul (temporalRadial w r B)).mul
        ((coord r 1).inv.mul ((coord r 1).inv.mul (coord r 1).inv))) = _
    rw [base_derivative_jet w r B hr hf]
    apply ScalarTwoJet.ext
    all_goals first | (funext i j; fin_cases i <;> fin_cases j) | (funext i; fin_cases i) | skip
    all_goals simp [temporalRadial,radialJet,streamRadialFirst,streamRadialSecond,streamRadialThird,
      ScalarTwoJet.mul,ScalarTwoJet.inv,ScalarTwoJet.add,constant,coord]
    all_goals try simp only [← pow_two,← sub_eq_add_neg]
    all_goals field_simp [hr,hf]
    all_goals ring

end
end RHTower.D4BMModularCore
