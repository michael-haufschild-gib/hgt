import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # A five-pulse polynomial for an uninitialized control qubit -/

open Matrix
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.BorrowedWire
noncomputable section

/-- A two-state pulse with equal diagonal entries. Keeping the two
off-diagonal variables separate makes the polynomial identity explicit. -/
def pulse (x u v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![x,u;-v,x]

private theorem sandwich (x u v y b c : ℂ) :
    pulse x u v*pulse y b c*pulse x u v =
      pulse (y*(x^2-u*v)-x*(u*c+v*b))
        (2*x*y*u+x^2*b-u^2*c) (2*x*y*v+x^2*c-v^2*b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pulse,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

/-- The two phase multipliers of the palindrome have sum -1/2
and product one; these identities fix its scalar response. -/
theorem five_pulse (x u v a b : ℂ) (hs : a+b= -(1/2)) (hp : a*b=1)
    (hunit : x^2+u*v=1) :
    let A := pulse x (a*u) (b*v)
    let B := pulse x (b*u) (a*v)
    let Q := A*(B*pulse x u v*B)*A
    let q := u*v
    ∃ U V : ℂ, Q=pulse (x*(1+q/2+3*q^2/8)) U V := by
  intro A B Q q
  have hs₂ : a^2+b^2= -(7/4) := by
    linear_combination (a+b-1/2)*hs - 2*hp
  have hs₃ : a^3+b^3=11/8 := by
    linear_combination (a^2-a*b+b^2-(a+b)/2+1/4)*hs + (3/2)*hp
  let Y := x*(x^2-(b*u)*(a*v))-x*((b*u)*v+(a*v)*u)
  let U := 2*x*x*(b*u)+x^2*u-(b*u)^2*v
  let V := 2*x*x*(a*v)+x^2*v-(a*v)^2*u
  have hY : Y=x*(x^2-q/2) := by
    dsimp only [Y,q]
    linear_combination -x*u*v*hp - x*u*v*hs
  have hpair : (a*u)*V+(b*v)*U=q*(-4*x^2-11*q/8) := by
    dsimp only [U,V,q]
    linear_combination 2*x^2*u*v*hs₂ + x^2*u*v*hs - (u*v)^2*hs₃
  have hab : (a*u)*(b*v)=q := by
    dsimp only [q]; linear_combination u*v*hp
  have hdiag : Y*(x^2-(a*u)*(b*v))-x*((a*u)*V+(b*v)*U) = x*(1+q/2+3*q^2/8) := by
    rw [hY,hab,hpair]
    have hx : x^2=1-q := by dsimp only [q]; linear_combination hunit
    rw [hx]
    ring
  dsimp only [Q,A,B]
  rw [sandwich x (b*u) (a*v) x u v]
  change ∃ U' V', pulse x (a*u) (b*v)*pulse Y U V*pulse x (a*u) (b*v)=_
  rw [sandwich,hdiag]
  exact ⟨_,_,rfl⟩

/-- Five pulses remove the first two powers of the squared leakage.
The new leakage amplitude is at most the cube of the old amplitude. -/
theorem five_pulse_leakage {x q : ℝ} (hx : 0≤x) (hq : 0≤q) (hu : x^2+q=1) :
    let y := x*(1+q/2+3*q^2/8)
    0≤y ∧ 1-y^2=q^3*(40+15*q+9*q^2)/64 ∧ 1-y^2≤q^3 := by
  intro y
  have hq₁ : q≤1 := by linarith only [hu,sq_nonneg x]
  have he : 1-y^2=q^3*(40+15*q+9*q^2)/64 := by
    change 1-(x*(1+q/2+3*q^2/8))^2=_
    rw [mul_pow,show x^2=1-q by linarith only [hu]]
    ring
  refine ⟨mul_nonneg hx (by positivity),he,?_⟩
  rw [he]
  have hs : q^2≤1 := pow_le_one₀ hq hq₁
  have h := mul_le_mul_of_nonneg_left (show 40+15*q+9*q^2≤64 by linarith only [hq₁,hs]) (pow_nonneg hq 3)
  linarith only [h]

#print axioms five_pulse
#print axioms five_pulse_leakage
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.BorrowedWire
