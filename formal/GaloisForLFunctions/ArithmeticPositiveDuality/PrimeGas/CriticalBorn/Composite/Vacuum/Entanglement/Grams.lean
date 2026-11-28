import GaloisForLFunctions.HTGeometry.Thermofield.EntropyApplications

/-! # Two Schmidt weights of a single excitation shared between two copies -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement

open Finset Matrix Real
open GaloisForLFunctions.HTGeometry
open scoped Matrix ComplexConjugate

variable {I J : Type*} [Fintype I] [Fintype J]

def mass {A : Type*} [Fintype A] (u : A → ℂ) := ∑ i, ‖u i‖^2

/-- The excitation may occupy either side of the vacuum. -/
def shared (u : J → ℂ) (v : I → ℂ) : Option I × Option J → ℂ
  | (none,some j) => u j
  | (some i,none) => v i
  | _ => 0

/-- Two columns suffice to factor the full reduced density matrix. -/
def columns (u : J → ℂ) (v : I → ℂ) : Matrix (Option I) Bool ℂ
  | none,false => (sqrt (mass u):ℂ)
  | some i,true => v i
  | _,_ => 0

def eigenWeights (u : J → ℂ) (v : I → ℂ) : Bool → ℝ
  | false => mass u
  | true => mass v

private theorem sum_conj {A : Type*} [Fintype A] (u : A → ℂ) :
    ∑ i, u i*star (u i)=(mass u:ℂ) := by
  simp only [mass,Complex.star_def,Complex.mul_conj',Complex.ofReal_sum,Complex.ofReal_pow]

private theorem sqrt_square {A : Type*} [Fintype A] (u : A → ℂ) :
    (sqrt (mass u):ℂ)*(sqrt (mass u):ℂ)=(mass u:ℂ) := by
  have h : 0 ≤ mass u := sum_nonneg fun i _ => sq_nonneg ‖u i‖
  rw [←Complex.ofReal_mul,Real.mul_self_sqrt h]

omit [Fintype I] in
theorem left_gram (u : J → ℂ) (v : I → ℂ) :
    pureStateReducedLeft (shared u v)=columns u v*(columns u v)ᴴ := by
  ext i j
  cases i <;> cases j <;>
    simp [pureStateReducedLeft_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      shared,columns,Fintype.sum_option,sqrt_square]
  exact sum_conj u

theorem two_levels (u : J → ℂ) (v : I → ℂ) :
    (columns u v)ᴴ*columns u v=diagonal (fun b => (eigenWeights u v b:ℂ)) := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,columns,eigenWeights,
      Fintype.sum_option,sqrt_square,mul_comm]
  exact sum_conj v

/-- Exact purity with both marginal weights and their multiplicities. -/
theorem shared_purity (u : J → ℂ) (v : I → ℂ) :
    Matrix.trace (pureStateReducedLeft (shared u v)*pureStateReducedLeft (shared u v))=
      (((mass u)^2+(mass v)^2:ℝ):ℂ) := by
  classical
  let B := columns u v
  rw [left_gram]
  change trace ((B*Bᴴ)*(B*Bᴴ))=_
  calc
    _ = trace (B*(Bᴴ*(B*Bᴴ))) := by rw [Matrix.mul_assoc]
    _ = trace ((Bᴴ*(B*Bᴴ))*B) := trace_mul_comm _ _
    _ = trace ((Bᴴ*B)*(Bᴴ*B)) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      dsimp only [B]
      rw [two_levels,diagonal_mul_diagonal,trace_diagonal,Fintype.sum_bool]
      simp [eigenWeights,Complex.ofReal_add,sq,add_comm]

private theorem entropy_congr {A : Type*} [Fintype A] [DecidableEq A] {P Q : Matrix A A ℂ}
    (eq : P=Q) (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    finiteMatrixVonNeumannEntropy P hP=finiteMatrixVonNeumannEntropy Q hQ := by subst Q; rfl

/-- The spectral von Neumann entropy reduces to the two occupied levels
even when each output space contains arbitrarily many elementary modes. -/
theorem shared_entropy [DecidableEq I] (u : J → ℂ) (v : I → ℂ) :
    finiteMatrixVonNeumannEntropy (pureStateReducedLeft (shared u v))
      (pureStateReducedLeft_isHermitian _) =
    -(mass u*log (mass u))-(mass v*log (mass v)) := by
  classical
  let B := columns u v
  let w := eigenWeights u v
  calc
    _ = finiteMatrixVonNeumannEntropy (B*Bᴴ) (Matrix.isHermitian_mul_conjTranspose_self B) :=
      entropy_congr (left_gram u v) _ _
    _ = _ := finiteMatrixVonNeumannEntropy_mul_conjTranspose_eq_conjTranspose_mul B
    _ = finiteMatrixVonNeumannEntropy (diagonal fun i => (w i:ℂ)) (Thermofield.realDiagonal_isHermitian w) :=
      entropy_congr (two_levels u v) _ _
    _ = _ := by
      rw [Thermofield.vonNeumannEntropy_real_diagonal]
      simp [GaloisForLFunctions.HTGeometry.entropy,tsum_fintype,w,eigenWeights,sub_eq_add_neg,add_comm]

#print axioms left_gram
#print axioms two_levels
#print axioms shared_purity
#print axioms shared_entropy

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement
