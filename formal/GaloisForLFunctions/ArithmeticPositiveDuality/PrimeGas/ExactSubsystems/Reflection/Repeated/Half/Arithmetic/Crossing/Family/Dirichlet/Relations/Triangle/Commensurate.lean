import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.RelativeCoordinates
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.Exponents

/-! # Commensurate energy gaps in a three-shell relation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real Polynomial
open scoped Polynomial

private theorem common_frequency {E F : ℝ} (e : 0<E) (f : 0<F) (dep : ¬independentGaps E F) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ E*b=F*a := by
  unfold independentGaps at dep
  push Not at dep
  obtain ⟨i,j,eq,nontrivial⟩ := dep
  have nz : i ≠ 0 := by
    intro z
    rw [z,Int.cast_zero,zero_mul,zero_add] at eq
    have jz := Int.cast_eq_zero.mp ((mul_eq_zero.mp eq).resolve_right f.ne')
    simp_all
  let q := -(j : ℚ)/i
  have qeq : (q : ℝ)=E/F := by
    simp only [q,Rat.cast_div,Rat.cast_neg,Rat.cast_intCast]
    apply (div_eq_div_iff (Int.cast_ne_zero.mpr nz) f.ne').mpr
    linear_combination -eq
  have qp : 0<q := Rat.cast_pos.mp (by rw [qeq]; exact div_pos e f)
  obtain ⟨a,b,ha,hb,rep⟩ := natural_ratio q qp
  rw [qeq] at rep
  refine ⟨a,b,ha,hb,?_⟩
  field_simp [f.ne'] at rep
  linear_combination rep

/-- Positive commensurate gaps turn a signed triangle into a univariate
polynomial. Its nonzero constant term ensures algebraicity at the source. -/
theorem commensurate_coordinate {E F : ℝ} (e : 0<E) (f : 0<F) (dep : ¬independentGaps E F)
    (A B : ℚ) (t : ℝ) (eq : (A : ℝ)*exp (t*E)+(B : ℝ)*exp (t*F)=1) :
    IsAlgebraic ℚ (exp (t*E)) := by
  obtain ⟨a,b,ha,hb,rel⟩ := common_frequency e f dep
  let r := exp (t*F/b)
  have bn : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have x : r^a=exp (t*E) := by
    rw [← exp_nat_mul]
    apply congrArg exp
    field_simp [bn]
    linear_combination -t*rel
  have y : r^b=exp (t*F) := by
    rw [← exp_nat_mul,mul_div_cancel₀ _ bn]
  let P : ℚ[X] := C A*X^a+C B*X^b-1
  have root : Polynomial.aeval r P=0 := by
    simp only [P,map_sub,map_add,map_mul,aeval_C,map_pow,aeval_X,map_one,x,y]
    exact sub_eq_zero.mpr eq
  have nonzero : P ≠ 0 := by
    intro zero
    have impossible := congrArg (Polynomial.eval (0 : ℚ)) zero
    simp [P,zero_pow ha.ne',zero_pow hb.ne'] at impossible
  rw [← x]
  exact (show IsAlgebraic ℚ r from ⟨P,nonzero,root⟩).pow a

#print axioms commensurate_coordinate

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
