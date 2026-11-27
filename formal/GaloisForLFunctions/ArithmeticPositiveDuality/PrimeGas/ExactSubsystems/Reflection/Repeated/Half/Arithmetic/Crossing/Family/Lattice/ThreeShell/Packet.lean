import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse.Temperature

/-! # An exact signed partition threshold on three fixed powers of one prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell

open Finset Real
open _root_.HTGeometry (finiteGibbsPartition)

/-- Occupation numbers 0, 3 and 5 have multiplicities A+2B, 2A+B and B. -/
abbrev States (A B : ℕ) := Fin (A+2*B) ⊕ (Fin (2*A+B) ⊕ Fin B)

def occupation (A B : ℕ) : States A B → ℕ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 3) (fun _ => 5))

private def displacement (A B : ℕ) : States A B → ℝ :=
  Sum.elim (fun _ => -2) (Sum.elim (fun _ => 1) (fun _ => 3))

private theorem centered_occupations (A B : ℕ) : centered (levels (occupation A B))=displacement A B := by
  have zero : (∑ i, displacement A B i)=0 := by
    simp only [displacement,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have shift : levels (occupation A B)=fun i => 1*displacement A B i+2 := by
    funext i
    rcases i with i | (i | i) <;> norm_num [levels,occupation,displacement]
  rw [shift,centered_affine,centered_eq_of_sum_zero zero]
  simp only [one_mul]

private theorem second (x : ℝ) : oddTerm x 2=(exp x-exp (-x))*coordinate x := by
  simp only [oddTerm,coordinate,mul_two,exp_add]
  ring

private theorem third (x : ℝ) : oddTerm x 3=(exp x-exp (-x))*(coordinate x^2-1) := by
  have unit : exp x*exp (-x)=1 := by rw [← exp_add,add_neg_cancel,exp_zero]
  simp only [oddTerm,coordinate,show (3 : ℝ)=2+1 from by ring,mul_add,mul_one,mul_two,exp_add]
  linear_combination -(exp x-exp (-x))*unit

/-- The centered heat asymmetry of a packet of actual integer shells. -/
def response (p : Nat.Primes) (A B : ℕ) (t : ℝ) :=
  oddTrace (centered (primeModes p (occupation A B))) t

theorem response_partitions (p : Nat.Primes) (A B : ℕ) (t : ℝ) :
    response p A B t=finiteGibbsPartition (-t) (centered (primeModes p (occupation A B)))-
      finiteGibbsPartition t (centered (primeModes p (occupation A B))) := oddTrace_eq _ _

/-- Translating by two occupations centers the packet. Its response is
the universal odd factor times a linear polynomial in twice the hyperbolic cosine. -/
theorem response_eq (p : Nat.Primes) (A B : ℕ) (t : ℝ) :
    response p A B t=base (t*log p.val)*((B : ℝ)*coordinate (t*log p.val)-(A : ℝ)) := by
  let x := t*log p.val
  have scale (z : ℝ) : oddTerm t (log p.val*z)=oddTerm x z := by
    simp only [oddTerm,x,neg_mul,mul_assoc]
  have neg : oddTerm x (-2)= -oddTerm x 2 := by
    simp only [oddTerm,mul_neg,neg_mul,neg_neg,neg_sub]
  rw [response,Sparse.mode_grid,centered_affine,centered_occupations]
  simp only [oddTrace,scale,displacement,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    neg,second,third]
  change _=base x*((B : ℝ)*coordinate x-(A : ℝ))
  simp only [oddTerm,mul_one,base]
  ring

#print axioms response_eq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell
