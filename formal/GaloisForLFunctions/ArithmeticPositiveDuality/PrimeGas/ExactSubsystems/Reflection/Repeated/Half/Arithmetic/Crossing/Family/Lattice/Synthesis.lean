import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Flow

/-! # Integer-polynomial thermal responses from direct sums and tensor products -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice

open Finset Real Polynomial

def coordinate (t : ℝ) := exp t + exp (-t)
def base (t : ℝ) := (exp t-exp (-t))*(coordinate t-2)

def trace {I : Type*} [Fintype I] (k : I → ℤ) (t : ℝ) :=
  oddTrace (fun i => (k i : ℝ)) t

/-- A centered finite integer spectrum, with one state for each occurrence of a level. -/
def Realized (f : ℝ → ℝ) := ∃ (n : ℕ) (k : Fin n → ℤ), (∑ i, k i)=0 ∧ ∀ t, trace k t=f t

private theorem pack {I : Type*} [Fintype I] {k : I → ℤ} {f : ℝ → ℝ}
    (zero : ∑ i, k i=0) (eq : ∀ t, trace k t=f t) : Realized f := by
  let e := (Fintype.equivFin I).symm
  refine ⟨_,k ∘ e,(Equiv.sum_comp e k).trans zero,fun t => ?_⟩
  exact (Equiv.sum_comp e (fun i => oddTerm t (k i))).trans (eq t)

private theorem realized_add {f g : ℝ → ℝ} (hf : Realized f) (hg : Realized g) :
    Realized (f+g) := by
  obtain ⟨_,a,za,ea⟩ := hf
  obtain ⟨_,b,zb,eb⟩ := hg
  refine pack (k := Sum.elim a b) ?_ (fun t => ?_)
  · simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,za,zb,add_zero]
  · simpa only [trace,oddTrace,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.add_apply] using congrArg₂ (·+·) (ea t) (eb t)

private theorem realized_neg {f : ℝ → ℝ} (hf : Realized f) : Realized (-f) := by
  obtain ⟨_,k,zk,eq⟩ := hf
  refine pack (k := fun i => -k i) (by rw [sum_neg_distrib,zk,neg_zero]) (fun t => ?_)
  have neg (x : ℝ) : oddTerm t (-x) = -oddTerm t x := by
    simp only [oddTerm,mul_neg,neg_mul,neg_neg,neg_sub]
  simpa only [trace,oddTrace,Int.cast_neg,neg,sum_neg_distrib,Pi.neg_apply] using congrArg Neg.neg (eq t)

private def responses : AddSubgroup (ℝ → ℝ) where
  carrier := {f | Realized f}
  zero_mem' := ⟨0,Fin.elim0,by simp,fun t => by simp [trace,oddTrace]⟩
  add_mem' := realized_add
  neg_mem' := realized_neg

private theorem step (t x : ℝ) :
    oddTerm t (x+1)+oddTerm t (x-1) = coordinate t*oddTerm t x := by
  simp only [oddTerm,coordinate,sub_eq_add_neg,mul_add,mul_neg,mul_one,neg_neg,exp_add]
  ring

/-- Tensoring with a symmetric two-state spectrum multiplies the response
by \(2\cosh t\) and preserves zero total energy. -/
theorem symmetric_tensor {f : ℝ → ℝ} (hf : Realized f) :
    Realized (fun t => coordinate t*f t) := by
  obtain ⟨n,k,zk,eq⟩ := hf
  let lift : Fin n ⊕ Fin n → ℤ := Sum.elim (fun i => k i+1) (fun i => k i-1)
  refine pack (k := lift) ?_ (fun t => ?_)
  · simp only [lift,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_add_distrib,sum_sub_distrib,zk,zero_add,zero_sub,add_neg_cancel]
  · rw [← eq t]
    simp only [trace,oddTrace,lift,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Int.cast_add,
      Int.cast_sub,Int.cast_one,mul_sum,← sum_add_distrib,step]

private theorem base_realized : Realized base := by
  let k : Fin 3 → ℤ := ![2,-1,-1]
  refine ⟨3,k,?_,fun t => ?_⟩
  · rw [Fin.sum_univ_three]; change (2 : ℤ)+(-1)+(-1)=0; ring
  · rw [trace,oddTrace,Fin.sum_univ_three]
    rw [show k 0=(2 : ℤ) from rfl,show k 1=(-1 : ℤ) from rfl,show k 2=(-1 : ℤ) from rfl]
    push_cast
    simp only [oddTerm,base,coordinate,mul_two,mul_neg,mul_one,neg_neg,exp_add]
    ring

/-- Every integer polynomial in \(2\cosh t\) is a realizable factor of the
three-level odd trace. Coefficients act by direct sums and energy reflection. -/
theorem polynomial_realized (P : ℤ[X]) :
    Realized (fun t => base t * aeval (coordinate t) P) := by
  have powers (n : ℕ) : Realized (fun t => base t * coordinate t^n) := by
    induction n with
    | zero => simpa only [pow_zero,mul_one] using base_realized
    | succ n ih =>
      have h := symmetric_tensor ih
      simpa only [pow_succ,mul_left_comm,mul_comm,mul_assoc] using h
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [map_add,mul_add,Pi.add_def] using realized_add hP hQ
  | monomial n c =>
    have mem : (fun t => base t * coordinate t^n) ∈ responses := powers n
    have h : Realized (c • (fun t => base t * coordinate t^n)) := responses.zsmul_mem mem c
    have eq : c • (fun t : ℝ => base t * coordinate t^n) =
        (fun t : ℝ => base t * aeval (coordinate t) (monomial n c)) := by
      funext t
      simp only [Pi.smul_apply,zsmul_eq_mul,aeval_monomial,show algebraMap ℤ ℝ c=(c : ℝ) from rfl]
      ring
    rwa [eq] at h

#print axioms symmetric_tensor
#print axioms polynomial_realized

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice
