import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Heat
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # First variation of the odd part of a finite heat trace -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing

open Finset Real
open _root_.HTGeometry (finiteGibbsPartition)

variable {I : Type*} [Fintype I]

def oddTerm (t x : ℝ) := exp (t*x)-exp (-t*x)
def oddTrace (E : I → ℝ) (t : ℝ) := ∑ i, oddTerm t (E i)

theorem oddTrace_eq (E : I → ℝ) (t : ℝ) : oddTrace E t =
    finiteGibbsPartition (-t) E - finiteGibbsPartition t E := by
  simp only [oddTrace,oddTerm,finiteGibbsPartition,neg_neg,sum_sub_distrib]

theorem odd_zero (E : I → ℝ) : oddTrace E 0=0 := by
  simp only [oddTrace,oddTerm,neg_zero,zero_mul,sub_self,sum_const_zero]

/-- The displacement at each level is its own contribution to the odd trace at order
\(a\). Its total is zero whenever that comparison is blind. -/
def move (E : I → ℝ) (a u : ℝ) (i : I) := E i+u*oddTerm a (E i)

theorem sum_move (E : I → ℝ) (a u : ℝ) : ∑ i, move E a u i=(∑ i, E i)+u*oddTrace E a := by
  simp only [move,oddTrace,sum_add_distrib,mul_sum]

omit [Fintype I] in
theorem move_zero (E : I → ℝ) (a : ℝ) : move E a 0=E := by
  funext i; simp only [move,zero_mul,add_zero]

private theorem adjacent (t a x : ℝ) :
    (exp (t*x)+exp (-t*x))*oddTerm a x = oddTerm (t+a) x-oddTerm (t-a) x := by
  simp only [oddTerm,sub_eq_add_neg,neg_add,neg_neg,add_mul,exp_add]
  ring

private theorem term_deriv (t a x : ℝ) : HasDerivAt
    (fun u : ℝ => oddTerm t (x+u*oddTerm a x)) (t*(oddTerm (t+a) x-oddTerm (t-a) x)) 0 := by
  have step : HasDerivAt (fun u : ℝ => x+u*oddTerm a x) (oddTerm a x) 0 := by
    simpa only [Pi.add_def,id_eq,one_mul,zero_add] using (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).mul_const (oddTerm a x))
  have h := ((step.const_mul t).exp).sub ((step.const_mul (-t)).exp)
  simp only [zero_mul,add_zero] at h
  apply h.congr_deriv
  rw [← adjacent]
  ring

/-- The first variation at order \(t\) is the difference of the readings at the
two adjacent orders \(t+a\) and \(t-a\), multiplied by \(t\). -/
theorem trace_deriv (E : I → ℝ) (a t : ℝ) : HasDerivAt
    (fun u => oddTrace (move E a u) t) (t*(oddTrace E (t+a)-oddTrace E (t-a))) 0 := by
  simpa only [move,oddTrace,mul_sum,sum_sub_distrib,mul_sub] using
    (HasDerivAt.fun_sum (u := univ) fun i _ => term_deriv t a (E i))

/-- A blind first comparison with a nonzero second reading admits a centered
perturbation on which the two comparisons have opposite signs. -/
theorem opens_crossing (E : I → ℝ) (hmean : ∑ i, E i=0) (one : oddTrace E 1=0)
    (two : oddTrace E 2≠0) :
    ∃ u : ℝ, (∑ i, move E 1 u i)=0 ∧ oddTrace (move E 1 u) 1*oddTrace (move E 1 u) 2<0 := by
  let f := fun u => oddTrace (move E 1 u) 1 * oddTrace (move E 1 u) 2
  have df : HasDerivAt f (oddTrace E 2*oddTrace E 2) 0 := by
    simpa only [f,Pi.mul_def,one_add_one_eq_two,sub_self,odd_zero,sub_zero,one_mul,move_zero,one,zero_mul,add_zero,mul_zero,zero_add]
      using (trace_deriv E 1 1).mul (trace_deriv E 1 2)
  have fzero : f 0=0 := by simp only [f,move_zero,one,zero_mul]
  have dips : ∃ u, f u<0 := by
    by_contra! no
    have minimum : IsLocalMin f 0 := Filter.Eventually.of_forall (fun u => fzero.le.trans (no u))
    exact (mul_self_pos.mpr two).ne' (minimum.hasDerivAt_eq_zero df)
  obtain ⟨u,hu⟩ := dips
  exact ⟨u,by rw [sum_move,hmean,one,mul_zero,add_zero],hu⟩

#print axioms trace_deriv
#print axioms opens_crossing

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing
