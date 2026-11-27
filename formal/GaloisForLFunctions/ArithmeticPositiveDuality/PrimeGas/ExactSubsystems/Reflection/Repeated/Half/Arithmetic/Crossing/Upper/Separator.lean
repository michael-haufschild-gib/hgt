import GaloisForLFunctions.HTGeometry.ExponentialKernelTotalPositivity
import GaloisForLFunctions.HTGeometry.PermutohedralDeletionReflection

/-! # Heat probes separating ordered intervals at prescribed cuts -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Upper

open Finset Real Set
open GaloisForLFunctions.HTGeometry (expNodeMatrix expSum det_expKernel_neg_div_delta_pos)
open GaloisForLFunctions.HTGeometry.Permutohedral (delta delta_succ)

variable {r : ℕ}

/-- At temperature zero the primitive of the exponential probe measures the energy itself. -/
def primitive (t x : ℝ) : ℝ := if t=0 then x else exp (t*x)/t

theorem primitive_deriv (t x : ℝ) : HasDerivAt (primitive t) (exp (t*x)) x := by
  change HasDerivAt (fun y => if t=0 then y else exp (t*y)/t) _ x
  by_cases h : t=0
  · subst t; simpa using hasDerivAt_id' x
  · have d := (((hasDerivAt_id x).const_mul t).exp).div_const t
    simpa only [if_neg h,id_eq,mul_one,mul_div_cancel_right₀ _ h] using d

/-- The first-row cofactors interpolate the sign of the cut polynomial. Strict total
positivity gives the sign on every complementary interval, including both unbounded ones. -/
theorem separator (a : Fin r → ℝ) (t : Fin (r+1) → ℝ) (ha : StrictMono a) (ht : StrictMono t) :
    ∃ c : Fin (r+1) → ℝ, ∀ x ∉ Set.range a, 0 < expSum c t x * ∏ i, (a i-x) := by
  let M (x : ℝ) := expNodeMatrix (Fin.cons x a) t
  let c (j : Fin (r+1)) := (-1 : ℝ)^j.val * (expNodeMatrix a (t ∘ j.succAbove)).det
  have expansion (x : ℝ) : (M x).det=expSum c t x := by
    rw [Matrix.det_succ_row_zero,expSum]
    refine sum_congr rfl fun j _ => ?_
    have minor : (M x).submatrix Fin.succ j.succAbove=expNodeMatrix a (t ∘ j.succAbove) := by
      ext k l; simp only [M,Matrix.submatrix_apply,expNodeMatrix,Matrix.of_apply,Fin.cons_succ,Function.comp_apply]
    rw [minor]
    simp only [M,c,expNodeMatrix,Matrix.of_apply,Fin.cons_zero]
    rw [mul_comm x (t j)]
    ring
  have positive : 0<delta (fun i => -a i) := by
    apply prod_pos fun i _ => prod_pos fun j hj => ?_
    exact sub_pos.mpr (neg_lt_neg (ha (mem_Ioi.mp hj)))
  refine ⟨c,fun x hx => ?_⟩
  let v : Fin (r+1) → ℝ := Fin.cons x a
  have inj : Function.Injective v := Fin.cons_injective_of_injective hx ha.injective
  have ratio := det_expKernel_neg_div_delta_pos (lam := fun i => -v i) (neg_injective.comp inj) ht
  have factor : delta (fun i => -v i)=(∏ i, (a i-x))*delta (fun i => -a i) := by
    rw [delta_succ]
    simp only [v,Fin.cons_zero,Fin.cons_succ,neg_sub_neg,Function.comp_def]
  rw [factor] at ratio
  simp only [neg_neg] at ratio
  change 0 < (M x).det / _ at ratio
  rw [expansion] at ratio
  rcases div_pos_iff.mp ratio with ⟨h,d⟩ | ⟨h,d⟩
  · exact mul_pos h ((mul_pos_iff_of_pos_right positive).mp d)
  · exact mul_pos_of_neg_of_neg h (neg_of_mul_neg_left d positive.le)

#print axioms separator

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Upper
