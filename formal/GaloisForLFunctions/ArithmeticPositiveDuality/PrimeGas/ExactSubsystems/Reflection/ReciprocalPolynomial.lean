import GaloisForLFunctions.HTGeometry.ParaorthogonalBlaschkeRoot

/-! # Reflection of a disk-free finite occupation polynomial -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Polynomial

/-- The generating polynomial for a finite set of distinct energy grades. -/
def gradePolynomial (S : Finset ℕ) : ℂ[X] := ∑ k ∈ S, X^k

private theorem grade_coeff (S : Finset ℕ) (n : ℕ) :
    (gradePolynomial S).coeff n = if n ∈ S then 1 else 0 := by
  simp only [gradePolynomial,finsetSum_coeff,coeff_X_pow,Finset.sum_ite_eq]

private theorem grade_degree (S : Finset ℕ) (hs : S.Nonempty) :
    (gradePolynomial S).natDegree = S.max' hs := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    exact (grade_coeff S n).trans (if_neg (fun h => hn.not_ge (S.le_max' n h)))
  · rw [grade_coeff,if_pos (S.max'_mem hs)]
    exact one_ne_zero

private theorem roots_eval {P : ℂ[X]} (hm : P.Monic) (x : ℂ) :
    P.eval x = (P.roots.map (fun u => x-u)).prod := by
  conv_lhs => rw [(IsAlgClosed.splits P).eq_prod_roots_of_monic hm]
  simp only [eval_multiset_prod,Multiset.map_map,Function.comp_def,eval_sub,eval_X,eval_C]

private theorem norm_root_product (R : Multiset ℂ) :
    ‖(R.map (fun u => -u)).prod‖ = (R.map norm).prod := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons u R ih => simp only [Multiset.map_cons,Multiset.prod_cons,norm_mul,norm_neg,ih]

/-- The unit constant term exhausts the product of the root moduli as soon as every root is outside the open disk. -/
private theorem roots_unit {P : ℂ[X]} (hm : P.Monic) (h₀ : P.eval 0 = 1)
    (hf : ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0) {u : ℂ} (hu : u ∈ P.roots) : ‖u‖ = 1 := by
  have hl (z : ℂ) (hz : z ∈ P.roots) : 1 ≤ ‖z‖ :=
    le_of_not_gt (fun h => hf z h (isRoot_of_mem_roots hz))
  have hp := congrArg norm (roots_eval hm 0)
  simp only [h₀,norm_one,zero_sub,norm_root_product] at hp
  obtain ⟨R,hR⟩ := Multiset.exists_cons_of_mem hu
  have ht : 1 ≤ (R.map norm).prod := Multiset.one_le_prod (fun r hr => by
    obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hr
    exact hl z (hR ▸ Multiset.mem_cons_of_mem hz))
  rw [hR,Multiset.map_cons,Multiset.prod_cons] at hp
  exact le_antisymm (calc
    ‖u‖ = ‖u‖*1 := (mul_one _).symm
    _ ≤ ‖u‖*(R.map norm).prod := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = 1 := hp.symm) (hl u hu)

/-- Conjugate reversal fixes the occupation polynomial, including all root multiplicities. -/
theorem gradePolynomial_reciprocal (S : Finset ℕ) (h₀ : 0 ∈ S)
    (hf : ∀ z : ℂ, ‖z‖ < 1 → (gradePolynomial S).eval z ≠ 0) :
    (gradePolynomial S).reverse = gradePolynomial S := by
  let P := gradePolynomial S
  have hD := grade_degree S ⟨0,h₀⟩
  have hm : P.Monic := by
    change (gradePolynomial S).coeff (gradePolynomial S).natDegree = 1
    rw [hD,grade_coeff,if_pos (S.max'_mem _)]
  have hv : P.eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero]
    exact (grade_coeff S 0).trans (if_pos h₀)
  have hreal : P.map (starRingEnd ℂ) = P := by
    simp only [P,gradePolynomial,Polynomial.map_sum,Polynomial.map_pow,Polynomial.map_X]
  let c := (P.roots.map (fun u => -star u)).prod
  have hratio (x : ℂ) : P.reverse.eval x = c*P.eval x := by
    have he := HTGeometry.conjugateReverse_eval_eq_root_product P x
    rw [hreal,hm,star_one,one_mul] at he
    rw [he,roots_eval hm x]
    unfold c
    rw [← Multiset.prod_map_mul]
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro u hu
    have hu1 := roots_unit hm hv hf hu
    have hprod : star u * u = 1 := by
      change (starRingEnd ℂ) u * u = 1
      rw [Complex.conj_mul',hu1]
      simp
    calc
      1-star u*x = star u*u-star u*x := by rw [hprod]
      _ = -star u*(x-u) := by ring
  have hc := hratio 0
  rw [hv,mul_one,← coeff_zero_eq_eval_zero,coeff_zero_reverse,hm] at hc
  exact Polynomial.funext (fun x => (hratio x).trans (by rw [← hc,one_mul]))

/-- Each occupied grade has an occupied partner summing to the highest grade. -/
theorem grade_reflected_mem (S : Finset ℕ) (h₀ : 0 ∈ S)
    (hf : ∀ z : ℂ, ‖z‖ < 1 → (gradePolynomial S).eval z ≠ 0) {k : ℕ} (hk : k ∈ S) :
    S.max' ⟨0,h₀⟩ - k ∈ S := by
  have he := congrArg (fun P : ℂ[X] => P.coeff k) (gradePolynomial_reciprocal S h₀ hf)
  change (gradePolynomial S).reverse.coeff k = (gradePolynomial S).coeff k at he
  rw [coeff_reverse,grade_degree S ⟨0,h₀⟩,revAt_le (S.le_max' k hk),grade_coeff,grade_coeff,if_pos hk] at he
  by_contra hn
  exact zero_ne_one ((if_neg hn).symm.trans he)

#print axioms gradePolynomial_reciprocal
#print axioms grade_reflected_mem

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
