import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Multiplicity histograms missed by a fixed finite set of area moments

For any prescribed finite set of derivative orders there are two disjoint
positive-order histograms with the same cardinality, winding and all the
prescribed area moments. Their possible orders form a geometric progression.
The construction clears the denominators of the moment exponents and uses
the positive and negative coefficients of one monic integer polynomial.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Splitting the coefficients of a monic polynomial with prescribed
integer roots gives disjoint natural weights with equal evaluations. -/
private theorem matching_polynomial_weights (S : Finset ℕ) :
    ∃ (N : ℕ) (a b : Fin N → ℕ), a≠b ∧ (∀ i, a i=0 ∨ b i=0) ∧
      ∀ x ∈ S, ∑ i, a i*x^i.val=∑ i, b i*x^i.val := by
  let P : ℤ[X] := ∏ x ∈ S, (X-C (x:ℤ))
  have hmon : P.Monic := monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C (x:ℤ))
  let N := P.natDegree+1
  let a (i : Fin N) := (P.coeff i.val).toNat
  let b (i : Fin N) := (-(P.coeff i.val)).toNat
  have hab (i : Fin N) : (a i:ℤ)-(b i:ℤ)=P.coeff i.val := by dsimp only [a,b]; omega
  refine ⟨N,a,b,?_,?_,?_⟩
  · intro he
    let top : Fin N := ⟨P.natDegree,Nat.lt_succ_self _⟩
    have h := hab top
    rw [he,sub_self] at h
    exact zero_ne_one (h.trans (hmon.coeff_natDegree))
  · intro i
    dsimp only [a,b]
    omega
  · intro x hx
    have hzero : P.eval (x:ℤ)=0 := by
      rw [show P.eval (x:ℤ)=∏ y ∈ S, ((x:ℤ)-(y:ℤ)) by
        simp only [P,eval_prod,eval_sub,eval_X,eval_C]]
      exact Finset.prod_eq_zero hx (sub_self _)
    rw [eval_eq_sum_range,←Fin.sum_univ_eq_sum_range] at hzero
    have he : ∑ i : Fin N, (a i:ℤ)*(x:ℤ)^i.val=∑ i : Fin N, (b i:ℤ)*(x:ℤ)^i.val := by
      rw [←sub_eq_zero,←Finset.sum_sub_distrib]
      simpa only [←sub_mul,hab] using hzero
    exact_mod_cast he

private theorem geometric_area_weight {D j : ℕ} (hd : j+1 ∣ D) (i : ℕ) :
    (((2^D)^i:ℕ):ℝ)^(2/((j+1:ℕ):ℝ)) = (((2^(2*(D/(j+1))))^i:ℕ):ℝ) := by
  have he : (D:ℝ)=((D/(j+1):ℕ):ℝ)*((j+1:ℕ):ℝ) := by
    exact_mod_cast (Nat.div_mul_cancel hd).symm
  have hp : ((j+1:ℕ):ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
  rw [←pow_mul,←pow_mul,Nat.cast_pow,Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤2),←Real.rpow_natCast]
  congr 1
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  rw [he]
  field_simp
  <;> ring

/-- Every fixed finite schedule admits two different histograms, even
when winding and the number of distinct sites are both observed. No
positive multiplicity occurs on both sides. -/
theorem finite_derivative_schedule_has_disjoint_histograms (J : Finset ℕ) :
    ∃ (N : ℕ) (m a b : Fin N → ℕ), StrictMono m ∧ (∀ i, 0<m i) ∧ a≠b ∧
      (∀ i, a i=0 ∨ b i=0) ∧ (∑ i, a i)=(∑ i, b i) ∧
      (∑ i, a i*m i)=(∑ i, b i*m i) ∧
      ∀ j ∈ J, (∑ i, (a i:ℝ)*(m i:ℝ)^(2/((j+1:ℕ):ℝ)))=
        ∑ i, (b i:ℝ)*(m i:ℝ)^(2/((j+1:ℕ):ℝ)) := by
  let D := ∏ j ∈ J, (j+1)
  have hD : 0<D := Finset.prod_pos fun j _ => Nat.succ_pos j
  let base : ℕ := 2^D
  have hb : 1<base := by
    simpa only [pow_zero] using (pow_lt_pow_right₀ (by decide : 1<(2:ℕ)) hD)
  let root (j : ℕ) := 2^(2*(D/(j+1)))
  let S := insert 1 (insert base (J.image root))
  obtain ⟨N,a,b,hdiff,hdis,h⟩ := matching_polynomial_weights S
  let m (i : Fin N) := base^i.val
  refine ⟨N,m,a,b,(fun i j hij => pow_lt_pow_right₀ hb (Fin.lt_def.mp hij)),
    (fun i => pow_pos (Nat.zero_lt_of_lt hb) _),hdiff,hdis,?_,?_,?_⟩
  · simpa only [one_pow,mul_one] using h 1 (Finset.mem_insert_self ..)
  · exact h base (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  · intro j hj
    have hjD : j+1 ∣ D := Finset.dvd_prod_of_mem (fun k : ℕ => k+1) hj
    have hx := h (root j) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem root hj)))
    have he (i : Fin N) : (m i:ℝ)^(2/((j+1:ℕ):ℝ))=(((root j)^i.val:ℕ):ℝ) :=
      geometric_area_weight hjD i.val
    simp only [he]
    exact_mod_cast hx

#print axioms finite_derivative_schedule_has_disjoint_histograms
end GaloisForLFunctions.ExceptionalLayerTheory
