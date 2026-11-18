import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianAllPointGapLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricFiberCounts

/-!
# Numerical semigroup weights on the geometric Hermitian curve

In each full block the ordinary and exceptional gaps differ by reversing
the residue. Summing over the gap triangle yields the excess Q choose 3
in gap weight at every square-field point. The order Q+1 recognizes all
Q³ exceptional affine points whenever Q>2. The weight relative to
1,…,g at a nonrational point is (Q+1)Q(Q-1)(Q-2)/24.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p^(s+1)
local notation "qℤ" => ((Q:ℕ):ℤ)
local notation "E" => HermitianGeometricConstants p s
local notation "Pts" => HermitianAffinePoint p s E
local notation "F" => hermitianFrobeniusPoint p s E
local notation "S" => hermitianPointPoleSemigroup p s
local notation "g" => (Q*(Q-1)/2 : ℕ)

/-- Sum of the actual gap orders minus 1+⋯+g, using the complete gap parametrization. -/
def hermitianPointGapWeight (P : Pts) : ℤ :=
  (∑ r : Fin Q, ∑ j : Fin r.val, (((hermitianPointGapEquiv p s P).symm ⟨r,j⟩).val:ℤ)) -
    (g*(g+1)/2 : ℕ)

private theorem sum_first (n : ℕ) :
    2*(∑ r ∈ Finset.range n,(r:ℤ)) = (n:ℤ)*(n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Nat.cast_succ]
    linear_combination ih

private theorem residue_excess (n : ℕ) :
    6*(∑ r ∈ Finset.range n,(r:ℤ)*(2*r-n)) = (n:ℤ)*(n-1)*(n-2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Nat.cast_succ]
    have h (r : ℕ) : (r:ℤ)*(2*r-(n+1))=r*(2*r-n)-r := by ring
    simp_rw [h,Finset.sum_sub_distrib]
    linear_combination ih - 3*(sum_first n)

/-- Six times the excess of rational over nonrational gap weight is Q(Q-1)(Q-2). -/
theorem hermitianPointGapWeight_excess (P U : Pts) (hP : F P=P) (hU : F U ≠ U) :
    6*(hermitianPointGapWeight p s P-hermitianPointGapWeight p s U) =
      qℤ*(qℤ-1)*(qℤ-2) := by
  have h (r : Fin Q) : (∑ t : Fin r.val,
      ((((hermitianPointGapEquiv p s P).symm ⟨r,t⟩).val:ℤ) -
       (((hermitianPointGapEquiv p s U).symm ⟨r,t⟩).val:ℤ))) =
      (r.val:ℤ)*(2*r.val-qℤ) := by
    simp only [hermitianPointGapEquiv_label,if_pos hP,if_neg hU,Int.natCast_add,Int.natCast_sub r.isLt.le,
      add_sub_add_right_eq_sub]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  unfold hermitianPointGapWeight
  rw [sub_sub_sub_cancel_right,← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib,h]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i:ℤ)*(2*i-qℤ)),residue_excess]

/-- In the nonelliptic cases the two gap weights are strictly ordered. -/
theorem hermitianExceptional_gapWeight_gt (P U : Pts) (hP : F P=P) (hU : F U ≠ U)
    (hq : 2<Q) : hermitianPointGapWeight p s U < hermitianPointGapWeight p s P := by
  have hz : 2 < qℤ := by exact_mod_cast hq
  have h := hermitianPointGapWeight_excess p s P U hP hU
  have hp' : 0 < qℤ*(qℤ-1)*(qℤ-2) := mul_pos (mul_pos (by omega) (by omega)) (by omega)
  omega

/-- There are exactly Q³ affine points admitting the second pole order Q+1 when Q>2. -/
theorem hermitianExceptional_affine_count (hq : 2<Q) :
    Nat.card {P : Pts // Q+1 ∈ S P} = Q^3 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun P => hermitianAffinePoint_rational_iff_second_nongap p s P hq)]
  exact (hermitianFirstTwoFixed_card p s).1

private theorem exists_fixed_point : ∃ P : Pts, F P=P := by
  let P : Pts := ⟨(0,0),by simp [(Fact.out : p.Prime).ne_zero]⟩
  refine ⟨P,(hermitianFrobeniusPoint_eq_self_iff p s E P).2 ?_⟩
  have hQ := pow_ne_zero (s+1) (Fact.out : p.Prime).ne_zero
  exact zero_pow (Nat.mul_ne_zero hQ hQ)

private theorem gap_triangle_sum (q : ℤ) (n : ℕ) :
    6*(∑ r ∈ Finset.range n, ∑ j ∈ Finset.range r, ((r:ℤ)+q*j)) =
      (n:ℤ)*(n-1)*(2*n-1+q*(n-2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Nat.cast_succ,Finset.sum_add_distrib,← Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    linear_combination ih + 3*q*(sum_first n)

private theorem twice_lower_triangle (n : ℕ) :
    2*((n*(n-1)/2:ℕ):ℤ) = (n:ℤ)*(n-1) := by
  rw [← Finset.sum_range_id,Nat.cast_sum]
  exact sum_first n

private theorem twice_upper_triangle (n : ℕ) :
    2*((n*(n+1)/2:ℕ):ℤ) = (n:ℤ)*(n+1) := by
  have h := twice_lower_triangle (n+1)
  rw [Nat.add_sub_cancel,Nat.mul_comm (n+1) n,Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at h
  exact h.trans (mul_comm _ _)

/-- Absolute gap weight at a square-field point, measured from the sequence 1,…,g. -/
theorem hermitianPointGapWeight_fixed (P : Pts) (hP : F P=P) :
    24*hermitianPointGapWeight p s P = qℤ*(qℤ-1)*(qℤ-2)*(qℤ+5) := by
  let A : ℤ := ∑ r : Fin Q, ∑ j : Fin r.val,
    (((hermitianPointGapEquiv p s P).symm ⟨r,j⟩).val:ℤ)
  have hA : 6*A = qℤ*(qℤ-1)*(qℤ^2-1) := by
    simp only [A,hermitianPointGapEquiv_label,if_pos hP,Int.natCast_add,Int.natCast_mul]
    have hs (r : ℕ) : (∑ j : Fin r, ((r:ℤ)+qℤ*j.val)) =
        ∑ j ∈ Finset.range r, ((r:ℤ)+qℤ*j) :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => (r:ℤ)+qℤ*j) r
    simp_rw [hs]
    rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => ∑ j ∈ Finset.range r, ((r:ℤ)+qℤ*j)),gap_triangle_sum]
    ring
  let D : ℤ := ((g*(g+1)/2:ℕ):ℤ)
  have hD : 2*D=(g:ℤ)*(g+1) := twice_upper_triangle g
  change 24*(A-D) = _
  calc
    _ = 4*(6*A)-12*(2*D) := by ring
    _ = 4*(qℤ*(qℤ-1)*(qℤ^2-1))-3*((2*(g:ℤ))^2+2*(2*(g:ℤ))) := by rw [hA,hD]; ring
    _ = _ := by rw [twice_lower_triangle Q]; ring

/-- Every nonrational point has absolute gap weight (Q+1 choose 4). -/
theorem hermitianPointGapWeight_nonfixed (U : Pts) (hU : F U ≠ U) :
    24*hermitianPointGapWeight p s U = qℤ*(qℤ-1)*(qℤ-2)*(qℤ+1) := by
  obtain ⟨P,hP⟩ := exists_fixed_point p s
  linear_combination hermitianPointGapWeight_fixed p s P hP - 4*(hermitianPointGapWeight_excess p s P U hP hU)

/-- A positive absolute gap weight at every geometric point occurs precisely above the elliptic case. -/
theorem hermitianPointGapWeight_pos_iff (P : Pts) :
    0 < hermitianPointGapWeight p s P ↔ 2<Q := by
  have hQ : 1 < Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  by_cases h : 2<Q
  · have hq : (2:ℤ)<qℤ := by exact_mod_cast h
    have hprod : 0 < qℤ*(qℤ-1)*(qℤ-2) := mul_pos (mul_pos (by omega) (by omega)) (by omega)
    refine iff_of_true ?_ h
    by_cases hP : F P=P
    · have he := hermitianPointGapWeight_fixed p s P hP
      have hp' : 0 < qℤ*(qℤ-1)*(qℤ-2)*(qℤ+5) := mul_pos hprod (by omega)
      omega
    · have he := hermitianPointGapWeight_nonfixed p s P hP
      have hp' : 0 < qℤ*(qℤ-1)*(qℤ-2)*(qℤ+1) := mul_pos hprod (by omega)
      omega
  · have he : Q=2 := by omega
    refine iff_of_false ?_ h
    by_cases hP : F P=P
    · have hw := hermitianPointGapWeight_fixed p s P hP
      rw [he] at hw
      norm_num at hw
      omega
    · have hw := hermitianPointGapWeight_nonfixed p s P hP
      rw [he] at hw
      norm_num at hw
      omega

/-- The two different weights are attained in every nonelliptic characteristic and extension degree. -/
theorem hermitianExceptional_gapWeight_exists (hq : 2<Q) :
    ∃ P U : Pts, F P=P ∧ F U≠U ∧ hermitianPointGapWeight p s U < hermitianPointGapWeight p s P := by
  obtain ⟨P,hp₀⟩ := exists_fixed_point p s
  obtain ⟨U,_,hu⟩ := hermitianGeometric_exists_degree_two_mul_char p s
  have hU : F U≠U := by
    intro h
    have hd := (hermitianFrobenius_return_iff p s U 1).1 (show F^[1] U=U from h)
    rw [hu,Nat.dvd_one] at hd
    have hp := (Fact.out : p.Prime).two_le
    omega
  exact ⟨P,U,hp₀,hU,hermitianExceptional_gapWeight_gt p s P U hp₀ hU hq⟩

#print axioms hermitianPointGapWeight_excess
#print axioms hermitianPointGapWeight_fixed
#print axioms hermitianPointGapWeight_nonfixed
#print axioms hermitianPointGapWeight_pos_iff
#print axioms hermitianExceptional_gapWeight_gt
#print axioms hermitianExceptional_affine_count
#print axioms hermitianExceptional_gapWeight_exists
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
