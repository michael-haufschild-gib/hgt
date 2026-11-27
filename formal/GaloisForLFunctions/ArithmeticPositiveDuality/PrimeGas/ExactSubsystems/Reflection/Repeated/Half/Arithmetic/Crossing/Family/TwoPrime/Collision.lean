import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Exact matching of finitely many integer sums on a square occupation grid -/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime

open Finset

abbrev Cell (n : ℕ) := Fin n × Fin n

/-- Quadratically many binary choices outnumber a fixed number of integer
coordinates whose individual bit lengths grow only linearly with the grid width. -/
theorem matched {J : Type*} [Fintype J] (B : ℕ) (f : (n : ℕ) → Cell n → J → ℕ)
    (bound : ∀ n x j, f n x j ≤ B^n) :
    ∃ (n : ℕ) (A C : Finset (Cell n)), 0<n ∧ Disjoint A C ∧ (A.Nonempty ∨ C.Nonempty) ∧
      ∀ j, (∑ x ∈ A, f n x j)=∑ x ∈ C, f n x j := by
  classical
  let d := Fintype.card J
  let n := (B+2)*d+1
  let L := (B+2)*n
  have np : 0<n := Nat.zero_lt_succ _
  have big := Nat.lt_two_pow_self (n := n)
  have cells : n*n < 2^n*2^n :=
    (Nat.mul_le_mul_right n big.le).trans_lt (Nat.mul_lt_mul_of_pos_left big (pow_pos (zero_lt_two : 0<2) _))
  have cap (S : Finset (Cell n)) (j : J) : (∑ x ∈ S, f n x j) < 2^L := by
    have size : S.card ≤ n*n := by simpa only [Fintype.card_prod,Fintype.card_fin] using S.card_le_univ
    calc
      (∑ x ∈ S, f n x j) ≤ ∑ _x ∈ S, B^n := sum_le_sum (fun x _ => bound n x j)
      _ = S.card*B^n := by rw [sum_const,nsmul_eq_mul,Nat.cast_id]
      _ ≤ (n*n)*(2^B)^n := Nat.mul_le_mul size (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := B)).le _)
      _ < (2^n*2^n)*(2^B)^n := Nat.mul_lt_mul_of_pos_right cells (by positivity)
      _ = 2^L := by rw [← pow_add,← pow_mul,← pow_add]; congr 1; unfold L; ring
  let key (S : Finset (Cell n)) (j : J) : Fin (2^L) := ⟨_,cap S j⟩
  have dims : L*d<n*n := by
    have h : (B+2)*d<n := Nat.lt_succ_self _
    calc L*d = ((B+2)*d)*n := by unfold L; ring
         _ < n*n := Nat.mul_lt_mul_of_pos_right h np
  have count : Fintype.card (J → Fin (2^L)) < Fintype.card (Finset (Cell n)) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_finset,Fintype.card_prod,← pow_mul]
    exact Nat.pow_lt_pow_right (one_lt_two : 1<2) dims
  obtain ⟨S,T,different,equal⟩ := Fintype.exists_ne_map_eq_of_card_lt key count
  refine ⟨n,S \ T,T \ S,np,disjoint_left.mpr (fun x h k => (mem_sdiff.mp h).2 (mem_sdiff.mp k).1),?_,fun j => ?_⟩
  · by_contra missing
    have none := not_or.mp missing
    apply different
    ext x
    constructor
    · intro h; by_contra k
      exact none.1 ⟨x,mem_sdiff.mpr ⟨h,k⟩⟩
    · intro h; by_contra k
      exact none.2 ⟨x,mem_sdiff.mpr ⟨h,k⟩⟩
  · exact sum_sdiff_eq_sum_sdiff_iff.mpr (congrArg Fin.val (congrFun equal j))

#print axioms matched

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime
