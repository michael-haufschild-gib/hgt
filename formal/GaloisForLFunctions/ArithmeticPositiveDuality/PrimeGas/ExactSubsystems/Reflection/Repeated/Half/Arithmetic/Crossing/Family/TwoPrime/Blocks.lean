import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime.Collision

/-! # Equal direct and reciprocal moments on two prime occupations -/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime

open Finset

def first {n : ℕ} (x : Cell n) := x.1.val+1
def second {n : ℕ} (x : Cell n) := x.2.val+1

def direct (p q : ℕ) {n : ℕ} (x : Cell n) := p^first x*q^second x
def reverse (p q : ℕ) {n : ℕ} (x : Cell n) := p^(n-first x)*q^(n-second x)

theorem first_le {n : ℕ} (x : Cell n) : first x ≤ n := x.1.isLt
theorem second_le {n : ℕ} (x : Cell n) : second x ≤ n := x.2.isLt

theorem complementary_product (p q : ℕ) {n : ℕ} (x : Cell n) :
    direct p q x*reverse p q x=(p*q)^n := by
  unfold direct reverse
  rw [mul_mul_mul_comm,← pow_add,← pow_add,Nat.add_sub_of_le (first_le x),Nat.add_sub_of_le (second_le x),mul_pow]

/-- Disjoint blocks preserve both occupation sums and all requested direct and
reciprocal moments. The common denominator of a reciprocal moment is fixed by the box. -/
theorem blocks (p q : Nat.Primes) (T : Finset ℕ) :
    ∃ (n : ℕ) (A B : Finset (Cell n)), Disjoint A B ∧ (A.Nonempty ∨ B.Nonempty) ∧
      (∑ x ∈ A, first x)=(∑ x ∈ B, first x) ∧ (∑ x ∈ A, second x)=(∑ x ∈ B, second x) ∧
      ∀ h ∈ T, (∑ x ∈ A, (direct p.val q.val x)^h)=(∑ x ∈ B, (direct p.val q.val x)^h) ∧
        (∑ x ∈ A, (reverse p.val q.val x)^h)=(∑ x ∈ B, (reverse p.val q.val x)^h) := by
  classical
  let H := T.sup id
  let m := p.val*q.val
  let D := max 2 (m^H)
  let J := Bool ⊕ (T ⊕ T)
  let f (n : ℕ) (x : Cell n) : J → ℕ := Sum.elim
    (fun b => if b then first x else second x)
    (Sum.elim (fun h => (direct p.val q.val x)^h.val) (fun h => (reverse p.val q.val x)^h.val))
  have small (n : ℕ) : n≤D^n := by
    exact (Nat.lt_two_pow_self (n := n)).le.trans (Nat.pow_le_pow_left (le_max_left _ _) _)
  have power {n v h : ℕ} (lo : v ≤ m^n) (mem : h ∈ T) : v^h ≤ D^n := by
    have le : h ≤ H := Finset.le_sup (f := id) mem
    have mp : 1 ≤ m := Nat.mul_pos p.property.pos q.property.pos
    calc
      v^h ≤ (m^n)^h := Nat.pow_le_pow_left lo _
      _ = (m^h)^n := by rw [← pow_mul,← pow_mul,Nat.mul_comm n h]
      _ ≤ D^n := Nat.pow_le_pow_left ((Nat.pow_le_pow_right mp le).trans (le_max_right _ _)) _
  have bound (n : ℕ) (x : Cell n) (j : J) : f n x j ≤ D^n := by
    rcases j with b | h
    · cases b
      · exact (second_le x).trans (small n)
      · exact (first_le x).trans (small n)
    · rcases h with h | h
      · apply power (h := h.val) _ h.property
        exact (Nat.mul_le_mul (Nat.pow_le_pow_right p.property.pos (first_le x))
          (Nat.pow_le_pow_right q.property.pos (second_le x))).trans_eq (mul_pow _ _ _).symm
      · apply power (h := h.val) _ h.property
        exact (Nat.mul_le_mul (Nat.pow_le_pow_right p.property.pos (Nat.sub_le n (first x)))
          (Nat.pow_le_pow_right q.property.pos (Nat.sub_le n (second x)))).trans_eq (mul_pow _ _ _).symm
  obtain ⟨n,A,B,_,disj,non,eq⟩ := matched D f bound
  exact ⟨n,A,B,disj,non,eq (.inl true),eq (.inl false),fun h hh =>
    ⟨eq (.inr (.inl ⟨h,hh⟩)),eq (.inr (.inr ⟨h,hh⟩))⟩⟩

#print axioms complementary_product
#print axioms blocks

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime
