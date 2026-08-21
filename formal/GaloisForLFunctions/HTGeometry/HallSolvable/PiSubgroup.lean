import GaloisForLFunctions.HTGeometry.HallSolvable.Conjugacy
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Associated

/-!
# Hall `π`-subgroups

This file restates P. Hall's existence and conjugacy theorems in the classical language of a set
`π` of primes.

* `IsPiNat π n` — every prime factor of `n` lies in `π`.
* `IsHallPiSubgroup π H` — `Nat.card H` is a `π`-number and `H.index` is a `π'`-number.
* `exists_isHallPiSubgroup` — **(E_π)** a finite solvable group has a Hall `π`-subgroup for every `π`.
* `conj_of_isHallPiSubgroup` — **(C_π)** any two Hall `π`-subgroups of a finite solvable group are
  conjugate.
-/

namespace GaloisForLFunctions.HTGeometry.HallSolvable

open Subgroup

/-- `n` is a `π`-number: every prime dividing `n` lies in `π`. -/
def IsPiNat (π : Set ℕ) (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ∈ π

/-- A `π`-number and a `π'`-number are coprime. -/
theorem coprime_of_isPiNat {π : Set ℕ} {a b : ℕ} (ha : IsPiNat π a)
    (hb : ∀ p : ℕ, p.Prime → p ∣ b → p ∉ π) : Nat.Coprime a b := by
  by_contra h
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
  exact hb p hp (hpd.trans (Nat.gcd_dvd_right a b)) (ha p hp (hpd.trans (Nat.gcd_dvd_left a b)))

/-- Every positive natural number splits as a `π`-number times a `π'`-number. -/
theorem exists_pi_factorization (π : Set ℕ) {n : ℕ} (hn : n ≠ 0) :
    ∃ m k : ℕ, n = m * k ∧ Nat.Coprime m k ∧ IsPiNat π m ∧
      (∀ p : ℕ, p.Prime → p ∣ k → p ∉ π) := by
  classical
  set A : Finset ℕ := n.primeFactors.filter (fun p => p ∈ π) with hA
  set B : Finset ℕ := n.primeFactors.filter (fun p => p ∉ π) with hB
  refine ⟨∏ p ∈ A, p ^ n.factorization p, ∏ p ∈ B, p ^ n.factorization p, ?_, ?_, ?_, ?_⟩
  · rw [hA, hB, Finset.prod_filter_mul_prod_filter_not]
    exact Nat.prod_primeFactors_pow_factorization hn
  · refine Nat.Coprime.prod_left fun i hi => Nat.Coprime.prod_right fun j hj => ?_
    have hi' : i.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hi).1).1
    have hj' : j.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hj).1).1
    refine Nat.Coprime.pow _ _ ((Nat.coprime_primes hi' hj').mpr ?_)
    rintro rfl
    exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2
  · intro p hp hpd
    obtain ⟨q, hq, hpq⟩ := Prime.exists_mem_finset_dvd hp.prime hpd
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp
      (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1).mp (hp.dvd_of_dvd_pow hpq)
    exact this ▸ (Finset.mem_filter.mp hq).2
  · intro p hp hpd
    obtain ⟨q, hq, hpq⟩ := Prime.exists_mem_finset_dvd hp.prime hpd
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp
      (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1).mp (hp.dvd_of_dvd_pow hpq)
    exact this ▸ (Finset.mem_filter.mp hq).2

/-- The `π`-part of a factorisation into a `π`-number times a `π'`-number is unique. -/
theorem pi_factorization_unique {π : Set ℕ} {n m k m' k' : ℕ}
    (h : n = m * k) (h' : n = m' * k')
    (hm : IsPiNat π m) (hk : ∀ p : ℕ, p.Prime → p ∣ k → p ∉ π)
    (hm' : IsPiNat π m') (hk' : ∀ p : ℕ, p.Prime → p ∣ k' → p ∉ π) :
    m = m' := by
  have hd : m ∣ m' * k' := by rw [← h', h]; exact ⟨k, rfl⟩
  have hd' : m' ∣ m * k := by rw [← h, h']; exact ⟨k', rfl⟩
  exact Nat.dvd_antisymm ((coprime_of_isPiNat hm hk').dvd_of_dvd_mul_right hd)
    ((coprime_of_isPiNat hm' hk).dvd_of_dvd_mul_right hd')

variable {G : Type*} [Group G]

/-- `H` is a Hall `π`-subgroup of `G`: its order is a `π`-number and its index a `π'`-number. -/
def IsHallPiSubgroup (π : Set ℕ) (H : Subgroup G) : Prop :=
  IsPiNat π (Nat.card ↥H) ∧ ∀ p : ℕ, p.Prime → p ∣ H.index → p ∉ π

/-- **P. Hall, existence (E_π).**  A finite solvable group has a Hall `π`-subgroup for every set of
primes `π`. -/
theorem exists_isHallPiSubgroup [Finite G] [IsSolvable G] (π : Set ℕ) :
    ∃ H : Subgroup G, IsHallPiSubgroup π H := by
  obtain ⟨m, k, hmk, hcop, hm, hk⟩ := exists_pi_factorization π (Nat.card_pos (α := G)).ne'
  obtain ⟨H, hH⟩ := exists_subgroup_card_of_coprime hmk hcop
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, zero_mul] at hmk
      exact absurd hmk (Nat.card_pos (α := G)).ne'
    · exact h
  have hidx : H.index = k := by
    have h1 : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
    rw [hH, hmk] at h1
    exact Nat.eq_of_mul_eq_mul_left hmpos h1
  exact ⟨H, by rw [hH]; exact hm, by rw [hidx]; exact hk⟩

/-- Every Hall `π`-subgroup has the same order. -/
theorem card_eq_card_of_isHallPiSubgroup [Finite G] {π : Set ℕ} {H K : Subgroup G}
    (hH : IsHallPiSubgroup π H) (hK : IsHallPiSubgroup π K) :
    Nat.card ↥H = Nat.card ↥K :=
  pi_factorization_unique (Subgroup.card_mul_index H).symm (Subgroup.card_mul_index K).symm
    hH.1 hH.2 hK.1 hK.2

/-- **P. Hall, conjugacy (C_π).**  Any two Hall `π`-subgroups of a finite solvable group are
conjugate. -/
theorem conj_of_isHallPiSubgroup [Finite G] [IsSolvable G] {π : Set ℕ} {H K : Subgroup G}
    (hH : IsHallPiSubgroup π H) (hK : IsHallPiSubgroup π K) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom :=
  conj_eq_of_card_eq_of_coprime (Subgroup.card_mul_index H).symm
    (coprime_of_isPiNat hH.1 hH.2) rfl (card_eq_card_of_isHallPiSubgroup hH hK).symm

end GaloisForLFunctions.HTGeometry.HallSolvable
