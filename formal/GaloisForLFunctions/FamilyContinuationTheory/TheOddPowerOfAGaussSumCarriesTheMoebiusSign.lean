import Mathlib

/-!
# The odd power of a Gauss sum carries the Möbius sign

The source of the family continuation is an identity that writes the Möbius function through
Gauss sums with a functional equation. Its algebraic part is a sign law for every order.

Let `χ` be a multiplicative character of order `n > 2` on a finite field `F`, `ψ` a primitive
additive character and `μ` a primitive `n`-th root of unity. The `n`-th power of the Gauss sum is
`χ(−1) · card F` times a product of `n − 2` Jacobi sums, and each Jacobi sum is `≡ −1` modulo
`(μ − 1)²` in `ℤ[μ]`.

* **Odd order** (`exists_gaussSum_pow_orderOf_eq_of_odd`): `g(χ)^n ≡ −card F`. The sign is `−1`
  at every prime, the value of the Möbius function: for odd `n` the `n`-th power of the `n`-th
  order Gauss sum of a squarefree modulus is Möbius times a multiplicative factor.
* **Even order** (`exists_gaussSum_pow_orderOf_eq_of_even`): `g(χ)^n ≡ χ(−1) · card F`. The
  number of Jacobi factors is even and the sign is the parity of the character, not Möbius.

Order three is the least order with the Möbius sign.
-/

open Finset

namespace GaloisForLFunctions.FamilyContinuationTheory

variable {R : Type*} [CommRing R]

/-- A product of `k` factors, each `≡ −1` modulo `π²` in a subalgebra containing `π`, is
`≡ (−1)^k` modulo `π²`. -/
theorem exists_prod_eq_neg_one_pow_add {ι : Type*} (A : Subalgebra ℤ R) {π : R} (hπ : π ∈ A)
    (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, ∃ z ∈ A, f i = -1 + z * π ^ 2) :
    ∃ z ∈ A, ∏ i ∈ s, f i = (-1) ^ s.card + z * π ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, A.zero_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨z₁, hz₁, h₁⟩ := hf a (mem_insert_self a s)
    obtain ⟨z₂, hz₂, h₂⟩ := ih fun i hi => hf i (mem_insert_of_mem hi)
    refine ⟨-z₂ + z₁ * (-1) ^ s.card + z₁ * z₂ * π ^ 2, ?_, ?_⟩
    · exact A.add_mem (A.add_mem (A.neg_mem hz₂)
        (A.mul_mem hz₁ (A.pow_mem (A.neg_mem A.one_mem) _)))
        (A.mul_mem (A.mul_mem hz₁ hz₂) (A.pow_mem hπ 2))
    · rw [prod_insert ha, card_insert_of_notMem ha, h₁, h₂]
      ring

variable {F : Type*} [Field F] [Fintype F] [IsDomain R]

/-- The Jacobi factors of the `n`-th power of a Gauss sum of order `n > 2` multiply to
`(−1)^n` modulo `(μ − 1)²`. -/
theorem exists_prod_jacobiSum_eq {χ : MulChar F R} {μ : R} (h2 : 2 < orderOf χ)
    (hμ : IsPrimitiveRoot μ (orderOf χ)) :
    ∃ z ∈ Algebra.adjoin ℤ {μ},
      ∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum χ (χ ^ i) =
        (-1) ^ (orderOf χ - 2) + z * (μ - 1) ^ 2 := by
  have hχ : χ ^ orderOf χ = 1 := pow_orderOf_eq_one χ
  have hπ : μ - 1 ∈ Algebra.adjoin ℤ {μ} :=
    Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton ℤ μ) (Subalgebra.one_mem _)
  obtain ⟨z, hz, hprod⟩ := exists_prod_eq_neg_one_pow_add (Algebra.adjoin ℤ {μ}) hπ
    (Ico 1 (orderOf χ - 1)) (fun i => jacobiSum χ (χ ^ i)) fun i _ =>
      exists_jacobiSum_eq_neg_one_add h2 hχ
        (by rw [← pow_mul, mul_comm, pow_mul, hχ, one_pow])
        (MulChar.orderOf_dvd_card_sub_one F χ) hμ
  refine ⟨z, hz, ?_⟩
  rw [hprod, Nat.card_Ico]
  congr 2

/-- **Odd order: the Möbius sign.** For a character of odd order `n > 2`, the `n`-th power of the
Gauss sum is `−card F` modulo `(μ − 1)²` in `ℤ[μ]`. -/
theorem exists_gaussSum_pow_orderOf_eq_of_odd {χ : MulChar F R} {ψ : AddChar F R} {μ : R}
    (hodd : Odd (orderOf χ)) (h2 : 2 < orderOf χ) (hψ : ψ.IsPrimitive)
    (hμ : IsPrimitiveRoot μ (orderOf χ)) :
    ∃ z ∈ Algebra.adjoin ℤ {μ},
      gaussSum χ ψ ^ orderOf χ = -(Fintype.card F : R) + z * (μ - 1) ^ 2 := by
  obtain ⟨z, hz, hprod⟩ := exists_prod_jacobiSum_eq h2 hμ
  have hoddc : Odd (orderOf χ - 2) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k - 1, by omega⟩
  refine ⟨(Fintype.card F : R) * z, Subalgebra.mul_mem _ (natCast_mem _ _) hz, ?_⟩
  rw [gaussSum_pow_eq_prod_jacobiSum (by omega) hψ,
    MulChar.val_neg_one_eq_one_of_odd_order hodd (pow_orderOf_eq_one χ), hprod, hoddc.neg_one_pow]
  ring

/-- **Even order: the parity of the character.** For a character of even order `n > 2`, the
`n`-th power of the Gauss sum is `χ(−1) · card F` modulo `(μ − 1)²` in `ℤ[μ]`. -/
theorem exists_gaussSum_pow_orderOf_eq_of_even {χ : MulChar F R} {ψ : AddChar F R} {μ : R}
    (heven : Even (orderOf χ)) (h2 : 2 < orderOf χ) (hψ : ψ.IsPrimitive)
    (hμ : IsPrimitiveRoot μ (orderOf χ)) :
    ∃ z ∈ Algebra.adjoin ℤ {μ},
      gaussSum χ ψ ^ orderOf χ = χ (-1) * (Fintype.card F : R) + z * (μ - 1) ^ 2 := by
  obtain ⟨z, hz, hprod⟩ := exists_prod_jacobiSum_eq h2 hμ
  have hevenc : Even (orderOf χ - 2) := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k - 1, by omega⟩
  -- `χ(−1) = ±1` lies in `ℤ[μ]`
  have hsign : χ (-1) ∈ Algebra.adjoin ℤ {μ} := by
    have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_mul_neg, mul_one, map_one]
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · rw [h]; exact Subalgebra.one_mem _
    · rw [h]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
  refine ⟨χ (-1) * (Fintype.card F : R) * z,
    Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hsign (natCast_mem _ _)) hz, ?_⟩
  rw [gaussSum_pow_eq_prod_jacobiSum (by omega) hψ, hprod, hevenc.neg_one_pow]
  ring

end GaloisForLFunctions.FamilyContinuationTheory
