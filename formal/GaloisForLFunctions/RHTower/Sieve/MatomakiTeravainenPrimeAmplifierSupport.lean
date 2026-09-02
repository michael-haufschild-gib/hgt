import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierEnergy
import Mathlib.Data.Sym.Card

/-!
# Unordered support of the Matomäki--Teräväinen prime amplifier

Unique factorization makes a nonzero coefficient of the powered prime amplifier depend on an
unordered multiset of prime indices, not an ordered prime tuple.  This file turns that fact into
the exact stars-and-bars support bound needed by sparse mean-value alternatives to Lemma 3.5.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Nonzero indices of the literal prime block. -/
def mtTypeIPrimeCoeffSupport (P : ℕ) : Finset (Fin (2 * P)) :=
  Finset.univ.filter fun j => mtTypeIPrimeCoeff P j ≠ 0

/-- Nonzero indices of the complete powered prime block. -/
def mtTypeIPrimeRaisedSupport (P ell : ℕ) : Finset (Fin ((2 * P) ^ ell)) :=
  Finset.univ.filter fun j => convPow (2 * P) ell (mtTypeIPrimeCoeff P) j ≠ 0

@[simp] theorem mem_mtTypeIPrimeCoeffSupport {P : ℕ} {j : Fin (2 * P)} :
    j ∈ mtTypeIPrimeCoeffSupport P ↔ mtTypeIPrimeCoeff P j ≠ 0 := by
  simp [mtTypeIPrimeCoeffSupport]

@[simp] theorem mem_mtTypeIPrimeRaisedSupport
    {P ell : ℕ} {j : Fin ((2 * P) ^ ell)} :
    j ∈ mtTypeIPrimeRaisedSupport P ell ↔
      convPow (2 * P) ell (mtTypeIPrimeCoeff P) j ≠ 0 := by
  simp [mtTypeIPrimeRaisedSupport]

/-- Every nonzero powered coefficient has a contributing ordered tuple all of whose coordinates
belong to the original prime support. -/
theorem exists_mtTypeIPrimeSupportTuple
    {P ell : ℕ} {j : Fin ((2 * P) ^ ell)}
    (hj : convPow (2 * P) ell (mtTypeIPrimeCoeff P) j ≠ 0) :
    ∃ p : Fin ell → Fin (2 * P), powIdx p = j ∧
      ∀ i : Fin ell, p i ∈ mtTypeIPrimeCoeffSupport P := by
  rw [convPow] at hj
  obtain ⟨p, hp, hpne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  rw [Finset.mem_filter] at hp
  refine ⟨p, hp.2, ?_⟩
  have hcoord : ∀ i : Fin ell, mtTypeIPrimeCoeff P (p i) ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp hpne) i (Finset.mem_univ i)
  exact fun i => mem_mtTypeIPrimeCoeffSupport.mpr (hcoord i)

/-- Chosen ordered representative of one nonzero powered coefficient. -/
noncomputable def mtTypeIPrimeRaisedSupportTuple
    (P ell : ℕ) (j : ↑(mtTypeIPrimeRaisedSupport P ell)) :
    Fin ell → Fin (2 * P) :=
  Classical.choose (exists_mtTypeIPrimeSupportTuple
    (mem_mtTypeIPrimeRaisedSupport.mp j.property))

theorem powIdx_mtTypeIPrimeRaisedSupportTuple
    (P ell : ℕ) (j : ↑(mtTypeIPrimeRaisedSupport P ell)) :
    powIdx (mtTypeIPrimeRaisedSupportTuple P ell j) = j :=
  (Classical.choose_spec (exists_mtTypeIPrimeSupportTuple
    (mem_mtTypeIPrimeRaisedSupport.mp j.property))).1

theorem mtTypeIPrimeRaisedSupportTuple_mem
    (P ell : ℕ) (j : ↑(mtTypeIPrimeRaisedSupport P ell)) (i : Fin ell) :
    mtTypeIPrimeRaisedSupportTuple P ell j i ∈ mtTypeIPrimeCoeffSupport P :=
  (Classical.choose_spec (exists_mtTypeIPrimeSupportTuple
    (mem_mtTypeIPrimeRaisedSupport.mp j.property))).2 i

/-- Unordered prime multiset attached to one nonzero powered coefficient. -/
noncomputable def mtTypeIPrimeRaisedSupportSym
    (P ell : ℕ) (j : ↑(mtTypeIPrimeRaisedSupport P ell)) :
    Sym (↑(mtTypeIPrimeCoeffSupport P)) ell :=
  Sym.ofVector ⟨List.ofFn fun i =>
    ⟨mtTypeIPrimeRaisedSupportTuple P ell j i,
      mtTypeIPrimeRaisedSupportTuple_mem P ell j i⟩,
    List.length_ofFn⟩

private theorem mtTypeIPrimeRaisedSupportSym_prod
    (P ell : ℕ) (j : ↑(mtTypeIPrimeRaisedSupport P ell)) :
    ((mtTypeIPrimeRaisedSupportSym P ell j).toMultiset.map
        (fun q => ((q.1 : ℕ) + 1))).prod =
      ∏ i : Fin ell, ((mtTypeIPrimeRaisedSupportTuple P ell j i : ℕ) + 1) := by
  simp [mtTypeIPrimeRaisedSupportSym, Sym.ofVector, List.prod_ofFn]

/-- Different powered coefficients have different unordered prime multisets. -/
theorem mtTypeIPrimeRaisedSupportSym_injective (P ell : ℕ) :
    Function.Injective (mtTypeIPrimeRaisedSupportSym P ell) := by
  intro j k hjk
  apply Subtype.ext
  apply Fin.ext
  have hprod := congrArg
    (fun s : Sym (↑(mtTypeIPrimeCoeffSupport P)) ell =>
      (s.toMultiset.map fun q => ((q.1 : ℕ) + 1)).prod) hjk
  rw [mtTypeIPrimeRaisedSupportSym_prod P ell j,
    mtTypeIPrimeRaisedSupportSym_prod P ell k] at hprod
  rw [← powIdx_val_add_one (mtTypeIPrimeRaisedSupportTuple P ell j),
    ← powIdx_val_add_one (mtTypeIPrimeRaisedSupportTuple P ell k)] at hprod
  rw [powIdx_mtTypeIPrimeRaisedSupportTuple P ell j,
    powIdx_mtTypeIPrimeRaisedSupportTuple P ell k] at hprod
  exact Nat.add_right_cancel hprod

/-- Exact stars-and-bars bound for the distinct support of the powered prime amplifier. -/
theorem card_mtTypeIPrimeRaisedSupport_le_choose (P ell : ℕ) :
    (mtTypeIPrimeRaisedSupport P ell).card ≤
      ((mtTypeIPrimeCoeffSupport P).card + ell - 1).choose ell := by
  calc
    (mtTypeIPrimeRaisedSupport P ell).card =
        Fintype.card ↑(mtTypeIPrimeRaisedSupport P ell) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Sym (↑(mtTypeIPrimeCoeffSupport P)) ell) :=
      Fintype.card_le_of_injective
        (mtTypeIPrimeRaisedSupportSym P ell)
        (mtTypeIPrimeRaisedSupportSym_injective P ell)
    _ = ((mtTypeIPrimeCoeffSupport P).card + ell - 1).choose ell := by
      rw [Sym.card_sym_eq_choose ell, Fintype.card_coe]

/-- The underlying prime support contains at most `P` indices. -/
theorem card_mtTypeIPrimeCoeffSupport_le (P : ℕ) :
    (mtTypeIPrimeCoeffSupport P).card ≤ P := by
  let f : Fin (2 * P) → ℕ := fun j => (j : ℕ) - P
  have hmaps : ∀ j ∈ mtTypeIPrimeCoeffSupport P, f j ∈ Finset.range P := by
    intro j hj
    have hsupport := mtTypeIPrimeCoeff_support j
      (mem_mtTypeIPrimeCoeffSupport.mp hj)
    rw [Finset.mem_range]
    dsimp only [f]
    omega
  have hinj : Set.InjOn f (mtTypeIPrimeCoeffSupport P) := by
    intro i hi j hj hij
    have hi' := mtTypeIPrimeCoeff_support i
      (mem_mtTypeIPrimeCoeffSupport.mp hi)
    have hj' := mtTypeIPrimeCoeff_support j
      (mem_mtTypeIPrimeCoeffSupport.mp hj)
    apply Fin.ext
    dsimp only [f] at hij
    omega
  exact (Finset.card_le_card_of_injOn f hmaps hinj).trans_eq (Finset.card_range P)

/-- Source-scale support bound with the unraised prime count replaced by its interval length. -/
theorem card_mtTypeIPrimeRaisedSupport_le_choose_length (P ell : ℕ) :
    (mtTypeIPrimeRaisedSupport P ell).card ≤ (P + ell - 1).choose ell := by
  exact (card_mtTypeIPrimeRaisedSupport_le_choose P ell).trans
    (Nat.choose_le_choose ell
      (Nat.sub_le_sub_right
        (Nat.add_le_add_right (card_mtTypeIPrimeCoeffSupport_le P) ell) 1))

end

end RHTower.Sieve
