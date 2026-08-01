import GaloisForLFunctions.HTGeometry.SplitFactorizationSubsets
import Mathlib.FieldTheory.Separable

/-!
# Counting the monic divisors of a separable split polynomial

A monic polynomial that is separable and splits is the product of its distinct linear factors, so
its monic divisors of a prescribed degree are the subsets of its root set of that size, and there
are exactly a binomial coefficient of them.

Separability is the only hypothesis that does any work.  Where a fibre of a factorization map is
counted, this replaces an intersection-theoretic count by a subset count, for every separable target
and not only for a distinguished one.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- **A monic separable split polynomial is the product of its distinct linear factors.** -/
theorem eq_prod_roots_toFinset {P : K[X]} (hmonic : P.Monic) (hsep : P.Separable)
    (hsplit : P.Splits) :
    P = ∏ r ∈ P.roots.toFinset, (X - C r) := by
  have hnodup : P.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard : P.roots.card = P.natDegree := (hsplit.natDegree_eq_card_roots).symm
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  have hval : (P.roots.toFinset : Finset K).val = P.roots := by
    rw [Multiset.toFinset_val, hnodup.dedup]
  calc P = (Multiset.map (fun a => X - C a) P.roots).prod := hprod.symm
    _ = ∏ r ∈ P.roots.toFinset, (X - C r) := by rw [Finset.prod_eq_multiset_prod, hval]

/-- **A separable split polynomial has as many distinct roots as its degree.** -/
theorem card_roots_toFinset {P : K[X]} (hsep : P.Separable) (hsplit : P.Splits) :
    (P.roots.toFinset : Finset K).card = P.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
    ← hsplit.natDegree_eq_card_roots]

/-- **The monic divisors of a prescribed degree of a monic separable split polynomial are counted by
a binomial coefficient.**  They are the subsets of the root set of that size. -/
theorem nat_card_monic_divisors {P : K[X]} (hmonic : P.Monic) (hsep : P.Separable)
    (hsplit : P.Splits) (m : ℕ) :
    Nat.card {A : K[X] // A.Monic ∧ A ∣ P ∧ A.natDegree = m} = P.natDegree.choose m := by
  classical
  set R := P.roots.toFinset with hR
  have hPR : P = ∏ r ∈ R, (X - C r) := eq_prod_roots_toFinset hmonic hsep hsplit
  have hcongr : Nat.card {A : K[X] // A.Monic ∧ A ∣ P ∧ A.natDegree = m}
      = Nat.card {S : Finset K // S ⊆ R ∧ S.card = m} := by
    rw [hPR]
    exact (Nat.card_congr (monicDivisorEquivSubset R m)).symm
  have hsub : Nat.card {S : Finset K // S ⊆ R ∧ S.card = m}
      = Nat.card {S : Finset K // S ∈ R.powersetCard m} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun S => by rw [Finset.mem_powersetCard])
  have hfin : Nat.card {S : Finset K // S ∈ R.powersetCard m} = (R.powersetCard m).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcongr, hsub, hfin, Finset.card_powersetCard, hR, card_roots_toFinset hsep hsplit]

end GaloisForLFunctions.HTGeometry
