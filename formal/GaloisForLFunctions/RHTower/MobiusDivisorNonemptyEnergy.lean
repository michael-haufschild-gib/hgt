import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeBlocks
import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreInterpolation

/-!
# Nonempty retained energy and exact late-prime steering

Removing the head square leaves the energy of all nonempty retained labels.
Its prime update retains the nonempty mixed products and consumes the singleton
square. Late primes remove only their own singleton squares from this energy.
Their effect on another prime's complete energy change is exactly affine in
the consumed late mass, with slope given by the signed retained singleton.
-/
noncomputable section
open Finset
namespace RHTower

/-- Energy outside the empty-cofactor head, with the literal source retained. -/
def mobiusDivisorNonemptyEnergy (M : ℕ) (P : Finset ℕ) : ℝ :=
  mobiusDivisorSelectionEnergy M P-(mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ)

/-- Removing the head square is exactly summation over the nonempty source labels. -/
theorem mobiusDivisorNonemptyEnergy_eq_sum (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorNonemptyEnergy M P =
      ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset.erase ∅,
        (mobiusDivisorSelectionFibre M P R)^(2 : ℕ) := by
  have h := sum_erase_add (s := (mobiusDivisorSelectionPrimes M).powerset)
    (f := fun R => (mobiusDivisorSelectionFibre M P R)^(2 : ℕ)) (a := ∅) (by simp)
  unfold mobiusDivisorNonemptyEnergy
  change (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
    (mobiusDivisorSelectionFibre M P R)^(2 : ℕ))-(mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ)=_
  linarith only [h]

/-- Nonempty retained energy is nonnegative at every cutoff and processed state. -/
theorem mobiusDivisorNonemptyEnergy_nonneg (M : ℕ) (P : Finset ℕ) :
    0 ≤ mobiusDivisorNonemptyEnergy M P := by
  rw [mobiusDivisorNonemptyEnergy_eq_sum]
  exact sum_nonneg (fun _ _ => sq_nonneg _)

/-- The complete prime-merger energy change is twice the sum of its literal paired overlaps. -/
theorem mobiusDivisorSelectionEnergy_insert_cross {p : ℕ} (hp : p.Prime)
    (M : ℕ) (P : Finset ℕ) (hpM : p<M) (hpP : p ∉ P) :
    mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P =
      2*∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset,
        mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert p R) := by
  rw [mobiusDivisorSelectionEnergy_insert_interpolation hp M P hpM hpP,mul_sum,mul_sum]
  apply sum_congr rfl
  intro R hR
  have hpR : p ∉ R := by
    intro h
    have := mem_powerset.mp hR h
    simp at this
  rw [mobiusDivisorSelectionFibre_prime_interpolation hp M P R hpP hpR]
  ring

/-- Exact nonempty energy change: nonempty pair overlaps minus the absorbed singleton square. -/
theorem mobiusDivisorNonemptyEnergy_insert_cross {p : ℕ} (hp : p.Prime)
    (M : ℕ) (P : Finset ℕ) (hpM : p<M) (hpP : p ∉ P) :
    mobiusDivisorNonemptyEnergy M (insert p P)-mobiusDivisorNonemptyEnergy M P =
      2*(∑ R ∈ (((mobiusDivisorSelectionPrimes M).erase p).powerset.erase ∅),
        mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert p R))-
      (mobiusDivisorSelectionFibre M P {p})^(2 : ℕ) := by
  have h := mobiusDivisorSelectionEnergy_insert_cross hp M P hpM hpP
  have hs := sum_erase_add (s := ((mobiusDivisorSelectionPrimes M).erase p).powerset)
    (f := fun R => mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert p R))
    (a := ∅) (by simp)
  simp only [insert_empty_eq] at hs
  unfold mobiusDivisorNonemptyEnergy
  rw [mobiusDivisorSelectionFibre_insert]
  simp only [notMem_empty,if_false,insert_empty_eq]
  nlinarith only [h,hs]

/-- A late-prime block changes nonempty energy only by removing its isolated singleton squares. -/
theorem mobiusDivisorNonemptyEnergy_union_late_primes (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p) (hfree : ∀ p ∈ L,p ∉ P) :
    mobiusDivisorNonemptyEnergy M (P ∪ L) = mobiusDivisorNonemptyEnergy M P-
      ∑ p ∈ L,(mobiusDivisorDilationChannel M p)^(2 : ℕ) := by
  unfold mobiusDivisorNonemptyEnergy
  rw [mobiusDivisorSelectionEnergy_union_late_primes M P L hL hfree,
    mobiusDivisorSelectionHead_union_late_primes M P L hL hfree]
  ring

/-- Consuming late primes always decreases nonempty energy, regardless of the current head sign. -/
theorem mobiusDivisorNonemptyEnergy_union_late_primes_le (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p) (hfree : ∀ p ∈ L,p ∉ P) :
    mobiusDivisorNonemptyEnergy M (P ∪ L) ≤ mobiusDivisorNonemptyEnergy M P := by
  rw [mobiusDivisorNonemptyEnergy_union_late_primes M P L hL hfree]
  have h := sum_nonneg (s := L) (fun p _ => sq_nonneg (mobiusDivisorDilationChannel M p))
  linarith only [h]

/-- Late-prime consumption changes another merger's full energy gain by one exact signed affine term. -/
theorem mobiusDivisorSelectionEnergy_late_block_steering
    (M q : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p) (hfree : ∀ p ∈ L,p ∉ P) (hqL : q ∉ L) :
    mobiusDivisorSelectionEnergy M (insert q (P ∪ L))-mobiusDivisorSelectionEnergy M (P ∪ L) =
      mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P-
        2*(∑ p ∈ L,divisorUnsignedDilationChannel M p)*mobiusDivisorSelectionFibre M P {q} := by
  have hfree' : ∀ p ∈ L,p ∉ insert q P := by
    intro p hp
    simp only [mem_insert,not_or]
    exact ⟨fun he => hqL (he ▸ hp),hfree p hp⟩
  have hc : (∑ p ∈ L,mobiusDivisorDilationChannel M p) =
      -(∑ p ∈ L,divisorUnsignedDilationChannel M p) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
      ArithmeticFunction.moebius_apply_prime (hL p hp).1]
    push_cast
    ring
  rw [← insert_union,mobiusDivisorSelectionEnergy_union_late_primes M (insert q P) L hL hfree',
    mobiusDivisorSelectionEnergy_union_late_primes M P L hL hfree,
    mobiusDivisorSelectionFibre_insert]
  simp only [notMem_empty,if_false,insert_empty_eq]
  rw [hc]
  ring

/-- Late consumption improves a prospective merger with nonnegative retained singleton. -/
theorem mobiusDivisorSelectionEnergy_late_block_steering_le
    (M q : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p) (hfree : ∀ p ∈ L,p ∉ P) (hqL : q ∉ L)
    (hq : 0 ≤ mobiusDivisorSelectionFibre M P {q}) :
    mobiusDivisorSelectionEnergy M (insert q (P ∪ L))-mobiusDivisorSelectionEnergy M (P ∪ L) ≤
      mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P := by
  rw [mobiusDivisorSelectionEnergy_late_block_steering M q P L hL hfree hqL]
  have hmass := sum_nonneg (s := L) (fun p _ => divisorUnsignedDilationChannel_nonneg M p)
  have h := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hmass) hq
  linarith only [h]

/-- Late consumption worsens a prospective merger with nonpositive retained singleton. -/
theorem mobiusDivisorSelectionEnergy_late_block_steering_ge
    (M q : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p) (hfree : ∀ p ∈ L,p ∉ P) (hqL : q ∉ L)
    (hq : mobiusDivisorSelectionFibre M P {q} ≤ 0) :
    mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P ≤
      mobiusDivisorSelectionEnergy M (insert q (P ∪ L))-mobiusDivisorSelectionEnergy M (P ∪ L) := by
  rw [mobiusDivisorSelectionEnergy_late_block_steering M q P L hL hfree hqL]
  have hmass := sum_nonneg (s := L) (fun p _ => divisorUnsignedDilationChannel_nonneg M p)
  have h := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num : (0:ℝ)≤2) hmass) hq
  linarith only [h]
end RHTower
