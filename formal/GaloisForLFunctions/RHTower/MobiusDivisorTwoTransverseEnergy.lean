import GaloisForLFunctions.RHTower.MobiusDivisorInheritedTwoCost

/-!
# Transverse energy and exact reserve commutation

Removing the empty and prime-two receiving squares isolates the complete
complementary energy. A block of mutually child-inactive two-coordinate
source primes subtracts its copied-square reserve independently of the
receiving displacement. Every further prime core avoiding two and that
block has exactly the same transverse energy increment before and after
reserve consumption. Its signed cost retains every complementary pair.
-/

noncomputable section
open Finset
namespace RHTower

/-- Complete retained energy outside the empty and prime-two receiving coordinates. -/
def mobiusDivisorTwoTransverseEnergy (M : ℕ) (P : Finset ℕ) : ℝ :=
  mobiusDivisorSelectionEnergy M P-(mobiusDivisorSelectionFibre M P ∅)^2-
    (mobiusDivisorSelectionFibre M P {2})^2

/-- The transverse energy is exactly the sum over the complementary actual labels. -/
theorem mobiusDivisorTwoTransverseEnergy_eq_sum (M : ℕ) (P : Finset ℕ) (hM : 2 < M) :
    mobiusDivisorTwoTransverseEnergy M P =
      ∑ R ∈ ((mobiusDivisorSelectionPrimes M).powerset.erase ∅).erase {2},
        (mobiusDivisorSelectionFibre M P R)^2 := by
  have hmem : ({2}:Finset ℕ) ∈ (mobiusDivisorSelectionPrimes M).powerset.erase ∅ := by
    apply mem_erase.mpr
    refine ⟨by simp,mem_powerset.mpr ?_⟩
    exact singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_range.mpr hM,Nat.prime_two⟩)
  have hh := sum_erase_add (s := (mobiusDivisorSelectionPrimes M).powerset.erase ∅)
    (f := fun R => (mobiusDivisorSelectionFibre M P R)^2) hmem
  have h0 := mobiusDivisorNonemptyEnergy_eq_sum M P
  unfold mobiusDivisorTwoTransverseEnergy mobiusDivisorNonemptyEnergy at *
  linarith only [hh,h0]

/-- Every transverse contribution is nonnegative. -/
theorem mobiusDivisorTwoTransverseEnergy_nonneg (M : ℕ) (P : Finset ℕ) (hM : 2 < M) :
    0 ≤ mobiusDivisorTwoTransverseEnergy M P := by
  rw [mobiusDivisorTwoTransverseEnergy_eq_sum M P hM]
  exact sum_nonneg (fun _ _ => sq_nonneg _)

/-- Two-coordinate helpers remove exactly their copied-square reserve from transverse
energy, with no balance or receiving-head assumption. -/
theorem mobiusDivisorTwoTransverseEnergy_union_two_child_inactive
    (M : ℕ) (P L : Finset ℕ) (hM : 2 < M)
    (hL : ∀ p ∈ L,p.Prime ∧ p < M ∧ p ∉ P ∧ p ≠ 2)
    (hcore : ∀ p ∈ L,mobiusDivisorSelectionPrimes (M/p+1)\{2} ⊆ P)
    (hchild : ∀ p ∈ L,∀ q ∈ L,p ≠ q → M/p+1 ≤ q) :
    mobiusDivisorTwoTransverseEnergy M (P ∪ L) = mobiusDivisorTwoTransverseEnergy M P-
      ∑ p ∈ L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^2+
        (mobiusDivisorInterpolatedFibre M p P {2})^2) := by
  have he := mobiusDivisorSelectionEnergy_union_two_child_inactive M P L hM hL hcore hchild
  have h0 := mobiusDivisorSelectionFibre_union_two_child_inactive M P L ∅
    (fun p hp => ⟨(hL p hp).1,(hL p hp).2.2.1,by simp⟩) hchild
  have h2 := mobiusDivisorSelectionFibre_union_two_child_inactive M P L {2}
    (fun p hp => ⟨(hL p hp).1,(hL p hp).2.2.1,by simpa using (hL p hp).2.2.2⟩) hchild
  unfold mobiusDivisorTwoTransverseEnergy
  rw [he,h0,h2]
  ring

private lemma packet_insert_inactive (M p q : ℕ) (P R : Finset ℕ)
    (hq : M/p+1 ≤ q) :
    mobiusDivisorInterpolatedFibre M p (insert q P) R = mobiusDivisorInterpolatedFibre M p P R := by
  rw [show insert q P = P ∪ {q} by simp]
  unfold mobiusDivisorInterpolatedFibre
  rw [mobiusDivisorSelectionFibre_union_inactive (M/p) P {q} R
    (by intro r hr; have he : r=q := mem_singleton.mp hr; omega),
    mobiusDivisorSelectionFibre_union_inactive (M/p+1) P {q} R
    (by intro r hr; have he : r=q := mem_singleton.mp hr; omega)]

/-- Every other available prime has exactly the same transverse merger cost before
and after a two-coordinate helper block, even with unbounded quotient. -/
theorem mobiusDivisorTwoTransverseEnergy_insert_gain_union
    (M : ℕ) (P L : Finset ℕ) (hM : 2 < M)
    (hL : ∀ p ∈ L,p.Prime ∧ p < M ∧ p ∉ P ∧ p ≠ 2)
    (hcore : ∀ p ∈ L,mobiusDivisorSelectionPrimes (M/p+1)\{2} ⊆ P)
    (hchild : ∀ p ∈ L,∀ q ∈ L,p ≠ q → M/p+1 ≤ q)
    {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) (hqL : q ∉ L) (hq2 : q ≠ 2) :
    mobiusDivisorTwoTransverseEnergy M (insert q (P ∪ L))-mobiusDivisorTwoTransverseEnergy M (P ∪ L) =
      mobiusDivisorTwoTransverseEnergy M (insert q P)-mobiusDivisorTwoTransverseEnergy M P := by
  have hqcut : ∀ p ∈ L,M/p+1 ≤ q := by
    intro p hp
    by_contra hn
    apply hqP
    apply hcore p hp
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),hq⟩,by simpa using hq2⟩
  have hL' : ∀ p ∈ L,p.Prime ∧ p < M ∧ p ∉ insert q P ∧ p ≠ 2 := by
    intro p hp
    obtain ⟨hpr,hpM,hpP,hp2⟩ := hL p hp
    refine ⟨hpr,hpM,?_,hp2⟩
    simp only [mem_insert,not_or]
    exact ⟨fun he => hqL (he ▸ hp),hpP⟩
  have h0 := mobiusDivisorTwoTransverseEnergy_union_two_child_inactive M P L hM hL hcore hchild
  have h1 := mobiusDivisorTwoTransverseEnergy_union_two_child_inactive M (insert q P) L hM hL'
    (fun p hp => (hcore p hp).trans (subset_insert q P)) hchild
  have hs : (∑ p ∈ L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p (insert q P) ∅)^2+
      (mobiusDivisorInterpolatedFibre M p (insert q P) {2})^2)) =
      ∑ p ∈ L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^2+
      (mobiusDivisorInterpolatedFibre M p P {2})^2) := by
    apply sum_congr rfl
    intro p hp
    rw [packet_insert_inactive M p q P ∅ (hqcut p hp),packet_insert_inactive M p q P {2} (hqcut p hp)]
  rw [hs,insert_union] at h1
  rw [h1,h0]
  ring

/-- The entire transverse energy landscape of additional prime cores is translated
by one helper reserve; the additional primes may have arbitrary quotient depths. -/
theorem mobiusDivisorTwoTransverseEnergy_union_gain_union
    (M : ℕ) (P L A : Finset ℕ) (hM : 2 < M)
    (hL : ∀ p ∈ L,p.Prime ∧ p < M ∧ p ∉ P ∧ p ≠ 2)
    (hcore : ∀ p ∈ L,mobiusDivisorSelectionPrimes (M/p+1)\{2} ⊆ P)
    (hchild : ∀ p ∈ L,∀ q ∈ L,p ≠ q → M/p+1 ≤ q)
    (hA : ∀ q ∈ A,q.Prime ∧ q ≠ 2 ∧ q ∉ L) :
    mobiusDivisorTwoTransverseEnergy M ((P ∪ L) ∪ A)-mobiusDivisorTwoTransverseEnergy M (P ∪ L) =
      mobiusDivisorTwoTransverseEnergy M (P ∪ A)-mobiusDivisorTwoTransverseEnergy M P := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert q A hqA ih =>
    have hA' : ∀ r ∈ A,r.Prime ∧ r ≠ 2 ∧ r ∉ L := fun r hr => hA r (mem_insert_of_mem hr)
    have hprev := ih hA'
    obtain ⟨hq,hq2,hqL⟩ := hA q (mem_insert_self q A)
    rw [union_insert,union_insert]
    by_cases hqP : q ∈ P ∪ A
    · have hqPL : q ∈ (P ∪ L) ∪ A := by
        rcases mem_union.mp hqP with hp|ha
        · exact mem_union_left _ (mem_union_left _ hp)
        · exact mem_union_right _ ha
      rw [insert_eq_of_mem hqP,insert_eq_of_mem hqPL]
      exact hprev
    · have hL' : ∀ p ∈ L,p.Prime ∧ p < M ∧ p ∉ P ∪ A ∧ p ≠ 2 := by
        intro p hp
        obtain ⟨hpr,hpM,hpP,hp2⟩ := hL p hp
        refine ⟨hpr,hpM,?_,hp2⟩
        simp only [mem_union,not_or]
        exact ⟨hpP,fun ha => (hA' p ha).2.2 hp⟩
      have hh := mobiusDivisorTwoTransverseEnergy_insert_gain_union M (P ∪ A) L hM hL'
        (fun p hp => (hcore p hp).trans subset_union_left) hchild hq hqP hqL hq2
      have he : (P ∪ A) ∪ L = (P ∪ L) ∪ A := by
        ext p
        simp only [mem_union]
        tauto
      rw [he] at hh
      linarith only [hh,hprev]

/-- Advancing an arbitrary prime retains every signed transverse pair and consumes
exactly its two receiving-partner squares. -/
theorem mobiusDivisorTwoTransverseEnergy_insert_cross
    (M : ℕ) (P : Finset ℕ) (hM : 2 < M) {q : ℕ}
    (hq : q.Prime) (hqM : q < M) (hqP : q ∉ P) (hq2 : q ≠ 2) :
    mobiusDivisorTwoTransverseEnergy M (insert q P)-mobiusDivisorTwoTransverseEnergy M P =
      2*(∑ R ∈ ((((mobiusDivisorSelectionPrimes M).erase q).powerset.erase ∅).erase {2}),
        mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert q R))-
        (mobiusDivisorSelectionFibre M P {q})^2-
        (mobiusDivisorSelectionFibre M P (insert q {2}))^2 := by
  have hmem : ({2}:Finset ℕ) ∈ ((mobiusDivisorSelectionPrimes M).erase q).powerset.erase ∅ := by
    apply mem_erase.mpr
    refine ⟨by simp,mem_powerset.mpr ?_⟩
    exact singleton_subset_iff.mpr (mem_erase.mpr ⟨Ne.symm hq2,
      mem_filter.mpr ⟨mem_range.mpr hM,Nat.prime_two⟩⟩)
  have hs := sum_erase_add (s := ((mobiusDivisorSelectionPrimes M).erase q).powerset.erase ∅)
    (f := fun R => mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert q R)) hmem
  have he := mobiusDivisorNonemptyEnergy_insert_cross hq M P hqM hqP
  unfold mobiusDivisorNonemptyEnergy at he
  unfold mobiusDivisorTwoTransverseEnergy
  simp only [mobiusDivisorSelectionFibre_insert,notMem_empty,if_false,insert_empty_eq,mem_singleton,hq2] at *
  nlinarith only [he,hs]

end RHTower
