import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeFibres

/-!
# Endpoint control for blocks of isolated late primes

Each unprocessed prime above half the cutoff contributes a nonpositive scalar
to the empty-cofactor head and changes no other surviving fibre. The head
decreases throughout a block. Energy decreases while the head is nonnegative
and increases after it becomes negative. Every intermediate processed subset
therefore has energy at most the maximum of the two block endpoints.
-/

noncomputable section
open Finset
namespace RHTower

/-- The entire late-prime block has an exact additive head update. -/
theorem mobiusDivisorSelectionHead_union_late_primes (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L, p.Prime ∧ p<M ∧ M ≤ 2*p) (hfree : ∀ p ∈ L, p ∉ P) :
    mobiusDivisorSelectionFibre M (P ∪ L) ∅ = mobiusDivisorSelectionFibre M P ∅+
      ∑ p ∈ L,mobiusDivisorDilationChannel M p := by
  revert hL hfree
  induction L using Finset.induction_on with
  | empty => intro hL hfree; simp
  | @insert p L hpL ih =>
    intro hL hfree
    obtain ⟨hp,hpM,hM⟩ := hL p (mem_insert_self p L)
    have hL' : ∀ q ∈ L,q.Prime ∧ q<M ∧ M ≤ 2*q := fun q hq => hL q (mem_insert_of_mem hq)
    have hfree' : ∀ q ∈ L,q ∉ P := fun q hq => hfree q (mem_insert_of_mem hq)
    have hpP : p ∉ P ∪ L := by simp [hfree p (mem_insert_self p L),hpL]
    rw [union_insert,mobiusDivisorSelectionHead_insert_late_prime hp hpM hM _ hpP,
      ih hL' hfree',sum_insert hpL]
    ring

/-- Every unprocessed late-prime block decreases the head. -/
theorem mobiusDivisorSelectionHead_union_late_primes_le (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L, p.Prime ∧ p<M ∧ M ≤ 2*p) (hfree : ∀ p ∈ L, p ∉ P) :
    mobiusDivisorSelectionFibre M (P ∪ L) ∅ ≤ mobiusDivisorSelectionFibre M P ∅ := by
  rw [mobiusDivisorSelectionHead_union_late_primes M P L hL hfree]
  have hn : (∑ p ∈ L,mobiusDivisorDilationChannel M p) ≤ 0 :=
    sum_nonpos (fun p hp => mobiusDivisorDilationChannel_late_prime_nonpos (hL p hp).1 M)
  linarith

/-- Exact block energy, retaining the head overlap and removed singleton squares. -/
theorem mobiusDivisorSelectionEnergy_union_late_primes (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L, p.Prime ∧ p<M ∧ M ≤ 2*p) (hfree : ∀ p ∈ L, p ∉ P) :
    mobiusDivisorSelectionEnergy M (P ∪ L) = mobiusDivisorSelectionEnergy M P+
      2*mobiusDivisorSelectionFibre M P ∅*(∑ p ∈ L,mobiusDivisorDilationChannel M p)+
      (∑ p ∈ L,mobiusDivisorDilationChannel M p)^(2 : ℕ)-
      ∑ p ∈ L,(mobiusDivisorDilationChannel M p)^(2 : ℕ) := by
  revert hL hfree
  induction L using Finset.induction_on with
  | empty => intro hL hfree; simp
  | @insert p L hpL ih =>
    intro hL hfree
    obtain ⟨hp,hpM,hM⟩ := hL p (mem_insert_self p L)
    have hL' : ∀ q ∈ L,q.Prime ∧ q<M ∧ M ≤ 2*q := fun q hq => hL q (mem_insert_of_mem hq)
    have hfree' : ∀ q ∈ L,q ∉ P := fun q hq => hfree q (mem_insert_of_mem hq)
    have hpP : p ∉ P ∪ L := by simp [hfree p (mem_insert_self p L),hpL]
    have he := mobiusDivisorSelectionEnergy_insert_late_prime hp hpM hM (P ∪ L) hpP
    have he' : mobiusDivisorSelectionEnergy M (insert p (P ∪ L)) =
        mobiusDivisorSelectionEnergy M (P ∪ L)+
          2*mobiusDivisorSelectionFibre M (P ∪ L) ∅*mobiusDivisorDilationChannel M p := by linarith
    rw [union_insert,he',ih hL' hfree',
      mobiusDivisorSelectionHead_union_late_primes M P L hL' hfree',sum_insert hpL,sum_insert hpL]
    ring

/-- A late block whose final head remains nonnegative contracts energy. -/
theorem mobiusDivisorSelectionEnergy_union_late_primes_le_of_head_nonneg
    (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L, p.Prime ∧ p<M ∧ M ≤ 2*p) (hfree : ∀ p ∈ L, p ∉ P)
    (hh : 0 ≤ mobiusDivisorSelectionFibre M (P ∪ L) ∅) :
    mobiusDivisorSelectionEnergy M (P ∪ L) ≤ mobiusDivisorSelectionEnergy M P := by
  revert hL hfree hh
  induction L using Finset.induction_on with
  | empty => intro hL hfree hh; simp
  | @insert p L hpL ih =>
    intro hL hfree hh
    obtain ⟨hp,hpM,hM⟩ := hL p (mem_insert_self p L)
    have hL' : ∀ q ∈ L,q.Prime ∧ q<M ∧ M ≤ 2*q := fun q hq => hL q (mem_insert_of_mem hq)
    have hfree' : ∀ q ∈ L,q ∉ P := fun q hq => hfree q (mem_insert_of_mem hq)
    have hpP : p ∉ P ∪ L := by simp [hfree p (mem_insert_self p L),hpL]
    have hc := mobiusDivisorDilationChannel_late_prime_nonpos hp M
    rw [union_insert,mobiusDivisorSelectionHead_insert_late_prime hp hpM hM _ hpP] at hh
    have hh' : 0 ≤ mobiusDivisorSelectionFibre M (P ∪ L) ∅ := by linarith
    have hei := ih hL' hfree' hh'
    have he := mobiusDivisorSelectionEnergy_insert_late_prime hp hpM hM (P ∪ L) hpP
    have hprod := mul_nonpos_of_nonneg_of_nonpos hh' hc
    rw [union_insert]
    nlinarith only [hei,he,hprod]

/-- A late block starting with a nonpositive head increases energy. -/
theorem mobiusDivisorSelectionEnergy_le_union_late_primes_of_head_nonpos
    (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L, p.Prime ∧ p<M ∧ M ≤ 2*p) (hfree : ∀ p ∈ L, p ∉ P)
    (hh : mobiusDivisorSelectionFibre M P ∅ ≤ 0) :
    mobiusDivisorSelectionEnergy M P ≤ mobiusDivisorSelectionEnergy M (P ∪ L) := by
  revert hL hfree
  induction L using Finset.induction_on with
  | empty => intro hL hfree; simp
  | @insert p L hpL ih =>
    intro hL hfree
    obtain ⟨hp,hpM,hM⟩ := hL p (mem_insert_self p L)
    have hL' : ∀ q ∈ L,q.Prime ∧ q<M ∧ M ≤ 2*q := fun q hq => hL q (mem_insert_of_mem hq)
    have hfree' : ∀ q ∈ L,q ∉ P := fun q hq => hfree q (mem_insert_of_mem hq)
    have hpP : p ∉ P ∪ L := by simp [hfree p (mem_insert_self p L),hpL]
    have hc := mobiusDivisorDilationChannel_late_prime_nonpos hp M
    have hh' := (mobiusDivisorSelectionHead_union_late_primes_le M P L hL' hfree').trans hh
    have hei := ih hL' hfree'
    have he := mobiusDivisorSelectionEnergy_insert_late_prime hp hpM hM (P ∪ L) hpP
    have hprod := mul_nonneg_of_nonpos_of_nonpos hh' hc
    rw [union_insert]
    nlinarith only [hei,he,hprod]

/-- Every intermediate late-prime subset stays below the maximum endpoint energy. -/
theorem mobiusDivisorSelectionEnergy_late_block_le_max_endpoints
    (M : ℕ) (P L R : Finset ℕ)
    (hL : ∀ p ∈ L, p.Prime ∧ p<M ∧ M ≤ 2*p) (hfree : ∀ p ∈ L, p ∉ P)
    (hRL : R ⊆ L) :
    mobiusDivisorSelectionEnergy M (P ∪ R) ≤
      max (mobiusDivisorSelectionEnergy M P) (mobiusDivisorSelectionEnergy M (P ∪ L)) := by
  by_cases hh : 0 ≤ mobiusDivisorSelectionFibre M (P ∪ R) ∅
  · exact (mobiusDivisorSelectionEnergy_union_late_primes_le_of_head_nonneg M P R
      (fun p hp => hL p (hRL hp)) (fun p hp => hfree p (hRL hp)) hh).trans (le_max_left _ _)
  · have hrem : ∀ p ∈ L \ R,p.Prime ∧ p<M ∧ M ≤ 2*p := fun p hp => hL p (mem_sdiff.mp hp).1
    have hremfree : ∀ p ∈ L \ R,p ∉ P ∪ R := by
      intro p hp
      obtain ⟨hpL,hpR⟩ := mem_sdiff.mp hp
      simp [hfree p hpL,hpR]
    have he : (P ∪ R) ∪ (L \ R)=P ∪ L := by
      ext p
      simp only [mem_union,mem_sdiff]
      constructor
      · rintro ((hp|hp)|⟨hp,hn⟩)
        · exact Or.inl hp
        · exact Or.inr (hRL hp)
        · exact Or.inr hp
      · intro hp
        by_cases hpR : p ∈ R
        · exact Or.inl (Or.inr hpR)
        · rcases hp with hp|hp
          · exact Or.inl (Or.inl hp)
          · exact Or.inr ⟨hp,hpR⟩
    have hbound := mobiusDivisorSelectionEnergy_le_union_late_primes_of_head_nonpos M
      (P ∪ R) (L \ R) hrem hremfree (le_of_not_ge hh)
    rw [he] at hbound
    exact hbound.trans (le_max_right _ _)

/-- A fixed ceiling controls the whole late-prime block exactly when it controls both endpoints. -/
theorem mobiusDivisorSelectionEnergy_late_block_ceiling_iff
    (M : ℕ) (P L : Finset ℕ) (B : ℝ)
    (hL : ∀ p ∈ L, p.Prime ∧ p<M ∧ M ≤ 2*p) (hfree : ∀ p ∈ L, p ∉ P) :
    (∀ R ⊆ L,mobiusDivisorSelectionEnergy M (P ∪ R) ≤ B) ↔
      mobiusDivisorSelectionEnergy M P ≤ B ∧ mobiusDivisorSelectionEnergy M (P ∪ L) ≤ B := by
  constructor
  · intro h
    exact ⟨by simpa using h ∅ (empty_subset L),h L (Subset.refl L)⟩
  · rintro ⟨hstart,hfinish⟩ R hRL
    exact (mobiusDivisorSelectionEnergy_late_block_le_max_endpoints M P L R hL hfree hRL).trans
      (max_le hstart hfinish)

end RHTower
