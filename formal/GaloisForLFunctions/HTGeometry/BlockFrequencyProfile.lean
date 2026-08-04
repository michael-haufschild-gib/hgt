import GaloisForLFunctions.HTGeometry.MonomialFrequencySeparation
import GaloisForLFunctions.HTGeometry.BlockCarrierMonomial

/-!
# The frequency of a tuple determines how many of its entries lie in each block

Rational independence makes the frequency of a tuple determine the multiset of indices it uses.  The
multiset in turn determines, for every block of a partition of the index set, how many entries of the
tuple lie in that block.

This is the separation a graded several-carrier relation needs: monomials of different block profiles
sit at disjoint frequencies, so each profile is tested on its own.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι] {κ : Type*} [DecidableEq κ]

/-- How much of a multiset of indices lies in a given block. -/
def blockProfile (bidx : ι → κ) (t : ι →₀ ℕ) (k : κ) : ℕ :=
  t.sum fun y c => if bidx y = k then c else 0

omit [DecidableEq ι] in
theorem blockProfile_add (bidx : ι → κ) (t t' : ι →₀ ℕ) (k : κ) :
    blockProfile bidx (t + t') k = blockProfile bidx t k + blockProfile bidx t' k := by
  classical
  rw [blockProfile, blockProfile, blockProfile]
  refine Finsupp.sum_add_index' (fun y => ?_) fun y c c' => ?_
  · by_cases hy : bidx y = k <;> simp [hy]
  · by_cases hy : bidx y = k <;> simp [hy]

omit [DecidableEq ι] in
theorem blockProfile_single (bidx : ι → κ) (y : ι) (k : κ) :
    blockProfile bidx (Finsupp.single y 1) k = if bidx y = k then 1 else 0 := by
  classical
  rw [blockProfile, Finsupp.sum_single_index]
  by_cases hy : bidx y = k <;> simp [hy]

/-- **The block profile of a tuple counts its entries block by block.** -/
theorem blockProfile_tupleCount (bidx : ι → κ) {β : Type*} [Fintype β]
    [DecidableEq β] (n : β → ι) (k : κ) :
    blockProfile bidx (tupleCount n) k = (univ.filter fun j : β => bidx (n j) = k).card := by
  classical
  rw [tupleCount]
  induction (univ : Finset β) using Finset.induction_on with
  | empty => simp [blockProfile]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, blockProfile_add, blockProfile_single, ih,
        Finset.filter_insert]
      by_cases hjk : bidx (n j) = k
      · rw [if_pos hjk, if_pos hjk, Finset.card_insert_of_notMem (by simp [hj])]
        omega
      · rw [if_neg hjk, if_neg hjk]
        omega

/-- **The frequency of a tuple determines its block profile.**  Rational independence makes the
frequency determine the multiset of indices, and the multiset determines how many entries lie in each
block. -/
theorem blockProfile_eq_of_frequency_eq {omega : ι → ℝ} (h : RationallyIndependentSequence omega)
    (bidx : ι → κ) {β β' : Type*} [Fintype β] [DecidableEq β] [Fintype β'] [DecidableEq β']
    {n : β → ι} {n' : β' → ι} (hfreq : ∑ j, omega (n j) = ∑ j, omega (n' j)) (k : κ) :
    (univ.filter fun j : β => bidx (n j) = k).card
      = (univ.filter fun j : β' => bidx (n' j) = k).card := by
  classical
  have hcount : tupleCount n = tupleCount n' := by
    refine monomialFrequency_injective h ?_
    rw [monomialFrequency_tupleCount, monomialFrequency_tupleCount, hfreq]
  rw [← blockProfile_tupleCount bidx n k, ← blockProfile_tupleCount bidx n' k, hcount]

/-! ### The canonical slot-to-block map of a profile -/

/-- The canonical assignment of slots to blocks realizing a prescribed profile: the slots are the
disjoint union of the blocks, in order. -/
def profileBlk {n : ℕ} (d : Fin n → ℕ) : Fin (∑ k, d k) → Fin n :=
  fun l => (finSigmaFinEquiv.symm l).1

/-- **The canonical assignment realizes its profile.** -/
theorem card_profileBlk {n : ℕ} (d : Fin n → ℕ) (k : Fin n) :
    (univ.filter fun l : Fin (∑ k, d k) => profileBlk d l = k).card = d k := by
  classical
  have hcard : (univ.filter fun l : Fin (∑ k, d k) => profileBlk d l = k).card
      = (univ.filter fun p : (j : Fin n) × Fin (d j) => p.1 = k).card := by
    refine (Finset.card_bij (fun p _ => finSigmaFinEquiv p) ?_ ?_ ?_).symm
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [profileBlk, Equiv.symm_apply_apply]
      exact hp.2
    · intro p _ q _ hpq
      exact finSigmaFinEquiv.injective hpq
    · intro l hl
      rw [Finset.mem_filter] at hl
      refine ⟨finSigmaFinEquiv.symm l, ?_, by rw [Equiv.apply_symm_apply]⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hl.2⟩
  rw [hcard, Finset.card_filter, Fintype.sum_sigma]
  have hterm : ∀ j : Fin n, (∑ _b : Fin (d j), if j = k then 1 else 0) = if j = k then d j else 0 := by
    intro j
    by_cases hjk : j = k
    · simp [hjk]
    · simp [hjk]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq' univ k d,
    if_pos (Finset.mem_univ k)]

/-! ### Grades of the wrong profile carry nothing -/

omit [DecidableEq ι] in
/-- A tuple whose block profile differs from the prescribed assignment has a mismatched slot. -/
theorem exists_slot_mismatch_of_profile_ne {M : ℕ} (bidx : ι → κ) (blk : Fin M → κ)
    {n : Fin M → ι} {k : κ}
    (hk : (univ.filter fun j : Fin M => bidx (n j) = k).card
        ≠ (univ.filter fun j : Fin M => blk j = k).card) :
    ∃ j, bidx (n j) ≠ blk j := by
  classical
  by_contra hcon
  push Not at hcon
  refine hk ?_
  refine congrArg Finset.card (Finset.filter_congr fun j _ => ?_)
  rw [hcon j]

omit [DecidableEq ι] in
/-- The amplitude of a several-carrier monomial vanishes on a tuple with a mismatched slot. -/
theorem blockMonomialAmplitude_eq_zero_of_mismatch (a : ι → ℂ) (bidx : ι → κ) (omega : ι → ℝ)
    {M : ℕ} (blk : Fin M → κ) (c : ℂ) (s : Fin M → ℕ) {n : Fin M → ι}
    (hn : ∃ j, bidx (n j) ≠ blk j) :
    blockMonomialAmplitude (fun j y => if bidx y = blk j then a y else 0) omega c s n = 0 := by
  classical
  obtain ⟨j, hj⟩ := hn
  rw [blockMonomialAmplitude]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  rw [if_neg hj, zero_mul]

/-- **A grade of the wrong block profile contributes nothing at a given frequency.**  Every tuple at
that frequency has the profile of the test tuple, so a grade whose prescribed assignment has a
different profile is annihilated slot by slot. -/
theorem fiberAmplitude_blockGrade_eq_zero_of_profile_ne {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) (a : ι → ℂ) (bidx : ι → κ)
    {M M' : ℕ} (blk : Fin M' → κ) {T : Type*} (cs : T → ℂ) (ss : T → (Fin M' → ℕ))
    {i : Fin M → ι} {k : κ}
    (hk : (univ.filter fun j : Fin M' => blk j = k).card
        ≠ (univ.filter fun j : Fin M => bidx (i j) = k).card) :
    fiberAmplitude
      (fun p : Σ _ : T, Fin M' → ι =>
        blockMonomialAmplitude (fun j y => if bidx y = blk j then a y else 0) omega
          (cs p.1) (ss p.1) p.2)
      (fun p : Σ _ : T, Fin M' → ι => tupleFrequency omega p.2)
      (tupleFrequency omega i) = 0 := by
  classical
  rw [fiberAmplitude]
  have hzero : ∀ q : {p : Σ _ : T, Fin M' → ι //
      tupleFrequency omega p.2 = tupleFrequency omega i},
      blockMonomialAmplitude (fun j y => if bidx y = blk j then a y else 0) omega
        (cs (q : Σ _ : T, Fin M' → ι).1) (ss (q : Σ _ : T, Fin M' → ι).1)
        (q : Σ _ : T, Fin M' → ι).2 = 0 := by
    rintro ⟨p, hp⟩
    refine blockMonomialAmplitude_eq_zero_of_mismatch a bidx omega blk (cs p.1) (ss p.1) ?_
    refine exists_slot_mismatch_of_profile_ne bidx blk (k := k) ?_
    have hprof := blockProfile_eq_of_frequency_eq h bidx (n := p.2) (n' := i) hp k
    rw [hprof]
    exact fun hcon => hk hcon.symm
  rw [tsum_congr hzero, tsum_zero]

end

end GaloisForLFunctions.HTGeometry
