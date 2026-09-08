import GaloisForLFunctions.RHTower.MobiusDivisorCoareaMassSplit

/-!
# Correcting coarea by preserving the exact late-prime diagonal

Remove the remaining isolated late mass from nonempty conditional energy,
and restore the actual late singleton squares instead of multiplying their
conditional energy by the head mass. The corrected action bounds raw energy
when the head dominates mixed cells only. Every late-prime block preserves
mixed conditional energy and has an exact quadratic head-action law.
No uniform bound for the corrected action or prime-selection theorem is assumed.
-/
noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- Nonempty labels other than the currently isolated active late singletons. -/
def mobiusDivisorMixedCoareaLabels (M : ℕ) (P : Finset ℕ) : Finset (Finset ℕ) :=
  ((mobiusDivisorSelectionPrimes M).powerset.erase ∅) \
    (mobiusDivisorActiveLatePrimes M \ P).image (fun p => ({p}:Finset ℕ))

/-- Conditional energy with the exact isolated late contribution removed. -/
def mobiusDivisorMixedCoarea (M : ℕ) (P : Finset ℕ) : ℝ :=
  mobiusDivisorNonemptyCoarea M P - mobiusDivisorRemainingLateMass M P

/-- Exact square reserve of the unprocessed active late-prime source atoms. -/
def mobiusDivisorRemainingLateEnergy (M : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ mobiusDivisorActiveLatePrimes M \ P, (mobiusDivisorDilationChannel M p)^2

/-- Head-weighted mixed conditional energy plus the head and late squares at their actual sizes. -/
def mobiusDivisorCorrectedCoareaAction (M : ℕ) (P : Finset ℕ) : ℝ :=
  (mobiusDivisorSelectionFibre M P ∅)^2 +
    mobiusDivisorFibreAbsoluteMass M P ∅ * mobiusDivisorMixedCoarea M P +
    mobiusDivisorRemainingLateEnergy M P

private lemma late_labels_subset (M : ℕ) (P : Finset ℕ) :
    (mobiusDivisorActiveLatePrimes M \ P).image (fun p => ({p}:Finset ℕ)) ⊆
      (mobiusDivisorSelectionPrimes M).powerset.erase ∅ := by
  intro R hR
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hR
  have h := mem_mobiusDivisorActiveLatePrimes (mem_sdiff.mp hp).1
  have hpU : p ∈ mobiusDivisorSelectionPrimes M := mem_filter.mpr ⟨mem_range.mpr h.2.1,h.1⟩
  simp [hpU]

private lemma sum_nonempty_split (M : ℕ) (P : Finset ℕ) (f : Finset ℕ → ℝ) :
    (∑ R ∈ mobiusDivisorMixedCoareaLabels M P, f R) +
      (∑ p ∈ mobiusDivisorActiveLatePrimes M \ P, f {p}) =
      ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset.erase ∅, f R := by
  have h := sum_sdiff (f:=f) (late_labels_subset M P)
  rw [sum_image (by intro a _ b _ he; simpa using he)] at h
  exact h

/-- Subtracting isolated late mass leaves exactly the mixed-label conditional energy. -/
theorem mobiusDivisorMixedCoarea_eq_sum (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorMixedCoarea M P = ∑ R ∈ mobiusDivisorMixedCoareaLabels M P,
      (mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R := by
  have h := sum_nonempty_split M P (fun R =>
    (mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R)
  have hl : (∑ p ∈ mobiusDivisorActiveLatePrimes M \ P,
      (mobiusDivisorSelectionFibre M P {p})^2 / mobiusDivisorFibreAbsoluteMass M P {p}) =
      mobiusDivisorRemainingLateMass M P :=
    sum_congr rfl (fun p hp => mobiusDivisorCoarea_activeLate_singleton
      (mem_sdiff.mp hp).1 P (mem_sdiff.mp hp).2)
  rw [hl] at h
  unfold mobiusDivisorMixedCoarea mobiusDivisorNonemptyCoarea
  linarith only [h]

/-- The corrected mixed conditional energy is nonnegative without a sign or selection hypothesis. -/
theorem mobiusDivisorMixedCoarea_nonneg (M : ℕ) (P : Finset ℕ) :
    0 ≤ mobiusDivisorMixedCoarea M P := by
  rw [mobiusDivisorMixedCoarea_eq_sum]
  exact sum_nonneg (fun R _ => div_nonneg (sq_nonneg _)
    (mobiusDivisorFibreAbsoluteMass_nonneg M P R))

/-- The correction removes exactly the common head-mass cost on isolated late cells. -/
theorem mobiusDivisorCorrectedCoareaAction_eq_correction (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorCorrectedCoareaAction M P = mobiusDivisorCoareaHeadAction M P -
      mobiusDivisorFibreAbsoluteMass M P ∅ * mobiusDivisorRemainingLateMass M P +
      mobiusDivisorRemainingLateEnergy M P := by
  unfold mobiusDivisorCorrectedCoareaAction mobiusDivisorCoareaHeadAction mobiusDivisorMixedCoarea
  ring

/-- Raw energy separates into the head square, exact late squares, and mixed-label squares. -/
theorem mobiusDivisorSelectionEnergy_eq_late_mixed (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorSelectionEnergy M P = (mobiusDivisorSelectionFibre M P ∅)^2 +
      mobiusDivisorRemainingLateEnergy M P +
      ∑ R ∈ mobiusDivisorMixedCoareaLabels M P, (mobiusDivisorSelectionFibre M P R)^2 := by
  have h := sum_nonempty_split M P (fun R => (mobiusDivisorSelectionFibre M P R)^2)
  have hl : (∑ p ∈ mobiusDivisorActiveLatePrimes M \ P,
      (mobiusDivisorSelectionFibre M P {p})^2) = mobiusDivisorRemainingLateEnergy M P := by
    apply sum_congr rfl
    intro p hp
    have hpr := mem_mobiusDivisorActiveLatePrimes (mem_sdiff.mp hp).1
    rw [mobiusDivisorSelectionFibre_late_prime hpr.1 hpr.2.1 hpr.2.2 P {p}
      (mem_sdiff.mp hp).2 (mem_singleton_self p),if_pos rfl]
  have hh := sum_erase_add (s := (mobiusDivisorSelectionPrimes M).powerset)
    (f := fun R => (mobiusDivisorSelectionFibre M P R)^2)
    (by simp : (∅:Finset ℕ) ∈ (mobiusDivisorSelectionPrimes M).powerset)
  rw [hl] at h
  change (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
    (mobiusDivisorSelectionFibre M P R)^2) = _
  linarith only [h,hh]

/-- Mixed-cell head dominance suffices for corrected coarea to bound the full raw energy. -/
theorem mobiusDivisorSelectionEnergy_le_correctedCoareaAction (M : ℕ) (P : Finset ℕ)
    (hdom : ∀ R ∈ mobiusDivisorMixedCoareaLabels M P,
      mobiusDivisorFibreAbsoluteMass M P R ≤ mobiusDivisorFibreAbsoluteMass M P ∅) :
    mobiusDivisorSelectionEnergy M P ≤ mobiusDivisorCorrectedCoareaAction M P := by
  have hpoint (R : Finset ℕ) (hR : R ∈ mobiusDivisorMixedCoareaLabels M P) :
      (mobiusDivisorSelectionFibre M P R)^2 ≤ mobiusDivisorFibreAbsoluteMass M P ∅ *
        ((mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R) := by
    by_cases hz : mobiusDivisorFibreAbsoluteMass M P R=0
    · have hf : mobiusDivisorSelectionFibre M P R=0 := by
        apply abs_eq_zero.mp
        exact le_antisymm ((abs_mobiusDivisorSelectionFibre_le_absoluteMass M P R).trans_eq hz)
          (abs_nonneg _)
      simp [hf]
    · calc
        _ = mobiusDivisorFibreAbsoluteMass M P R *
            ((mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R) := by
              field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hdom R hR)
          (div_nonneg (sq_nonneg _) (mobiusDivisorFibreAbsoluteMass_nonneg M P R))
  have hs := sum_le_sum hpoint
  rw [← mul_sum,← mobiusDivisorMixedCoarea_eq_sum] at hs
  rw [mobiusDivisorSelectionEnergy_eq_late_mixed]
  unfold mobiusDivisorCorrectedCoareaAction
  linarith only [hs]

/-- The restored late diagonal always has the corpus quadratic source ceiling. -/
theorem mobiusDivisorRemainingLateEnergy_le_quadratic (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorRemainingLateEnergy M P ≤ 722*(M:ℝ)^2 := by
  have hsub : mobiusDivisorActiveLatePrimes M \ P ⊆ Icc 1 M := by
    intro p hp
    have h := mem_mobiusDivisorActiveLatePrimes (mem_sdiff.mp hp).1
    exact mem_Icc.mpr ⟨h.1.pos,by omega⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
    (sum_mobiusDivisorDilationChannel_sq_le_quadratic M)

private lemma remaining_sum_insert (M : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p ∈ mobiusDivisorActiveLatePrimes M) (hpP : p ∉ P) (f : ℕ → ℝ) :
    (∑ q ∈ mobiusDivisorActiveLatePrimes M \ insert p P, f q) =
      (∑ q ∈ mobiusDivisorActiveLatePrimes M \ P, f q)-f p := by
  rw [sdiff_insert]
  have h := sum_erase_add (s:=mobiusDivisorActiveLatePrimes M \ P) (f:=f) (mem_sdiff.mpr ⟨hp,hpP⟩)
  linarith only [h]

/-- Consuming a fresh late prime preserves all mixed conditional energy exactly. -/
theorem mobiusDivisorMixedCoarea_insert_activeLate {M p : ℕ}
    (hp : p ∈ mobiusDivisorActiveLatePrimes M) (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorMixedCoarea M (insert p P) = mobiusDivisorMixedCoarea M P := by
  have h := mem_mobiusDivisorActiveLatePrimes hp
  unfold mobiusDivisorMixedCoarea mobiusDivisorRemainingLateMass
  rw [mobiusDivisorNonemptyCoarea_insert_late_prime h.1 h.2.1 h.2.2 P hpP,
    remaining_sum_insert M P hp hpP]
  ring

/-- A late merger changes corrected action by incoming mass times mixed coarea minus twice the head. -/
theorem mobiusDivisorCorrectedCoareaAction_insert_activeLate {M p : ℕ}
    (hp : p ∈ mobiusDivisorActiveLatePrimes M) (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorCorrectedCoareaAction M (insert p P)-mobiusDivisorCorrectedCoareaAction M P =
      |mobiusDivisorDilationChannel M p| *
        (mobiusDivisorMixedCoarea M P-2*mobiusDivisorSelectionFibre M P ∅) := by
  have h := mem_mobiusDivisorActiveLatePrimes hp
  have hc : mobiusDivisorDilationChannel M p = -|mobiusDivisorDilationChannel M p| := by
    rw [abs_of_nonpos (mobiusDivisorDilationChannel_late_prime_nonpos h.1 M)]; ring
  unfold mobiusDivisorCorrectedCoareaAction mobiusDivisorRemainingLateEnergy
  rw [mobiusDivisorMixedCoarea_insert_activeLate hp P hpP,
    mobiusDivisorFibreAbsoluteMass_insert_late_prime h.1 h.2.1 h.2.2 P ∅ hpP,
    mobiusDivisorSelectionHead_insert_late_prime h.1 h.2.1 h.2.2 P hpP,
    remaining_sum_insert M P hp hpP,if_pos rfl,hc]
  simp only [abs_neg,abs_abs]
  ring

/-- Exact corrected action transport through any fresh active late block, with its diagonal credit. -/
theorem mobiusDivisorCorrectedCoareaAction_late_block (M : ℕ) (P L : Finset ℕ)
    (hL : L ⊆ mobiusDivisorActiveLatePrimes M) (hfree : ∀ p ∈ L, p ∉ P) :
    mobiusDivisorMixedCoarea M (P ∪ L) = mobiusDivisorMixedCoarea M P ∧
    mobiusDivisorCorrectedCoareaAction M (P ∪ L)-mobiusDivisorCorrectedCoareaAction M P =
      (∑ p ∈ L, |mobiusDivisorDilationChannel M p|) *
        (mobiusDivisorMixedCoarea M P-2*mobiusDivisorSelectionFibre M P ∅) +
      (∑ p ∈ L, |mobiusDivisorDilationChannel M p|)^2 -
      ∑ p ∈ L, (mobiusDivisorDilationChannel M p)^2 := by
  induction L using Finset.induction_on with
  | empty => simp
  | @insert p L hpL ih =>
    have hp := hL (mem_insert_self p L)
    have hL' : L ⊆ mobiusDivisorActiveLatePrimes M := fun q hq => hL (mem_insert_of_mem hq)
    have hfree' : ∀ q ∈ L, q ∉ P := fun q hq => hfree q (mem_insert_of_mem hq)
    have hpPL : p ∉ P ∪ L := by simp [hfree p (mem_insert_self p L),hpL]
    have hi := ih hL' hfree'
    have hmix := mobiusDivisorMixedCoarea_insert_activeLate hp (P ∪ L) hpPL
    have ha := mobiusDivisorCorrectedCoareaAction_insert_activeLate hp (P ∪ L) hpPL
    have hh := mobiusDivisorSelectionHead_union_late_primes M P L
      (fun q hq => mem_mobiusDivisorActiveLatePrimes (hL' hq)) hfree'
    have hc : (∑ q ∈ L, mobiusDivisorDilationChannel M q) =
        -(∑ q ∈ L, |mobiusDivisorDilationChannel M q|) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro q hq
      rw [abs_of_nonpos (mobiusDivisorDilationChannel_late_prime_nonpos
        (mem_mobiusDivisorActiveLatePrimes (hL' hq)).1 M)]
      ring
    rw [hc] at hh
    rw [hi.1] at hmix ha
    rw [hh] at ha
    rw [union_insert,sum_insert hpL,sum_insert hpL]
    refine ⟨hmix,?_⟩
    nlinarith only [ha,hi.2,sq_abs (mobiusDivisorDilationChannel M p)]

end RHTower
