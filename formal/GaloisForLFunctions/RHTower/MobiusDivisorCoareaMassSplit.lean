import GaloisForLFunctions.RHTower.MobiusDivisorCoareaHeadTransport
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeInterleavingCapacity
import GaloisForLFunctions.RHTower.MobiusDivisorUniformSuccessorTransport

/-!
# The unavoidable consumed/remaining late-mass cost of head coarea

Every processed late prime adds its original absolute mass to the head.
Every unprocessed late prime remains an isolated cell with conditional
energy equal to its absolute mass. Thus head action dominates the
product of consumed and remaining late mass, at every processed state.
This is an actual-source theorem, independent of prime order or RH.
-/
noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- Original late-prime absolute mass already collected by the head. -/
def mobiusDivisorConsumedLateMass (M : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ mobiusDivisorActiveLatePrimes M ∩ P, |mobiusDivisorDilationChannel M p|

/-- Original late-prime absolute mass still in isolated singleton cells. -/
def mobiusDivisorRemainingLateMass (M : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ mobiusDivisorActiveLatePrimes M \ P, |mobiusDivisorDilationChannel M p|

/-- Active prime coefficients have exactly the unsigned source mass. -/
theorem abs_mobiusDivisorDilationChannel_activeLate {M p : ℕ}
    (hp : p ∈ mobiusDivisorActiveLatePrimes M) :
    |mobiusDivisorDilationChannel M p| = divisorUnsignedDilationChannel M p := by
  have h := mem_mobiusDivisorActiveLatePrimes hp
  simp [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_apply_prime h.1,
    abs_of_nonneg (divisorUnsignedDilationChannel_nonneg M p)]

/-- The consumed and remaining pieces retain the complete arithmetic late mass. -/
theorem mobiusDivisorConsumed_add_remainingLateMass (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorConsumedLateMass M P + mobiusDivisorRemainingLateMass M P =
      mobiusDivisorLatePrimeMass M := by
  unfold mobiusDivisorConsumedLateMass mobiusDivisorRemainingLateMass
  rw [sum_inter_add_sum_sdiff]
  exact (sum_congr rfl (fun p hp => abs_mobiusDivisorDilationChannel_activeLate hp)).trans
    (sum_mobiusDivisorActiveLatePrimes M)

/-- Processed late atoms cannot cancel out of the original absolute head mass. -/
theorem mobiusDivisorConsumedLateMass_le_headMass (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorConsumedLateMass M P ≤ mobiusDivisorFibreAbsoluteMass M P ∅ := by
  let I := (mobiusDivisorSelectionIndices M).filter (fun d => d.primeFactors \ P = ∅)
  have hsub : mobiusDivisorActiveLatePrimes M ∩ P ⊆ I := by
    intro p hp
    obtain ⟨hpL,hpP⟩ := mem_inter.mp hp
    have h := mem_mobiusDivisorActiveLatePrimes hpL
    have hpi : p ∈ mobiusDivisorSelectionIndices M :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨h.1.pos,by omega⟩,h.1.squarefree⟩
    exact mem_filter.mpr ⟨hpi,by simp [h.1.primeFactors,hpP]⟩
  have he : mobiusDivisorFibreAbsoluteMass M P ∅ =
      ∑ p ∈ I, |mobiusDivisorDilationChannel M p| := by
    simp [mobiusDivisorFibreAbsoluteMass,subsetLabelFibre,I,sum_filter]
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)

/-- An unprocessed late singleton contributes its entire absolute mass to coarea. -/
theorem mobiusDivisorCoarea_activeLate_singleton {M p : ℕ}
    (hp : p ∈ mobiusDivisorActiveLatePrimes M) (P : Finset ℕ) (hpP : p ∉ P) :
    (mobiusDivisorSelectionFibre M P {p})^(2 : ℕ) / mobiusDivisorFibreAbsoluteMass M P {p} =
      |mobiusDivisorDilationChannel M p| := by
  have h := mem_mobiusDivisorActiveLatePrimes hp
  rw [mobiusDivisorSelectionFibre_late_prime h.1 h.2.1 h.2.2 P {p}
      hpP (mem_singleton_self p),
    mobiusDivisorFibreAbsoluteMass_late_prime h.1 h.2.1 h.2.2 P {p}
      hpP (mem_singleton_self p)]
  simp only [if_true]
  by_cases hz : mobiusDivisorDilationChannel M p=0
  · simp [hz]
  apply (div_eq_iff (abs_ne_zero.mpr hz)).mpr
  nlinarith only [sq_abs (mobiusDivisorDilationChannel M p)]

/-- Remaining isolated late mass survives in nonempty conditional energy at every state. -/
theorem mobiusDivisorRemainingLateMass_le_nonemptyCoarea (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorRemainingLateMass M P ≤ mobiusDivisorNonemptyCoarea M P := by
  let L := mobiusDivisorActiveLatePrimes M \ P
  let t := fun R => (mobiusDivisorSelectionFibre M P R)^(2 : ℕ) / mobiusDivisorFibreAbsoluteMass M P R
  have hsub : L.image (fun p => ({p}:Finset ℕ)) ⊆
      (mobiusDivisorSelectionPrimes M).powerset.erase ∅ := by
    intro R hR
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hR
    have h := mem_mobiusDivisorActiveLatePrimes (mem_sdiff.mp hp).1
    have hpU : p ∈ mobiusDivisorSelectionPrimes M :=
      mem_filter.mpr ⟨mem_range.mpr h.2.1,h.1⟩
    simp [hpU]
  change (∑ p ∈ L, |mobiusDivisorDilationChannel M p|) ≤
    ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset.erase ∅, t R
  calc
    _ = ∑ p ∈ L, t {p} := sum_congr rfl (fun p hp =>
      (mobiusDivisorCoarea_activeLate_singleton (mem_sdiff.mp hp).1 P (mem_sdiff.mp hp).2).symm)
    _ = ∑ R ∈ L.image (fun p => ({p}:Finset ℕ)), t R := by
      rw [sum_image (by intro a _ b _ he; simpa using he)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun R _ _ =>
      div_nonneg (sq_nonneg _) (mobiusDivisorFibreAbsoluteMass_nonneg M P R))

/-- The head coarea action contains the product of consumed and unconsumed late mass. -/
theorem mobiusDivisorCoareaHeadAction_ge_late_mass_split (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorConsumedLateMass M P * mobiusDivisorRemainingLateMass M P ≤
      mobiusDivisorCoareaHeadAction M P := by
  have ht : 0 ≤ mobiusDivisorConsumedLateMass M P := sum_nonneg (fun _ _ => abs_nonneg _)
  have hr : 0 ≤ mobiusDivisorRemainingLateMass M P := sum_nonneg (fun _ _ => abs_nonneg _)
  have h := mul_le_mul (mobiusDivisorConsumedLateMass_le_headMass M P)
    (mobiusDivisorRemainingLateMass_le_nonemptyCoarea M P) hr
    (mobiusDivisorFibreAbsoluteMass_nonneg M P ∅)
  unfold mobiusDivisorCoareaHeadAction
  nlinarith only [h,sq_nonneg (mobiusDivisorSelectionFibre M P ∅)]

/-- A one-index insertion changes consumed late mass by exactly one fresh active atom. -/
theorem mobiusDivisorConsumedLateMass_insert (M : ℕ) (P : Finset ℕ) (p : ℕ) :
    mobiusDivisorConsumedLateMass M (insert p P) = mobiusDivisorConsumedLateMass M P +
      if p ∈ mobiusDivisorActiveLatePrimes M ∧ p ∉ P then
        |mobiusDivisorDilationChannel M p| else 0 := by
  unfold mobiusDivisorConsumedLateMass
  by_cases hpL : p ∈ mobiusDivisorActiveLatePrimes M
  · by_cases hpP : p ∈ P
    · simp [hpP]
    · have he : mobiusDivisorActiveLatePrimes M ∩ insert p P =
          insert p (mobiusDivisorActiveLatePrimes M ∩ P) := by ext q; simp [hpL]
      rw [he,sum_insert (by simp [hpP])]
      simp [hpL,hpP,add_comm]
  · have he : mobiusDivisorActiveLatePrimes M ∩ insert p P =
        mobiusDivisorActiveLatePrimes M ∩ P := by ext q; simp; aesop
    simp [he,hpL]

/-- Every consumed late-mass increment obeys the actual square-root channel ceiling. -/
theorem mobiusDivisorConsumedLateMass_insert_step_le (M : ℕ) (P : Finset ℕ) (p : ℕ) :
    mobiusDivisorConsumedLateMass M (insert p P) - mobiusDivisorConsumedLateMass M P ≤
      (3/5:ℝ) * Real.sqrt M := by
  rw [mobiusDivisorConsumedLateMass_insert]
  by_cases h : p ∈ mobiusDivisorActiveLatePrimes M ∧ p ∉ P
  · rw [if_pos h,add_sub_cancel_left,abs_mobiusDivisorDilationChannel_activeLate h.1]
    exact divisorUnsignedDilationChannel_le_three_fifths_sqrt M p
  · simp only [if_neg h,add_zero,sub_self]
    positivity

end RHTower
