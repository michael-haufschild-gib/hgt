import GaloisForLFunctions.HTGeometry.StaticShortcutSelectorPartitionLaw
import Mathlib.Algebra.Order.Chebyshev

/-!
# Static shortcut recurrence-or-channel-production law

A channel-resolved shortcut history has only two ways to carry large total shortcut mass: reuse
occupied observer channels strongly enough to create same-channel recurrence energy, or occupy many
channels. This module proves the exact universal product law, its capacity contrapositive, a sharp
fresh-channel example, and the stationary two-memory capstone for one static unitary flow.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {J C F : Type*} [Fintype J] [Fintype C] [DecidableEq C]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Observer channels receiving nonzero total history weight. -/
def selectorOccupiedChannels (chosen : J → C) (w : J → ℝ) : Finset C :=
  Finset.univ.filter fun c => selectorChannelWeight chosen w c ≠ 0

/-- Channel loads partition total sample weight exactly. -/
theorem sum_selectorChannelWeight_eq_sum
    (chosen : J → C) (w : J → ℝ) :
    (∑ c, selectorChannelWeight chosen w c) = ∑ j, w j := by
  classical
  simp only [selectorChannelWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [selectorMaskedWeight]

/-- Selector recurrence energy is nonnegative. -/
theorem selectorRecurrenceEnergy_nonneg
    (r : J → F) (chosen : J → C) (w : J → ℝ) :
    0 ≤ selectorRecurrenceEnergy r chosen w := by
  apply Finset.sum_nonneg
  intro c hc
  rw [weightedRecurrenceEnergy_eq_norm_sq]
  positivity

/-- Total history mass is controlled by occupied-channel count times channel-load energy. -/
theorem selectorTotalWeight_sq_le_occupied_mul_load
    (chosen : J → C) (w : J → ℝ) :
    (∑ j, w j) ^ 2 ≤
      (selectorOccupiedChannels chosen w).card * selectorLoadEnergy chosen w := by
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := selectorOccupiedChannels chosen w)
    (f := fun c => selectorChannelWeight chosen w c)
  have hleft :
      (∑ c ∈ selectorOccupiedChannels chosen w,
          selectorChannelWeight chosen w c) = ∑ j, w j := by
    rw [selectorOccupiedChannels, Finset.sum_filter_ne_zero]
    exact sum_selectorChannelWeight_eq_sum chosen w
  have hright :
      (∑ c ∈ selectorOccupiedChannels chosen w,
          selectorChannelWeight chosen w c ^ 2) = selectorLoadEnergy chosen w := by
    simp only [selectorOccupiedChannels, selectorLoadEnergy]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hzero : selectorChannelWeight chosen w c = 0
    · simp [hzero]
    · simp [hzero]
  rw [hleft, hright] at hcs
  exact hcs

/-- **Recurrence-or-channel-production law.** Shortcut mass must be paid either through
same-channel recurrence energy or through the number of occupied observer channels. -/
theorem selectorRecurrence_or_channelProduction
    (r : J → F) (q : C → F) (chosen : J → C) (w : J → ℝ)
    {eta B : ℝ}
    (heta : 0 ≤ eta)
    (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, eta ≤ inner ℝ (r j) (q (chosen j)))
    (hq : ∀ c, ‖q c‖ ^ 2 ≤ B) :
    eta ^ 2 * (∑ j, w j) ^ 2 ≤
      B * (selectorOccupiedChannels chosen w).card *
        selectorRecurrenceEnergy r chosen w := by
  have hmass := selectorTotalWeight_sq_le_occupied_mul_load chosen w
  have hrec := selectorThreshold_sq_load_le_recurrenceEnergy
    r q chosen w heta hw halign hq
  calc
    eta ^ 2 * (∑ j, w j) ^ 2 ≤
        eta ^ 2 * ((selectorOccupiedChannels chosen w).card *
          selectorLoadEnergy chosen w) :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg eta)
    _ = (selectorOccupiedChannels chosen w).card *
        (eta ^ 2 * selectorLoadEnergy chosen w) := by ring
    _ ≤ (selectorOccupiedChannels chosen w).card *
        (B * selectorRecurrenceEnergy r chosen w) := by
      exact mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = B * (selectorOccupiedChannels chosen w).card *
        selectorRecurrenceEnergy r chosen w := by ring

/-- A claimed capacity `K` bounds total shortcut mass only if its recurrence budget is large
enough. -/
theorem selectorMass_sq_le_capacity_mul_recurrence
    (r : J → F) (q : C → F) (chosen : J → C) (w : J → ℝ)
    {eta B : ℝ} {K : ℕ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, eta ≤ inner ℝ (r j) (q (chosen j)))
    (hq : ∀ c, ‖q c‖ ^ 2 ≤ B)
    (hcapacity : (selectorOccupiedChannels chosen w).card ≤ K) :
    eta ^ 2 * (∑ j, w j) ^ 2 ≤
      B * K * selectorRecurrenceEnergy r chosen w := by
  have hmain := selectorRecurrence_or_channelProduction
    r q chosen w heta hw halign hq
  calc
    eta ^ 2 * (∑ j, w j) ^ 2 ≤
        B * (selectorOccupiedChannels chosen w).card *
          selectorRecurrenceEnergy r chosen w := hmain
    _ ≤ B * K * selectorRecurrenceEnergy r chosen w := by
      have hR := selectorRecurrenceEnergy_nonneg r chosen w
      gcongr

/-- If a capacity `K` cannot pay the recurrence bill, more than `K` observer channels must have
been occupied. -/
theorem selectorOccupiedChannels_gt_of_recurrenceBudget_lt
    (r : J → F) (q : C → F) (chosen : J → C) (w : J → ℝ)
    {eta B : ℝ} {K : ℕ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, eta ≤ inner ℝ (r j) (q (chosen j)))
    (hq : ∀ c, ‖q c‖ ^ 2 ≤ B)
    (hgap : B * K * selectorRecurrenceEnergy r chosen w <
      eta ^ 2 * (∑ j, w j) ^ 2) :
    K < (selectorOccupiedChannels chosen w).card := by
  by_contra hnot
  have hcapacity : (selectorOccupiedChannels chosen w).card ≤ K :=
    Nat.le_of_not_gt hnot
  have hbound := selectorMass_sq_le_capacity_mul_recurrence
    r q chosen w heta hB hw halign hq hcapacity
  linarith

/-- Fresh unit-weight identity channels saturate the mass/load occupancy inequality exactly. -/
theorem selectorIdentity_unitWeight_occupancy_saturation :
    ((∑ _j : C, (1 : ℝ)) ^ 2) =
      (selectorOccupiedChannels (fun j : C => j) (fun _ => 1)).card *
        selectorLoadEnergy (fun j : C => j) (fun _ => 1) := by
  simp [selectorOccupiedChannels, selectorChannelWeight, selectorMaskedWeight,
    selectorLoadEnergy]
  ring

variable [CompleteSpace F]

/-- **Static two-memory recurrence-or-channel-production capstone.** Every adaptive shortcut
history above its completed target-specific baseline forces either a large occupied target image or
large same-target stationary recurrence energy. -/
theorem adaptive_shortcuts_force_recurrence_or_channelProduction
    (PiOp P : F →L[ℝ] F) (U : UnitaryFlow ℝ F) (x : F)
    (target : C → F) (chosen : J → C) (time : J → ℝ) (w : J → ℝ)
    {eta B : ℝ}
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ t z, P (U.op t z) = P z)
    (hUP : ∀ t z, U.op t (P z) = P z)
    (hPiy : ∀ c, PiOp (target c) = PiOp x)
    (heta : 0 ≤ eta)
    (hw : ∀ j, 0 ≤ w j)
    (hq : ∀ c, ‖preparationMemory PiOp x (target c)‖ ^ 2 ≤ B)
    (hcollision : ∀ j,
      inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x)
            (preparationMemory PiOp x (target (chosen j))) + eta ≤
        inner ℝ (U.op (time j) x) (target (chosen j))) :
    eta ^ 2 * (∑ j, w j) ^ 2 ≤
      B * (selectorOccupiedChannels chosen w).card *
        (∑ i, ∑ j,
          if chosen i = chosen j then
            w i * w j * inner ℝ (x - P x)
              (U.op (time j - time i) (x - P x))
          else 0) := by
  have halign : ∀ j,
      eta ≤ inner ℝ (dynamicMemory P (U.op (time j)) x)
        (preparationMemory PiOp x (target (chosen j))) := by
    intro j
    have h := twoMemory_dynamicAlignment_ge_of_collision_ge
      PiOp P (U.op (time j)) x (target (chosen j))
      hPisa hPiid hPiP (hPU (time j)) (hPiy (chosen j))
      (threshold :=
        inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x)
            (preparationMemory PiOp x (target (chosen j))) + eta)
      (hcollision j)
    linarith
  have hmain := selectorRecurrence_or_channelProduction
    (r := fun j => dynamicMemory P (U.op (time j)) x)
    (q := fun c => preparationMemory PiOp x (target c))
    chosen w heta hw halign hq
  have hdynamic :
      (fun j => dynamicMemory P (U.op (time j)) x) =
        fun j => U.op (time j) (x - P x) := by
    funext j
    simp only [dynamicMemory, map_sub, hUP]
  rw [hdynamic, selectorRecurrenceEnergy_flow_eq_kernel] at hmain
  exact hmain

end

end GaloisForLFunctions.HTGeometry
