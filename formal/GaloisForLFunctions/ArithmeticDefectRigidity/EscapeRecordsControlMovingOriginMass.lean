import GaloisForLFunctions.ArithmeticDefectRigidity.ReceiverEnergyCrossingsHaveUnitOvershoot
import GaloisForLFunctions.ArithmeticDefectRigidity.FixedSuccessorsDisappearFromEscapingProfiles
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass
import Mathlib.Data.Finset.Max
import GaloisForLFunctions.ArithmeticDefectRigidity.CompleteWienerPairingsFollowTheCommonCofactorLimit
import GaloisForLFunctions.BezoutValuationIncidence.TruncatedPronicGramMatrixAndFiniteHorizonVonMangoldtApproximation

/-!
# Escape records control moving origin mass

Unbounded receiver energy forces arbitrarily large sublinear square-prefix
records. At records the accumulated energy is negligible relative to the
square height; first crossings realize every positive normalized origin mass.
-/

section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A square-prefix bound with exponent below one pays the actual receiver. -/
theorem admits_of_receiver_square_power_bound (ε : SubcriticalDamping)
    {a C : ℝ} (ha : a < 1) (hC : 0 ≤ C)
    (hA : ∀ n : ℕ, 1 ≤ n → pmPowerDampedCenteredDivisorPrefix ε n ^ 2 ≤ C * (n : ℝ) ^ a) :
    Admits dampedMobiusEnergy ε := by
  refine ⟨C * (1 + 1 / ((2 - a) - 1)), fun T => ?_⟩
  have hcell (n : ℕ) (hn : n ∈ Icc 1 T) :
      pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        C * (n : ℝ) ^ (-(2 - a)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hp : (n : ℝ) ^ a = (n : ℝ) ^ (-(2 - a)) * (n : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
      congr 1
      ring
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ C * (n : ℝ) ^ a := hA n (mem_Icc.mp hn).1
      _ = C * (n : ℝ) ^ (-(2 - a)) * (n : ℝ) ^ 2 := by rw [hp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by nlinarith only [hn0.le] : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1))
        (mul_nonneg hC (Real.rpow_nonneg hn0.le _))
  change (∑ n ∈ Icc 1 T, pmPowerDampedCenteredDivisorPrefix ε n ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))) ≤ _
  calc
    _ ≤ ∑ n ∈ Icc 1 T, C * (n : ℝ) ^ (-(2 - a)) := sum_le_sum hcell
    _ = C * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 - a)) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_le (by linarith : 1 < 2 - a) T) hC

/-- Escape forces square-prefix spikes beyond every sublinear power bound. -/
theorem admits_or_receiver_square_exceeds_every_sublinear_power (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ a : ℝ, a < 1 → ∀ C : ℝ, 0 ≤ C → ∃ n : ℕ, 1 ≤ n ∧
        C * (n : ℝ) ^ a < pmPowerDampedCenteredDivisorPrefix ε n ^ 2 := by
  by_cases hpaid : Admits dampedMobiusEnergy ε
  · exact Or.inl hpaid
  · refine Or.inr fun a ha C hC => ?_
    by_contra h
    push Not at h
    exact hpaid (admits_of_receiver_square_power_bound ε ha hC h)


/-- Sublinear-power spikes may be taken at actual prefix records. -/
theorem admits_or_receiver_records_exceed_every_sublinear_power (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ a : ℝ, 0 ≤ a → a < 1 → ∀ C : ℝ, 0 ≤ C → ∃ k : ℕ, 1 ≤ k ∧
        (∀ j : ℕ, j ≤ k → pmPowerDampedCenteredDivisorPrefix ε j ^ 2 ≤
          pmPowerDampedCenteredDivisorPrefix ε k ^ 2) ∧
        C * (k : ℝ) ^ a < pmPowerDampedCenteredDivisorPrefix ε k ^ 2 := by
  rcases admits_or_receiver_square_exceeds_every_sublinear_power ε with hpaid | hspikes
  · exact Or.inl hpaid
  · refine Or.inr fun a ha0 ha C hC => ?_
    obtain ⟨n, hn, hspike⟩ := hspikes a ha C hC
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (range (n + 1))
      (fun j => pmPowerDampedCenteredDivisorPrefix ε j ^ 2) ⟨0, by simp⟩
    have hkn : k ≤ n := by have := mem_range.mp hk; omega
    have hnk := hmax n (mem_range.mpr (Nat.lt_succ_self n))
    have hkpos : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
        zero_pow two_ne_zero] at hnk
      exact (not_lt_of_ge (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) a)))
        (hspike.trans_le hnk)
    refine ⟨k, hkpos, fun j hj => hmax j (mem_range.mpr (by omega)), ?_⟩
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast hkn) ha0) hC).trans_lt
        (hspike.trans_le hnk)

/-- Escape supplies record origins whose square height dominates every prescribed sublinear power. -/
theorem admits_or_exists_receiver_record_sequence (ε : SubcriticalDamping)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1) :
    Admits dampedMobiusEnergy ε ∨ ∃ k : ℕ → ℕ,
      (∀ m, 1 ≤ k m) ∧
      (∀ m j, j ≤ k m → pmPowerDampedCenteredDivisorPrefix ε j ^ 2 ≤
        pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2) ∧
      Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2) atTop atTop ∧
      Tendsto (fun m => (k m : ℝ) ^ a /
        pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2) atTop (𝓝 0) := by
  rcases admits_or_receiver_records_exceed_every_sublinear_power ε with hpaid | hrecords
  · exact Or.inl hpaid
  · choose k hk hrecord hbig using
      fun m : ℕ => hrecords a ha0 ha ((m : ℝ) + 1) (by positivity)
    refine Or.inr ⟨k, hk, hrecord, ?_, ?_⟩
    · apply tendsto_atTop_mono (fun m => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
      have hp : 1 ≤ (k m : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hk m) ha0
      have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (m : ℝ) + 1)
      nlinarith only [h, (hbig m).le]
    · have hlim : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_mono (fun (m : ℕ) => (by linarith only : (m : ℝ) ≤ (m : ℝ) + 1))
            (tendsto_natCast_atTop_atTop (R := ℝ)))
      apply squeeze_zero (fun m => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (sq_nonneg _)) (fun m => ?_) hlim
      have hp : 0 < (k m : ℝ) ^ a := Real.rpow_pos_of_pos (by exact_mod_cast hk m) a
      have hA : 0 < pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2 :=
        (mul_pos (by positivity : 0 < (m : ℝ) + 1) hp).trans (hbig m)
      apply (div_le_div_iff₀ hA (by positivity)).mpr
      simpa only [one_mul, mul_comm] using (hbig m).le

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_receiver_square_exceeds_every_sublinear_power

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_exists_receiver_record_sequence
end
end


section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- At diverging prefix records, the accumulated source energy is negligible relative to record height squared. -/
theorem receiverEnergy_div_record_square_tendsto_zero (ε : SubcriticalDamping)
    (k : ℕ → ℕ)
    (hrecord : ∀ m j, j ≤ k m → pmPowerDampedCenteredDivisorPrefix ε j ^ 2 ≤
      pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2)
    (hM : Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2) atTop atTop) :
    Tendsto (fun m => dampedMobiusEnergy ε (k m) /
      pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2) atTop (𝓝 0) := by
  let w : ℕ → ℝ := fun n => 1 / ((n : ℝ) * ((n : ℝ) + 1))
  let f : ℕ → ℕ → ℝ := fun m n => if n ∈ Icc 1 (k m) then
    pmPowerDampedCenteredDivisorPrefix ε n ^ 2 /
      pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2 * w n else 0
  have hf0 (m n : ℕ) : 0 ≤ f m n := by unfold f w; split_ifs <;> positivity
  have hlim (n : ℕ) : Tendsto (fun m => f m n) atTop (𝓝 0) := by
    have hz := ((tendsto_const_nhds
      (x := pmPowerDampedCenteredDivisorPrefix ε n ^ 2)).div_atTop hM).mul_const (w n)
    rw [zero_mul] at hz
    apply squeeze_zero (fun m => hf0 m n) (fun m => ?_) hz
    dsimp only [f]
    split_ifs
    · exact le_rfl
    · positivity
  have hmajor (m n : ℕ) : ‖f m n‖ ≤ w n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 m n)]
    dsimp only [f]
    split_ifs with hn
    · have hle := hrecord m n (mem_Icc.mp hn).2
      by_cases hpos : 0 < pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2
      · exact mul_le_of_le_one_left (by dsimp [w]; positivity)
          ((div_le_one hpos).mpr hle)
      · have hz : pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2 = 0 :=
          le_antisymm (le_of_not_gt hpos) (sq_nonneg _)
        rw [hz, div_zero, zero_mul]
        dsimp [w]
        positivity
    · dsimp [w]
      positivity
  have hsum : Tendsto (fun m => ∑' n, f m n) atTop (𝓝 (∑' _n : ℕ, (0 : ℝ))) :=
    tendsto_tsum_of_dominated_convergence hasSum_pm_reciprocal_weight.summable hlim
      (Eventually.of_forall hmajor)
  rw [tsum_zero] at hsum
  convert hsum using 1
  funext m
  rw [tsum_eq_sum (s := Icc 1 (k m)) (fun n hn => by simp only [f, if_neg hn])]
  change (∑ n ∈ Icc 1 (k m), pmPowerDampedCenteredDivisorPrefix ε n ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) /
      pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2 = _
  rw [sum_div]
  apply sum_congr rfl
  intro n hn
  simp only [f, if_pos hn, w]
  ring

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.receiverEnergy_div_record_square_tendsto_zero
end
end


section
noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- On escape, first energy crossings realize every positive origin-trace ratio. -/
theorem admits_or_exists_record_horizons (ε : SubcriticalDamping)
    {a c : ℝ} (ha0 : 0 ≤ a) (ha : a < 1) (hc : 0 < c) :
    Admits dampedMobiusEnergy ε ∨ ∃ k T : ℕ → ℕ,
      (∀ m, 1 ≤ k m) ∧
      (∀ m j, j ≤ k m → pmPowerDampedCenteredDivisorPrefix ε j ^ 2 ≤
        pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2) ∧
      Tendsto T atTop atTop ∧
      (∀ᶠ m in atTop, k m < T m) ∧
      Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2 /
        dampedMobiusEnergy ε (T m + 1)) atTop (𝓝 c) ∧
      Tendsto (fun m => (k m : ℝ) ^ a /
        dampedMobiusEnergy ε (T m + 1)) atTop (𝓝 0) := by
  rcases admits_or_exists_receiver_record_sequence ε ha0 ha with hpaid | ⟨k, hk, hrecord, hM, hsmall⟩
  · exact Or.inl hpaid
  rcases admits_or_every_positive_level_has_unit_overshoot ε with hpaid | hcross
  · exact Or.inl hpaid
  let M : ℕ → ℝ := fun m => pmPowerDampedCenteredDivisorPrefix ε (k m) ^ 2
  choose T hTlow hThigh using fun m : ℕ =>
    hcross (M m / c + 1) (by dsimp [M]; positivity)
  have hM0 (m : ℕ) : 0 ≤ M m := sq_nonneg _
  have hElow (m : ℕ) : M m / c + 1 ≤ dampedMobiusEnergy ε (T m + 1) :=
    (hTlow m).trans (dampedMobiusEnergy_mono ε (Nat.le_succ _))
  have hEhigh (m : ℕ) : dampedMobiusEnergy ε (T m + 1) < M m / c + 3 := by
    have hinc := receiverEnergy_succ_le ε (T m)
    linarith only [hinc, hThigh m]
  have hEpos (m : ℕ) : 0 < dampedMobiusEnergy ε (T m + 1) := by
    have hnonneg := div_nonneg (hM0 m) hc.le
    linarith only [hElow m, hnonneg]
  have hET : Tendsto (fun m => dampedMobiusEnergy ε (T m)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hM.eventually_ge_atTop (c * b)] with m hm
    have hdiv : b ≤ M m / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hm)
    exact hdiv.trans ((le_add_of_nonneg_right zero_le_one).trans (hTlow m))
  have hE : Tendsto (fun m => dampedMobiusEnergy ε (T m + 1)) atTop atTop :=
    tendsto_atTop_mono (fun m => dampedMobiusEnergy_mono ε (Nat.le_succ _)) hET
  have hT : Tendsto T atTop atTop := by
    refine tendsto_atTop.2 fun N => ?_
    filter_upwards [hET.eventually_gt_atTop (dampedMobiusEnergy ε N)] with m hm
    by_contra hn
    exact hm.not_ge (dampedMobiusEnergy_mono ε (le_of_lt (lt_of_not_ge hn)))
  have hratio : Tendsto (fun m => M m / dampedMobiusEnergy ε (T m + 1)) atTop (𝓝 c) := by
    have hzero : Tendsto (fun m => c - M m / dampedMobiusEnergy ε (T m + 1))
        atTop (𝓝 0) := by
      apply squeeze_zero (fun m => ?_) (fun m => ?_)
        (tendsto_const_nhds.div_atTop hE :
          Tendsto (fun m => (3 * c) / dampedMobiusEnergy ε (T m + 1)) atTop (𝓝 0))
      · have hbound : M m ≤ c * dampedMobiusEnergy ε (T m + 1) := by
          have h := (div_le_iff₀ hc).mp ((le_add_of_nonneg_right zero_le_one).trans (hElow m))
          simpa only [mul_comm] using h
        exact sub_nonneg.mpr ((div_le_iff₀ (hEpos m)).mpr hbound)
      · apply (le_div_iff₀ (hEpos m)).mpr
        have hid : (c - M m / dampedMobiusEnergy ε (T m + 1)) *
            dampedMobiusEnergy ε (T m + 1) =
              c * dampedMobiusEnergy ε (T m + 1) - M m := by
          field_simp [(hEpos m).ne']
        rw [hid]
        have h := mul_lt_mul_of_pos_left (hEhigh m) hc
        have hid' : c * (M m / c + 3) = M m + 3 * c := by
          field_simp [hc.ne']
        rw [hid'] at h
        linarith only [h]
    have h := (tendsto_const_nhds (x := c)).sub hzero
    simpa only [sub_zero, sub_sub_cancel] using h
  have hnegligible := receiverEnergy_div_record_square_tendsto_zero ε k hrecord hM
  have hkT : ∀ᶠ m in atTop, k m < T m := by
    filter_upwards [hM.eventually_gt_atTop 0,
      hnegligible.eventually (gt_mem_nhds (one_div_pos.mpr hc))] with m hm hsmall
    have hrec : dampedMobiusEnergy ε (k m) < M m / c := by
      have h := (div_lt_iff₀ hm).mp hsmall
      simpa only [one_div_mul_eq_div] using h
    have hless : dampedMobiusEnergy ε (k m) < dampedMobiusEnergy ε (T m) :=
      hrec.trans_le ((le_add_of_nonneg_right zero_le_one).trans (hTlow m))
    by_contra h
    exact hless.not_ge (dampedMobiusEnergy_mono ε (le_of_not_gt h))
  refine Or.inr ⟨k, T, hk, hrecord, hT, hkT, hratio, ?_⟩
  have hmul := hsmall.mul hratio
  rw [zero_mul] at hmul
  apply hmul.congr'
  filter_upwards [hM.eventually_gt_atTop 0] with m hm
  change (_ / M m) * (M m / _) = _
  rw [← mul_div_assoc, div_mul_cancel₀ _ hm.ne']

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_exists_record_horizons
end
end
