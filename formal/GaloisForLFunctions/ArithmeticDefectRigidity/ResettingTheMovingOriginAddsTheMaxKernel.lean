import GaloisForLFunctions.ArithmeticDefectRigidity.CommonCofactorLimitsExistAlongPrescribedHorizons
import GaloisForLFunctions.ArithmeticDefectRigidity.OriginStepsHaveTheMaxKernel
import GaloisForLFunctions.ArithmeticDefectRigidity.EscapeRecordsControlMovingOriginMass
import GaloisForLFunctions.ArithmeticDefectRigidity.SubcriticalCofactorsPairBoundedlyWithBoundedRows
import GaloisForLFunctions.ArithmeticDefectRigidity.VanishingRelativeEnergyPreservesMovingGrams
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationHardyInequalityOnThePronicMeasure

/-!
# Resetting the moving origin adds the max kernel

A source-power controlled reset-origin shift has receiver-scale Gram
K+c/max(j,k) when its origin square divided by receiver energy tends to c.
Its own normalization divides by 1+c, and every positive c is realized
by shifted actual rows on the escape branch.
-/

section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A translated actual source whose arithmetic origin alone is reset to zero. -/
def resetOriginReceiver (ε : SubcriticalDamping) (k n : ℕ) : ℝ :=
  if n = 0 then 0 else pmPowerDampedCenteredDivisorPrefix ε (n + k)

/-- The source and the surviving step component of a reset-origin translation. -/
def originBoundaryMain (ε : SubcriticalDamping) (k n : ℕ) : ℝ :=
  pmPowerDampedCenteredDivisorPrefix ε n +
    pmPowerDampedCenteredDivisorPrefix ε k * originStep n

theorem resetOriginReceiver_eq (ε : SubcriticalDamping) (k n : ℕ) :
    resetOriginReceiver ε k n = originBoundaryMain ε k n + receiverAdditiveDefect ε n k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [resetOriginReceiver, originBoundaryMain, originStep, receiverAdditiveDefect,
      if_true, ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      mul_zero, zero_add, sub_zero, sub_self]
  · simp only [resetOriginReceiver, originBoundaryMain, originStep, receiverAdditiveDefect,
      if_neg hn.ne', mul_one]
    ring

theorem originBoundaryMain_pairing (ε : SubcriticalDamping) (h T : ℕ) (j k : ℕ+) :
    pronicPairing T (rowDilate j (originBoundaryMain ε h))
        (rowDilate k (originBoundaryMain ε h)) =
      pronicPairing T (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε))
        (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε)) +
      pmPowerDampedCenteredDivisorPrefix ε h *
        pronicPairing T (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε)) (rowDilate k originStep) +
      pmPowerDampedCenteredDivisorPrefix ε h *
        pronicPairing T (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε)) (rowDilate j originStep) +
      pmPowerDampedCenteredDivisorPrefix ε h ^ 2 *
        pronicPairing T (rowDilate j originStep) (rowDilate k originStep) := by
  simp only [pronicPairing, rowDilate, originBoundaryMain, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- The moving origin times a bounded source-step pairing disappears at receiver scale. -/
theorem origin_scaled_source_step_pairing_tendsto_zero (ε : SubcriticalDamping)
    (T h : ℕ → ℕ) (hE : Tendsto (fun m => dampedMobiusEnergy ε (T m + 1)) atTop atTop)
    {c : ℝ}
    (hc : Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (h m) ^ 2 /
      dampedMobiusEnergy ε (T m + 1)) atTop (𝓝 c)) (j k : ℕ+) :
    Tendsto (fun m => (pmPowerDampedCenteredDivisorPrefix ε (h m) /
      dampedMobiusEnergy ε (T m + 1)) *
        pronicPairing (T m + 1) (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε))
          (rowDilate k originStep)) atTop (𝓝 0) := by
  have htrace := origin_div_energy_tendsto_zero
    (fun m => pmPowerDampedCenteredDivisorPrefix ε (h m))
    (fun m => dampedMobiusEnergy ε (T m + 1)) hE hc
  obtain ⟨C, hC, hbound⟩ := exists_uniform_bounded_row_pairing ε
  have hstep (n : ℕ) : |rowDilate k originStep n| ≤ (1 : ℝ) := by
    rw [rowDilate_originStep]
    split_ifs <;> norm_num
  have hlim := htrace.abs.mul_const C
  rw [abs_zero, zero_mul] at hlim
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  refine squeeze_zero (fun _ => abs_nonneg _) (fun m => ?_) hlim
  simp only [Function.comp_apply]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [mul_one] using hbound (rowDilate k originStep) 1 hstep j (T m + 1))
    (abs_nonneg _)

/-- The main reset-origin Gram is the actual Gram plus its step boundary mass. -/
theorem originBoundaryMain_gram_tendsto {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (h : ℕ → ℕ)
    (hE : Tendsto (fun m => dampedMobiusEnergy ε (L.subsequence m + 1)) atTop atTop)
    {c : ℝ} (hc : Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (h m) ^ 2 /
      dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 c)) (j k : ℕ+) :
    Tendsto (fun m => pronicPairing (L.subsequence m + 1)
      (rowDilate j (originBoundaryMain ε (h m)))
      (rowDilate k (originBoundaryMain ε (h m))) /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop
      (𝓝 (L.kernel j k + c / ((max (j : ℕ) (k : ℕ) : ℕ) : ℝ))) := by
  have hT : Tendsto (fun m => L.subsequence m + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp L.strictMono.tendsto_atTop
  have hcross₁ := origin_scaled_source_step_pairing_tendsto_zero ε L.subsequence h hE hc j k
  have hcross₂ := origin_scaled_source_step_pairing_tendsto_zero ε L.subsequence h hE hc k j
  have hstep := hc.mul ((pronicPairing_originSteps_tendsto j k).comp hT)
  have hlim := (((L.converges j k).add hcross₁).add hcross₂).add hstep
  simp only [add_zero, mul_one_div] at hlim
  apply hlim.congr
  intro m
  simp only [Function.comp_apply]
  rw [originBoundaryMain_pairing]
  unfold cofactorGram
  ring

/-- The existing uniform source saving applies along arbitrary escaping observation horizons. -/
theorem recentered_energy_tendsto_zero_along (ε : SubcriticalDamping) (T h : ℕ → ℕ)
    (hE : Tendsto (fun m => dampedMobiusEnergy ε (T m + 1)) atTop atTop)
    (hh : ∃ C : ℝ, ∀ᶠ m in atTop,
      (h m : ℝ) ^ (1 - (ε : ℝ)) / dampedMobiusEnergy ε (T m + 1) ≤ C) :
    Tendsto (fun m => pronicNorm (T m + 1) (fun n => receiverAdditiveDefect ε n (h m)) ^ 2 /
      dampedMobiusEnergy ε (T m + 1)) atTop (𝓝 0) := by
  apply HTGeometry.normalized_cost_tendsto_zero_of_uniform_small_budget
    (fun k m => pronicNorm (T m + 1) (fun n => receiverAdditiveDefect ε n k) ^ 2)
    (fun k => (k : ℝ) ^ (1 - (ε : ℝ)))
    (fun m => dampedMobiusEnergy ε (T m + 1)) (fun k m => sq_nonneg _) ?_ hE h hh
  intro δ hδ
  obtain ⟨B, _, hB⟩ := exists_uniform_subpower_recentered_budget ε hδ
  exact ⟨B, fun k m => hB k (T m + 1)⟩

theorem recentered_cofactor_energy_tendsto_zero_along (ε : SubcriticalDamping)
    (T h : ℕ → ℕ)
    (hE : Tendsto (fun m => dampedMobiusEnergy ε (T m + 1)) atTop atTop)
    (hh : ∃ C : ℝ, ∀ᶠ m in atTop,
      (h m : ℝ) ^ (1 - (ε : ℝ)) / dampedMobiusEnergy ε (T m + 1) ≤ C) (j : ℕ+) :
    Tendsto (fun m => pronicNorm (T m + 1)
      (rowDilate j (fun n => receiverAdditiveDefect ε n (h m))) ^ 2 /
      dampedMobiusEnergy ε (T m + 1)) atTop (𝓝 0) := by
  have hlim := (recentered_energy_tendsto_zero_along ε T h hE hh).const_mul (1 / (j : ℝ))
  rw [mul_zero] at hlim
  refine squeeze_zero (fun m => div_nonneg (sq_nonneg _) (dampedMobiusEnergy_nonneg _ _))
    (fun m => ?_) hlim
  have hzero : receiverAdditiveDefect ε 0 (h m) = 0 := by
    simp only [receiverAdditiveDefect, Nat.zero_add,
      ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      sub_zero, sub_self]
  have hnorm := pronicNorm_rowDilate_sq_le j.property (T m + 1)
    (fun n => receiverAdditiveDefect ε n (h m)) hzero
  have hdiv := div_le_div_of_nonneg_right hnorm (dampedMobiusEnergy_nonneg ε (T m + 1))
  rw [mul_div_assoc] at hdiv
  convert hdiv using 1 <;> rfl

/-- On escape every bounded source-power translation has its exact reset-origin boundary Gram. -/
theorem admits_or_resetOrigin_gram_tendsto (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ (L : ActualCofactorLimit ε) (h : ℕ → ℕ) (c : ℝ),
      (∃ C : ℝ, ∀ᶠ m in atTop,
        (h m : ℝ) ^ (1 - (ε : ℝ)) / dampedMobiusEnergy ε (L.subsequence m + 1) ≤ C) →
      Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (h m) ^ 2 /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 c) →
      ∀ j k : ℕ+, Tendsto (fun m =>
        pronicPairing (L.subsequence m + 1)
          (rowDilate j (resetOriginReceiver ε (h m)))
          (rowDilate k (resetOriginReceiver ε (h m))) /
            dampedMobiusEnergy ε (L.subsequence m + 1)) atTop
        (𝓝 (L.kernel j k + c / ((max (j : ℕ) (k : ℕ) : ℕ) : ℝ))) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with hpaid | hE
  · exact Or.inl hpaid
  refine Or.inr fun L h c hh hc j k => ?_
  have hT : Tendsto (fun m => L.subsequence m + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp L.strictMono.tendsto_atTop
  have hEL := hE.comp hT
  have hmain := originBoundaryMain_gram_tendsto L h hEL hc j k
  have hself (p : ℕ+) : Tendsto (fun m =>
      pronicNorm (L.subsequence m + 1) (rowDilate p (originBoundaryMain ε (h m))) ^ 2 /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 (L.kernel p p + c / (p : ℝ))) := by
    have hp := originBoundaryMain_gram_tendsto L h hEL hc p p
    simp_rw [pronicNorm_sq]
    simpa only [max_self, pronicPairing, pow_two] using hp
  have herror := normalized_moving_gram_perturbation_tendsto_zero
    (fun m => L.subsequence m + 1) (fun m => dampedMobiusEnergy ε (L.subsequence m + 1))
    (Eventually.of_forall fun m => receiverEnergy_succ_pos ε (L.subsequence m))
    (fun m => rowDilate j (originBoundaryMain ε (h m)))
    (fun m => rowDilate k (originBoundaryMain ε (h m)))
    (fun m => rowDilate j (fun n => receiverAdditiveDefect ε n (h m)))
    (fun m => rowDilate k (fun n => receiverAdditiveDefect ε n (h m)))
    (hself j) (hself k)
    (recentered_cofactor_energy_tendsto_zero_along ε L.subsequence h hEL hh j)
    (recentered_cofactor_energy_tendsto_zero_along ε L.subsequence h hEL hh k)
  have hlim := herror.add hmain
  rw [zero_add] at hlim
  apply hlim.congr
  intro m
  have hrow (p : ℕ+) :
      (fun n => rowDilate p (originBoundaryMain ε (h m)) n +
        rowDilate p (fun n => receiverAdditiveDefect ε n (h m)) n) =
          rowDilate p (resetOriginReceiver ε (h m)) := by
    funext n
    exact (resetOriginReceiver_eq ε (h m) (n / p)).symm
  rw [hrow j, hrow k]
  ring

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_resetOrigin_gram_tendsto
end
end


section
noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Reset-origin translations normalize by their exact extra step energy. -/
theorem admits_or_resetOrigin_own_gram_tendsto (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ (L : ActualCofactorLimit ε) (h : ℕ → ℕ) (c : ℝ),
      (∃ C : ℝ, ∀ᶠ m in atTop,
        (h m : ℝ) ^ (1 - (ε : ℝ)) / dampedMobiusEnergy ε (L.subsequence m + 1) ≤ C) →
      Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (h m) ^ 2 /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 c) →
      ∀ j k : ℕ+, Tendsto (fun m =>
        pronicPairing (L.subsequence m + 1)
          (rowDilate j (resetOriginReceiver ε (h m)))
          (rowDilate k (resetOriginReceiver ε (h m))) /
            pronicNorm (L.subsequence m + 1) (resetOriginReceiver ε (h m)) ^ 2) atTop
        (𝓝 ((L.kernel j k + c / ((max (j : ℕ) (k : ℕ) : ℕ) : ℝ)) / (1 + c))) := by
  rcases admits_or_resetOrigin_gram_tendsto ε with hpaid | hgram
  · exact Or.inl hpaid
  refine Or.inr fun L h c hh hc j k => ?_
  have hc0 : 0 ≤ c := ge_of_tendsto hc
    (Eventually.of_forall fun m => div_nonneg (sq_nonneg _) (dampedMobiusEnergy_nonneg _ _))
  have hden : Tendsto (fun m =>
      pronicNorm (L.subsequence m + 1) (resetOriginReceiver ε (h m)) ^ 2 /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 (1 + c)) := by
    have hp := hgram L h c hh hc 1 1
    have hone : ((1 : ℕ+) : ℕ) = 1 := rfl
    simp only [hone, max_self, Nat.cast_one] at hp
    simp_rw [pronicNorm_sq]
    simpa only [rowDilate, Nat.div_one, pronicPairing, pow_two,
      L.kernel_one_one, div_one] using hp
  have hlim := (hgram L h c hh hc j k).div hden (by positivity : (1 : ℝ) + c ≠ 0)
  apply hlim.congr
  intro m
  simp only [Pi.div_apply]
  by_cases hz : pronicNorm (L.subsequence m + 1) (resetOriginReceiver ε (h m)) ^ 2 = 0
  · simp only [hz, zero_div, div_zero]
  · field_simp [hz, (receiverEnergy_succ_pos ε (L.subsequence m)).ne']

/-- Every positive step-boundary mass is realized by shifted actual source rows on escape. -/
theorem admits_or_every_positive_resetOrigin_boundary_is_realized (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ c : ℝ, 0 < c →
      ∃ (L : ActualCofactorLimit ε) (h : ℕ → ℕ),
        (∀ᶠ m in atTop, h m < L.subsequence m) ∧
        Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (h m) ^ 2 /
          dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 c) ∧
        ∀ j k : ℕ+, Tendsto (fun m =>
          pronicPairing (L.subsequence m + 1)
            (rowDilate j (resetOriginReceiver ε (h m)))
            (rowDilate k (resetOriginReceiver ε (h m))) /
              pronicNorm (L.subsequence m + 1) (resetOriginReceiver ε (h m)) ^ 2) atTop
          (𝓝 ((L.kernel j k + c / ((max (j : ℕ) (k : ℕ) : ℕ) : ℝ)) / (1 + c))) := by
  by_cases hpaid : Admits dampedMobiusEnergy ε
  · exact Or.inl hpaid
  have hgram := (admits_or_resetOrigin_own_gram_tendsto ε).resolve_left hpaid
  refine Or.inr fun c hc => ?_
  obtain ⟨h, T, _, _, hT, hhT, htrace, hsmall⟩ :=
    (admits_or_exists_record_horizons ε
      (a := 1 - (ε : ℝ)) (by linarith only [ε.property.2])
      (by linarith only [ε.property.1]) hc).resolve_left hpaid
  obtain ⟨ns, hns, L, hL⟩ := exists_actualCofactorLimit_along_cofinal ε T hT
  have htrace' : Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (h (ns m)) ^ 2 /
      dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 c) := by
    convert htrace.comp hns.tendsto_atTop using 1
    funext m
    simp only [hL, Function.comp_apply]
  have hsmall' : Tendsto (fun m => (h (ns m) : ℝ) ^ (1 - (ε : ℝ)) /
      dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 0) := by
    convert hsmall.comp hns.tendsto_atTop using 1
    funext m
    simp only [hL, Function.comp_apply]
  refine ⟨L, h ∘ ns, ?_, htrace', ?_⟩
  · simpa only [hL, Function.comp_apply] using hns.tendsto_atTop.eventually hhT
  · apply hgram L (h ∘ ns) c ?_ htrace'
    refine ⟨1, ?_⟩
    exact (hsmall'.eventually (gt_mem_nhds zero_lt_one)).mono fun m hm => hm.le

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_every_positive_resetOrigin_boundary_is_realized
end
end
