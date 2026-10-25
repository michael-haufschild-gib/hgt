import GaloisForLFunctions.ArithmeticDefectRigidity.ResettingTheMovingOriginAddsTheMaxKernel
import GaloisForLFunctions.ArithmeticDefectRigidity.AConstantOriginBoundaryViolatesCofactorContraction

/-!
# Raw moving origins add constant Gram mass

Keeping the moving origin adds constant boundary covariance. Every positive
mass occurs in translated rows on escape and violates the zero-origin
contraction satisfied by actual common cofactor kernels.
-/
section
noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A raw translated source retains its moving value at index zero. -/
def unresetReceiver (ε : SubcriticalDamping) (k n : ℕ) : ℝ :=
  pmPowerDampedCenteredDivisorPrefix ε (n + k)

/-- The actual source plus the constant origin trace. -/
def constantBoundaryMain (ε : SubcriticalDamping) (k n : ℕ) : ℝ :=
  pmPowerDampedCenteredDivisorPrefix ε n + pmPowerDampedCenteredDivisorPrefix ε k

theorem unresetReceiver_eq (ε : SubcriticalDamping) (k n : ℕ) :
    unresetReceiver ε k n = constantBoundaryMain ε k n + receiverAdditiveDefect ε n k := by
  unfold unresetReceiver constantBoundaryMain receiverAdditiveDefect
  ring

/-- Pronic pairing ignores index zero, where the constant and first step differ. -/
theorem pronicPairing_one_eq_originStep (T : ℕ) (f : ℕ → ℝ) :
    pronicPairing T f (fun _ => 1) = pronicPairing T f (rowDilate (1 : ℕ+) originStep) := by
  unfold pronicPairing
  refine sum_congr rfl fun n hn => ?_
  simp only [rowDilate_originStep, if_pos (show ((1 : ℕ+) : ℕ) ≤ n from (mem_Icc.mp hn).1)]

/-- The positive pronic mass tends to one. -/
theorem pronicPairing_ones_tendsto :
    Tendsto (fun T => pronicPairing T (fun _ => 1) (fun _ => 1)) atTop (𝓝 (1 : ℝ)) := by
  have heq (T : ℕ) : pronicPairing T (fun _ => 1) (fun _ => 1) =
      pronicPairing T (rowDilate (1 : ℕ+) originStep) (rowDilate (1 : ℕ+) originStep) := by
    unfold pronicPairing
    refine sum_congr rfl fun n hn => ?_
    simp only [rowDilate_originStep, if_pos (show ((1 : ℕ+) : ℕ) ≤ n from (mem_Icc.mp hn).1)]
  have hone : ((1 : ℕ+) : ℕ) = 1 := rfl
  simpa only [heq, max_self, hone, Nat.cast_one, div_one] using
    pronicPairing_originSteps_tendsto 1 1

theorem constantBoundaryMain_pairing (ε : SubcriticalDamping) (h T : ℕ) (j k : ℕ+) :
    pronicPairing T (rowDilate j (constantBoundaryMain ε h))
        (rowDilate k (constantBoundaryMain ε h)) =
      pronicPairing T (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε))
        (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε)) +
      pmPowerDampedCenteredDivisorPrefix ε h *
        pronicPairing T (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε)) (fun _ => 1) +
      pmPowerDampedCenteredDivisorPrefix ε h *
        pronicPairing T (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε)) (fun _ => 1) +
      pmPowerDampedCenteredDivisorPrefix ε h ^ 2 *
        pronicPairing T (fun _ => 1) (fun _ => 1) := by
  simp only [pronicPairing, rowDilate, constantBoundaryMain, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- A retained raw origin contributes constant Gram mass, since every dilation fixes constants. -/
theorem constantBoundaryMain_gram_tendsto {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (h : ℕ → ℕ)
    (hE : Tendsto (fun m => dampedMobiusEnergy ε (L.subsequence m + 1)) atTop atTop)
    {c : ℝ} (hc : Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (h m) ^ 2 /
      dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 c)) (j k : ℕ+) :
    Tendsto (fun m => pronicPairing (L.subsequence m + 1)
      (rowDilate j (constantBoundaryMain ε (h m)))
      (rowDilate k (constantBoundaryMain ε (h m))) /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 (L.kernel j k + c)) := by
  have hT : Tendsto (fun m => L.subsequence m + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp L.strictMono.tendsto_atTop
  have hcross₁ := origin_scaled_source_step_pairing_tendsto_zero ε L.subsequence h hE hc j 1
  have hcross₂ := origin_scaled_source_step_pairing_tendsto_zero ε L.subsequence h hE hc k 1
  simp_rw [← pronicPairing_one_eq_originStep] at hcross₁ hcross₂
  have hmass := hc.mul (pronicPairing_ones_tendsto.comp hT)
  have hlim := (((L.converges j k).add hcross₁).add hcross₂).add hmass
  simp only [add_zero, mul_one] at hlim
  apply hlim.congr
  intro m
  simp only [Function.comp_apply]
  rw [constantBoundaryMain_pairing]
  unfold cofactorGram
  ring

/-- On escape every controlled raw translation has its exact constant-boundary Gram. -/
theorem admits_or_unreset_gram_tendsto (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ (L : ActualCofactorLimit ε) (h : ℕ → ℕ) (c : ℝ),
      (∃ C : ℝ, ∀ᶠ m in atTop,
        (h m : ℝ) ^ (1 - (ε : ℝ)) / dampedMobiusEnergy ε (L.subsequence m + 1) ≤ C) →
      Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (h m) ^ 2 /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 c) →
      ∀ j k : ℕ+, Tendsto (fun m =>
        pronicPairing (L.subsequence m + 1)
          (rowDilate j (unresetReceiver ε (h m)))
          (rowDilate k (unresetReceiver ε (h m))) /
            dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 (L.kernel j k + c)) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with hpaid | hE
  · exact Or.inl hpaid
  refine Or.inr fun L h c hh hc j k => ?_
  have hT : Tendsto (fun m => L.subsequence m + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp L.strictMono.tendsto_atTop
  have hEL := hE.comp hT
  have hmain := constantBoundaryMain_gram_tendsto L h hEL hc j k
  have hself (p : ℕ+) : Tendsto (fun m =>
      pronicNorm (L.subsequence m + 1) (rowDilate p (constantBoundaryMain ε (h m))) ^ 2 /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 (L.kernel p p + c)) := by
    have hp := constantBoundaryMain_gram_tendsto L h hEL hc p p
    simp_rw [pronicNorm_sq]
    simpa only [pronicPairing, pow_two] using hp
  have herror := normalized_moving_gram_perturbation_tendsto_zero
    (fun m => L.subsequence m + 1) (fun m => dampedMobiusEnergy ε (L.subsequence m + 1))
    (Eventually.of_forall fun m => receiverEnergy_succ_pos ε (L.subsequence m))
    (fun m => rowDilate j (constantBoundaryMain ε (h m)))
    (fun m => rowDilate k (constantBoundaryMain ε (h m)))
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
      (fun n => rowDilate p (constantBoundaryMain ε (h m)) n +
        rowDilate p (fun n => receiverAdditiveDefect ε n (h m)) n) =
          rowDilate p (unresetReceiver ε (h m)) := by
    funext n
    exact (unresetReceiver_eq ε (h m) (n / p)).symm
  rw [hrow j, hrow k]
  ring

/-- Own-energy normalization divides the raw constant boundary by one plus its mass. -/
theorem admits_or_unreset_own_gram_tendsto (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ (L : ActualCofactorLimit ε) (h : ℕ → ℕ) (c : ℝ),
      (∃ C : ℝ, ∀ᶠ m in atTop,
        (h m : ℝ) ^ (1 - (ε : ℝ)) / dampedMobiusEnergy ε (L.subsequence m + 1) ≤ C) →
      Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (h m) ^ 2 /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 c) →
      ∀ j k : ℕ+, Tendsto (fun m =>
        pronicPairing (L.subsequence m + 1)
          (rowDilate j (unresetReceiver ε (h m)))
          (rowDilate k (unresetReceiver ε (h m))) /
            pronicNorm (L.subsequence m + 1) (unresetReceiver ε (h m)) ^ 2) atTop
        (𝓝 ((L.kernel j k + c) / (1 + c))) := by
  rcases admits_or_unreset_gram_tendsto ε with hpaid | hgram
  · exact Or.inl hpaid
  refine Or.inr fun L h c hh hc j k => ?_
  have hc0 : 0 ≤ c := ge_of_tendsto hc
    (Eventually.of_forall fun m => div_nonneg (sq_nonneg _) (dampedMobiusEnergy_nonneg _ _))
  have hone : ((1 : ℕ+) : ℕ) = 1 := rfl
  have hden : Tendsto (fun m =>
      pronicNorm (L.subsequence m + 1) (unresetReceiver ε (h m)) ^ 2 /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 (1 + c)) := by
    have hp := hgram L h c hh hc 1 1
    simp_rw [pronicNorm_sq]
    simpa only [rowDilate, hone, Nat.div_one, pronicPairing, pow_two, L.kernel_one_one] using hp
  have hlim := (hgram L h c hh hc j k).div hden (by positivity : (1 : ℝ) + c ≠ 0)
  apply hlim.congr
  intro m
  simp only [Pi.div_apply]
  exact div_div_div_cancel_right₀ (receiverEnergy_succ_pos ε (L.subsequence m)).ne' _ _

/-- Every positive raw boundary mass occurs on escape, outside the actual zero-origin class. -/
theorem admits_or_every_positive_unreset_boundary_is_realized (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ c : ℝ, 0 < c →
      ∃ (L : ActualCofactorLimit ε) (h : ℕ → ℕ),
        (∀ᶠ m in atTop, h m < L.subsequence m) ∧
        (∀ j k : ℕ+, Tendsto (fun m =>
          pronicPairing (L.subsequence m + 1)
            (rowDilate j (unresetReceiver ε (h m)))
            (rowDilate k (unresetReceiver ε (h m))) /
              pronicNorm (L.subsequence m + 1) (unresetReceiver ε (h m)) ^ 2) atTop
          (𝓝 ((L.kernel j k + c) / (1 + c)))) ∧
        ∀ (δ : SubcriticalDamping) (M : ActualCofactorLimit δ),
          ¬ ∀ j k : ℕ+, M.kernel j k = (L.kernel j k + c) / (1 + c) := by
  by_cases hpaid : Admits dampedMobiusEnergy ε
  · exact Or.inl hpaid
  have hgram := (admits_or_unreset_own_gram_tendsto ε).resolve_left hpaid
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
  refine ⟨L, h ∘ ns, ?_, ?_, fun δ M => unreset_boundary_ne_actual_kernel L M hc⟩
  · simpa only [hL, Function.comp_apply] using hns.tendsto_atTop.eventually hhT
  · apply hgram L (h ∘ ns) c ?_ htrace'
    refine ⟨1, ?_⟩
    exact (hsmall'.eventually (gt_mem_nhds zero_lt_one)).mono fun m hm => hm.le

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_unreset_own_gram_tendsto
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_every_positive_unreset_boundary_is_realized
end
end

