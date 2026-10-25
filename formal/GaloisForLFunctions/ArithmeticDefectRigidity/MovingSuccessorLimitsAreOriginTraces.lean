import GaloisForLFunctions.ArithmeticDefectRigidity.TheOriginTraceControlsMovingSuccessors
import GaloisForLFunctions.HTGeometry.UniformSmallBudgetsVanishAfterNormalization

/-!
# Moving successor limits are origin traces

The sharp additive-defect budget identifies a convergent normalized origin
trace as the entire pronic limit of a subenergy raw displacement. Uniform
subquadratic energy also forces every nonvanishing cofinal displacement to
have unbounded squared shift length relative to receiver energy.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The distance to a proposed constant trace is bounded by the recentered
translation cost and the scalar trace error. -/
theorem normalized_successor_trace_error_sq_le (ε : SubcriticalDamping)
    (k T : ℕ) (a : ℝ) :
    pronicNorm T (fun n =>
      (pmPowerDampedCenteredDivisorPrefix ε (n + k) -
        pmPowerDampedCenteredDivisorPrefix ε n) / Real.sqrt (dampedMobiusEnergy ε T) - a) ^ 2 ≤
      4 * ((k : ℝ) / dampedMobiusEnergy ε T) +
        2 * (pmPowerDampedCenteredDivisorPrefix ε k /
          Real.sqrt (dampedMobiusEnergy ε T) - a) ^ 2 := by
  let E := dampedMobiusEnergy ε T
  let b := pmPowerDampedCenteredDivisorPrefix ε k / Real.sqrt E - a
  have hE : 0 ≤ E := dampedMobiusEnergy_nonneg ε T
  have hcell (n : ℕ) :
      ((pmPowerDampedCenteredDivisorPrefix ε (n + k) -
        pmPowerDampedCenteredDivisorPrefix ε n) / Real.sqrt E - a) ^ 2 ≤
      (2 / E) * receiverAdditiveDefect ε n k ^ 2 + 2 * b ^ 2 := by
    have heq : (pmPowerDampedCenteredDivisorPrefix ε (n + k) -
        pmPowerDampedCenteredDivisorPrefix ε n) / Real.sqrt E - a =
        receiverAdditiveDefect ε n k / Real.sqrt E + b := by
      dsimp only [b, receiverAdditiveDefect]
      ring
    have hsq : (receiverAdditiveDefect ε n k / Real.sqrt E) ^ 2 =
        receiverAdditiveDefect ε n k ^ 2 / E := by
      rw [div_pow, Real.sq_sqrt hE]
    rw [heq]
    calc
      _ ≤ 2 * (receiverAdditiveDefect ε n k / Real.sqrt E) ^ 2 + 2 * b ^ 2 := by
        nlinarith only [sq_nonneg (receiverAdditiveDefect ε n k / Real.sqrt E - b)]
      _ = _ := by rw [hsq]; ring
  have hmass : pronicNorm T (fun _ => 1) ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using pow_le_pow_left₀
      (pronicNorm_nonneg T (fun _ => 1)) (pronicNorm_one_le T) 2
  calc
    _ ≤ ∑ n ∈ Icc 1 T,
        ((2 / E) * receiverAdditiveDefect ε n k ^ 2 + 2 * b ^ 2) /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [pronicNorm_sq]
      exact sum_le_sum fun n _ => div_le_div_of_nonneg_right (hcell n) (by positivity)
    _ = (2 / E) * pronicNorm T (fun n => receiverAdditiveDefect ε n k) ^ 2 +
        2 * b ^ 2 * pronicNorm T (fun _ => 1) ^ 2 := by
      rw [pronicNorm_sq, pronicNorm_sq, mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ (2 / E) * (2 * (k : ℝ)) + 2 * b ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (pronicNorm_receiverAdditiveDefect_sq_le ε k T)
          (div_nonneg (by norm_num) hE))
        (mul_le_of_le_one_right (by positivity) hmass)
    _ = _ := by dsimp only [E, b]; ring

/-- When shift length is subenergy, a convergent scalar origin trace is the
whole normalized raw displacement in pronic norm, along any horizons. -/
theorem normalized_successor_energy_tendsto_origin_trace (ε : SubcriticalDamping)
    (T k : ℕ → ℕ) {a : ℝ}
    (hk : Tendsto (fun m => (k m : ℝ) / dampedMobiusEnergy ε (T m)) atTop (𝓝 0))
    (ha : Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (k m) /
      Real.sqrt (dampedMobiusEnergy ε (T m))) atTop (𝓝 a)) :
    Tendsto (fun m => pronicNorm (T m) (fun n =>
      (pmPowerDampedCenteredDivisorPrefix ε (n + k m) -
        pmPowerDampedCenteredDivisorPrefix ε n) /
          Real.sqrt (dampedMobiusEnergy ε (T m)) - a) ^ 2) atTop (𝓝 0) := by
  have hb := (ha.sub_const a).pow 2
  rw [sub_self, zero_pow two_ne_zero] at hb
  have hlim := (hk.const_mul 4).add (hb.const_mul 2)
  simp only [mul_zero, add_zero] at hlim
  exact squeeze_zero (fun m => sq_nonneg _)
    (fun m => normalized_successor_trace_error_sq_le ε (k m) (T m) a) hlim

/-- The normalized raw displacement converges in pronic norm to its limiting
constant origin trace when shift length is subenergy. -/
theorem normalized_successor_tendsto_origin_trace (ε : SubcriticalDamping)
    (T k : ℕ → ℕ) {a : ℝ}
    (hk : Tendsto (fun m => (k m : ℝ) / dampedMobiusEnergy ε (T m)) atTop (𝓝 0))
    (ha : Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (k m) /
      Real.sqrt (dampedMobiusEnergy ε (T m))) atTop (𝓝 a)) :
    Tendsto (fun m => pronicNorm (T m) (fun n =>
      (pmPowerDampedCenteredDivisorPrefix ε (n + k m) -
        pmPowerDampedCenteredDivisorPrefix ε n) /
          Real.sqrt (dampedMobiusEnergy ε (T m)) - a)) atTop (𝓝 0) := by
  have h := (normalized_successor_energy_tendsto_origin_trace ε T k hk ha).sqrt
  have heq (m : ℕ) : Real.sqrt (pronicNorm (T m) (fun n =>
      (pmPowerDampedCenteredDivisorPrefix ε (n + k m) -
        pmPowerDampedCenteredDivisorPrefix ε n) /
          Real.sqrt (dampedMobiusEnergy ε (T m)) - a) ^ 2) =
      pronicNorm (T m) (fun n =>
        (pmPowerDampedCenteredDivisorPrefix ε (n + k m) -
          pmPowerDampedCenteredDivisorPrefix ε n) /
            Real.sqrt (dampedMobiusEnergy ε (T m)) - a) :=
    Real.sqrt_sq (pronicNorm_nonneg _ _)
  simpa only [heq, Real.sqrt_zero] using h

/-- Nonvanishing raw displacement on cofinal horizons forces the squared
shift length to exceed every energy-relative bound frequently on escape. -/
theorem admits_or_nonvanishing_successors_require_unbounded_scale (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ T k : ℕ → ℕ,
      Tendsto T atTop atTop →
      ¬ Tendsto (fun m => successorDisplacementEnergy ε (k m) (T m) /
        dampedMobiusEnergy ε (T m)) atTop (𝓝 0) →
      ∀ C : ℝ, ∃ᶠ m in atTop, C < (k m : ℝ) ^ 2 / dampedMobiusEnergy ε (T m) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with hpaid | hE
  · exact Or.inl hpaid
  refine Or.inr fun T k hT hnonzero C => ?_
  change ¬ ∀ᶠ m in atTop, ¬ C < (k m : ℝ) ^ 2 / dampedMobiusEnergy ε (T m)
  intro hbound
  apply hnonzero
  apply HTGeometry.normalized_cost_tendsto_zero_of_uniform_small_budget
    (fun k m => successorDisplacementEnergy ε k (T m))
    (fun k => (k : ℝ) ^ 2) (fun m => dampedMobiusEnergy ε (T m))
    (fun k m => successorDisplacementEnergy_nonneg ε k (T m)) ?_ (hE.comp hT) k
    ⟨C, hbound.mono fun m hm => le_of_not_gt hm⟩
  intro δ hδ
  obtain ⟨B, _, hB⟩ := exists_uniform_subquadratic_successor_budget ε hδ
  exact ⟨B, fun k m => hB k (T m)⟩

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.normalized_successor_tendsto_origin_trace
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_nonvanishing_successors_require_unbounded_scale
end
