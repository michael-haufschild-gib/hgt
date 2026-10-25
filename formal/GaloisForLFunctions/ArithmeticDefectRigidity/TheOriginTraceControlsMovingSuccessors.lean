import GaloisForLFunctions.ArithmeticDefectRigidity.FixedSuccessorsDisappearFromEscapingProfiles
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationSelfSimilarityOfThePronicMeasure
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheExactPronicCostOfACappedRow

/-!
# Origin traces and moving translations

The recentered translation has a sharp linear pronic budget. The raw translation
also carries the prefix at its new origin. Sublinearity makes every translation
with bounded squared length divided by receiver energy disappear on escape.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The centered increments occupy an interval of width one. -/
theorem abs_centeredResponse_sub_le_one (ε : SubcriticalDamping) (n m : ℕ) :
    |pmPowerDampedCenteredDivisorCoeff ε n - pmPowerDampedCenteredDivisorCoeff ε m| ≤ 1 := by
  have hn0 := pmPowerDampedDivisorCoeff_nonneg ε.property.1.le n
  have hn1 := pmPowerDampedDivisorCoeff_le_one ε.property.1.le n
  have hm0 := pmPowerDampedDivisorCoeff_nonneg ε.property.1.le m
  have hm1 := pmPowerDampedDivisorCoeff_le_one ε.property.1.le m
  unfold pmPowerDampedCenteredDivisorCoeff
  exact abs_le.mpr ⟨by linarith only [hn0, hm1], by linarith only [hn1, hm0]⟩

/-- Translation after subtracting its value at the origin. -/
def receiverAdditiveDefect (ε : ℝ) (n k : ℕ) : ℝ :=
  pmPowerDampedCenteredDivisorPrefix ε (n + k) -
    pmPowerDampedCenteredDivisorPrefix ε n - pmPowerDampedCenteredDivisorPrefix ε k

theorem receiverAdditiveDefect_symm (ε : ℝ) (n k : ℕ) :
    receiverAdditiveDefect ε n k = receiverAdditiveDefect ε k n := by
  unfold receiverAdditiveDefect
  rw [Nat.add_comm]
  ring

/-- Summing differences of centered increments controls the additive defect by either length. -/
theorem abs_receiverAdditiveDefect_le_left (ε : SubcriticalDamping) (n k : ℕ) :
    |receiverAdditiveDefect ε n k| ≤ (n : ℝ) := by
  induction n with
  | zero =>
    simp only [receiverAdditiveDefect, Nat.zero_add,
      ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      sub_zero, sub_self, abs_zero, Nat.cast_zero, le_refl]
  | succ n ih =>
    have heq : receiverAdditiveDefect ε (n + 1) k = receiverAdditiveDefect ε n k +
        (pmPowerDampedCenteredDivisorCoeff ε (n + k + 1) -
          pmPowerDampedCenteredDivisorCoeff ε (n + 1)) := by
      unfold receiverAdditiveDefect
      rw [show n + 1 + k = n + k + 1 by omega,
        pmPowerDampedCenteredDivisorPrefix_succ,
        pmPowerDampedCenteredDivisorPrefix_succ]
      ring
    rw [heq, Nat.cast_add, Nat.cast_one]
    exact (abs_add_le _ _).trans (add_le_add ih (abs_centeredResponse_sub_le_one ε _ _))

/-- The sharp pointwise envelope depends on the smaller of the two lengths. -/
theorem abs_receiverAdditiveDefect_le_min (ε : SubcriticalDamping) (n k : ℕ) :
    |receiverAdditiveDefect ε n k| ≤ (min n k : ℕ) := by
  have hn := abs_receiverAdditiveDefect_le_left ε n k
  have hk := abs_receiverAdditiveDefect_le_left ε k n
  rw [receiverAdditiveDefect_symm ε k n] at hk
  rw [Nat.cast_min]
  exact le_min hn hk

/-- The harmonic cap cost uniformly bounds the recentered translation energy. -/
theorem pronicNorm_receiverAdditiveDefect_sq_le_cost (ε : SubcriticalDamping) (k T : ℕ) :
    pronicNorm T (fun n => receiverAdditiveDefect ε n k) ^ 2 ≤ cappedLinearCost k := by
  refine le_trans ?_ (pronicNorm_cappedLinear_sq_le_cost k T)
  rw [pronicNorm_sq, pronicNorm_sq]
  apply sum_le_sum
  intro n _
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_receiverAdditiveDefect_le_min ε n k) 2

/-- Recentring at the new origin leaves only a linear translation budget. -/
theorem pronicNorm_receiverAdditiveDefect_sq_le (ε : SubcriticalDamping) (k T : ℕ) :
    pronicNorm T (fun n => receiverAdditiveDefect ε n k) ^ 2 ≤ 2 * (k : ℝ) :=
  (pronicNorm_receiverAdditiveDefect_sq_le_cost ε k T).trans (cappedLinearCost_le_two_mul k)

/-- Every subenergy recentered translation disappears in receiver normalization. -/
theorem recentered_successors_vanish_of_subenergy_length (ε : SubcriticalDamping) (k : ℕ → ℕ)
    (hk : Tendsto (fun T => (k T : ℝ) / dampedMobiusEnergy ε T) atTop (𝓝 0)) :
    Tendsto (fun T => pronicNorm T (fun n => receiverAdditiveDefect ε n (k T)) ^ 2 /
      dampedMobiusEnergy ε T) atTop (𝓝 0) := by
  refine squeeze_zero
    (fun T => div_nonneg (sq_nonneg _) (dampedMobiusEnergy_nonneg ε T))
    (fun T => div_le_div_of_nonneg_right
      (pronicNorm_receiverAdditiveDefect_sq_le ε (k T) T)
      (dampedMobiusEnergy_nonneg ε T)) ?_
  simpa only [mul_zero, mul_div_assoc] using hk.const_mul 2

section PrefixGrowth
open GaloisForLFunctions.TransHorizonIncidenceMechanics

theorem abs_receiver_le_sublinear_power (ε : SubcriticalDamping) {n : ℕ} (hn : 1 ≤ n) :
    |pmPowerDampedCenteredDivisorPrefix ε n| ≤
      (3 + 13 / (ε : ℝ)) * (n : ℝ) ^ (1 - (ε : ℝ)) := by
  have hS : ∀ x : ℕ, n ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ 1 * x := by
    intro x _
    rw [one_mul]
    calc
      _ ≤ ∑ e ∈ Icc 1 x, |moebiusReal e| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ Icc 1 x, (1 : ℝ) := sum_le_sum fun e _ => abs_moebiusReal_le_one' e
      _ = x := by simp
  have h := abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos
    zero_le_one ε.property.1 ε.property.2.le (fun d => abs_moebiusReal_le_one' d)
    hn le_rfl hS
  rw [← dampedDensity_eq_tsum ε.property.1,
    ← pmPowerDampedRealWeight_eq_dampedSignWeight] at h
  have heq : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n =
      pmPowerDampedCenteredDivisorPrefix ε n := by
    rw [weightCenteredPrefix, pmPowerDampedCenteredDivisorPrefix_eq]
    rfl
  rw [heq] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ 3 * (n : ℝ) ^ (1 - (ε : ℝ)) +
        13 / (ε : ℝ) * 1 * n * (n : ℝ) ^ (-(ε : ℝ)) := h
    _ = _ := by
      rw [show 1 - (ε : ℝ) = -(ε : ℝ) + 1 by ring, Real.rpow_add_one hn0.ne']
      ring

theorem receiver_div_nat_tendsto_zero (ε : SubcriticalDamping) :
    Tendsto (fun n : ℕ => pmPowerDampedCenteredDivisorPrefix ε n / (n : ℝ))
      atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_neg_atTop ε.property.1).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Tendsto (fun n : ℕ =>
      (3 + 13 / (ε : ℝ)) * (n : ℝ) ^ (-(ε : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul hpow
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  refine squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp only [Function.comp_apply]
  rw [abs_div, show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    _ ≤ ((3 + 13 / (ε : ℝ)) * (n : ℝ) ^ (1 - (ε : ℝ))) / n :=
      div_le_div_of_nonneg_right (abs_receiver_le_sublinear_power ε hn) hn0.le
    _ = _ := by
      rw [show 1 - (ε : ℝ) = -(ε : ℝ) + 1 by ring, Real.rpow_add_one hn0.ne']
      field_simp


end PrefixGrowth

/-- Raw translation splits into its origin value and a linearly priced remainder. -/
theorem successorDisplacementEnergy_le_origin_trace (ε : SubcriticalDamping) (k T : ℕ) :
    successorDisplacementEnergy ε k T ≤
      4 * (k : ℝ) + 2 * pmPowerDampedCenteredDivisorPrefix ε k ^ 2 := by
  have hcell (n : ℕ) :
      (pmPowerDampedCenteredDivisorPrefix ε (n + k) -
        pmPowerDampedCenteredDivisorPrefix ε n) ^ 2 ≤
      2 * receiverAdditiveDefect ε n k ^ 2 + 2 * pmPowerDampedCenteredDivisorPrefix ε k ^ 2 := by
    have heq : pmPowerDampedCenteredDivisorPrefix ε (n + k) -
        pmPowerDampedCenteredDivisorPrefix ε n =
        receiverAdditiveDefect ε n k + pmPowerDampedCenteredDivisorPrefix ε k := by
      unfold receiverAdditiveDefect
      ring
    rw [heq]
    nlinarith only [sq_nonneg (receiverAdditiveDefect ε n k -
      pmPowerDampedCenteredDivisorPrefix ε k)]
  have hmass : pronicNorm T (fun _ => 1) ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using pow_le_pow_left₀
      (pronicNorm_nonneg T (fun _ => 1)) (pronicNorm_one_le T) 2
  calc
    _ ≤ ∑ n ∈ Icc 1 T, (2 * receiverAdditiveDefect ε n k ^ 2 +
        2 * pmPowerDampedCenteredDivisorPrefix ε k ^ 2) / ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [successorDisplacementEnergy, pronicNorm_sq]
      exact sum_le_sum fun n _ => div_le_div_of_nonneg_right (hcell n) (by positivity)
    _ = 2 * pronicNorm T (fun n => receiverAdditiveDefect ε n k) ^ 2 +
        2 * pmPowerDampedCenteredDivisorPrefix ε k ^ 2 * pronicNorm T (fun _ => 1) ^ 2 := by
      rw [pronicNorm_sq, pronicNorm_sq, mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ 2 * (2 * (k : ℝ)) + 2 * pmPowerDampedCenteredDivisorPrefix ε k ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left (pronicNorm_receiverAdditiveDefect_sq_le ε k T)
        (by norm_num)) (mul_le_of_le_one_right (by positivity) hmass)
    _ = _ := by ring

/-- An explicit uniform quadratic coefficient for raw translation energy. -/
def successorRatioBudget (ε : SubcriticalDamping) (k : ℕ) : ℝ :=
  (4 * (k : ℝ) + 2 * pmPowerDampedCenteredDivisorPrefix ε k ^ 2) / (k : ℝ) ^ 2

/-- The origin trace and linear remainder together have little-oh quadratic energy. -/
theorem successorRatioBudget_tendsto_zero (ε : SubcriticalDamping) :
    Tendsto (successorRatioBudget ε) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun k : ℕ => (4 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hfirst.add (((receiver_div_nat_tendsto_zero ε).pow 2).const_mul 2)
  simp only [zero_pow two_ne_zero, mul_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  unfold successorRatioBudget
  field_simp

/-- The explicit coefficient bounds every horizon, including the zero translation. -/
theorem successorDisplacementEnergy_le_ratioBudget (ε : SubcriticalDamping) (k T : ℕ) :
    successorDisplacementEnergy ε k T ≤ (k : ℝ) ^ 2 * successorRatioBudget ε k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simpa only [Nat.cast_zero, zero_pow two_ne_zero, zero_mul] using
      successorDisplacementEnergy_le ε 0 T
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    calc
      _ ≤ 4 * (k : ℝ) + 2 * pmPowerDampedCenteredDivisorPrefix ε k ^ 2 :=
        successorDisplacementEnergy_le_origin_trace ε k T
      _ = _ := by unfold successorRatioBudget; field_simp

/-- Every positive quadratic coefficient admits a horizon-independent additive remainder. -/
theorem exists_uniform_subquadratic_successor_budget (ε : SubcriticalDamping)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k T : ℕ,
      successorDisplacementEnergy ε k T ≤ δ * (k : ℝ) ^ 2 + B := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((successorRatioBudget_tendsto_zero ε).eventually (gt_mem_nhds hδ))
  refine ⟨(K : ℝ) ^ 2, sq_nonneg _, fun k T => ?_⟩
  by_cases hk : K ≤ k
  · have h := mul_le_mul_of_nonneg_left (hK k hk).le (sq_nonneg (k : ℝ))
    exact (successorDisplacementEnergy_le_ratioBudget ε k T).trans
      (by nlinarith only [h, sq_nonneg (K : ℝ)])
  · have hk' : (k : ℝ) ≤ K := by exact_mod_cast le_of_lt (lt_of_not_ge hk)
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg k) hk' 2
    exact (successorDisplacementEnergy_le ε k T).trans
      (by nlinarith only [hsq, mul_nonneg hδ.le (sq_nonneg (k : ℝ))])

/-- Even translations of order the square root of receiver energy vanish on escape. -/
theorem admits_or_squareRoot_successors_disappear (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ k : ℕ → ℕ,
      (∃ C : ℝ, ∀ᶠ T : ℕ in atTop,
        (k T : ℝ) ^ 2 / dampedMobiusEnergy ε T ≤ C) →
      Tendsto (fun T => successorDisplacementEnergy ε (k T) T /
        dampedMobiusEnergy ε T) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun k ⟨C, hC⟩ => Metric.tendsto_nhds.mpr fun η hη => ?_
    have hCp : 0 < |C| + 1 := by positivity
    obtain ⟨B, hB0, hB⟩ := exists_uniform_subquadratic_successor_budget ε
      (show 0 < η / (2 * (|C| + 1)) by positivity)
    have hsmall : ∀ᶠ T : ℕ in atTop, B / dampedMobiusEnergy ε T < η / 2 :=
      (tendsto_const_nhds.div_atTop hE).eventually (gt_mem_nhds (by positivity))
    filter_upwards [hC, hsmall, hE.eventually_ge_atTop 1] with T hCT hBT hET
    have hEpos : 0 < dampedMobiusEnergy ε T := by linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (moving_successor_budget ε (k T) T).1]
    calc
      _ ≤ (η / (2 * (|C| + 1))) * ((k T : ℝ) ^ 2 / dampedMobiusEnergy ε T) +
          B / dampedMobiusEnergy ε T := by
        have h := div_le_div_of_nonneg_right (hB (k T) T) hEpos.le
        simpa only [add_div, mul_div_assoc] using h
      _ ≤ (η / (2 * (|C| + 1))) * (|C| + 1) + B / dampedMobiusEnergy ε T := by
        gcongr
        exact hCT.trans (by linarith [le_abs_self C])
      _ < η := by
        have heq : (η / (2 * (|C| + 1))) * (|C| + 1) = η / 2 := by field_simp
        rw [heq]
        linarith only [hBT]

end GaloisForLFunctions.ArithmeticDefectRigidity
