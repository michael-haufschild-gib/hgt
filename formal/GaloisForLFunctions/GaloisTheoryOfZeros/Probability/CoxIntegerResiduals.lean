import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxDetectionBoundary
import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.FiniteGammaCoxLaw

/-!
# Uniform Gamma–Cox classification of integer residuals

Integrality supplies a unit gap at every nonzero residual. The common error
envelope is independent of the integer's size. Consequently a fixed finite
number of candidates may change arbitrarily with concentration. Even `n`
candidates at concentration `n` have vanishing total error probability.
-/

open Filter Topology
open scoped BigOperators Classical
namespace GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
noncomputable section

/-- A nonzero integer supplies a uniform squared-residual gap. -/
theorem int_cast_sq_ge_one (n : ℤ) (hn : n ≠ 0) : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hs : (0 : ℤ) < n ^ 2 := sq_pos_of_ne_zero hn
  have hi : (1 : ℤ) ≤ n ^ 2 := by omega
  exact_mod_cast hi

/-- Integer false-positive weights have a uniform exponential envelope. -/
theorem weight_int_le (K : ℝ) (n : ℤ) (hK : 0 ≤ K) (hn : n ≠ 0) :
    weight K (n : ℝ) ≤ Real.exp (-K) := by
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_nonneg hK (sub_nonneg.mpr (int_cast_sq_ge_one n hn))]

/-- The exact worst nonzero integer detection probability occurs at residual one. -/
theorem detection_int_le_one (K : ℝ) (n : ℤ) (hK : 0 ≤ K) (hn : n ≠ 0) :
    detection K (n : ℝ) ≤ detection K 1 := by
  apply detection_antitone_sq K (n : ℝ) 1 hK
  simpa only [one_pow] using int_cast_sq_ge_one n hn

/-- Sum of the true-zero miss rate and the universal integer false-positive envelope. -/
def integerEnvelope (K : ℝ) : ℝ :=
  Real.exp (-K * Real.log 2) + K * Real.exp (-K)

/-- Each integer candidate contributes at most the same error envelope. -/
theorem integer_term_le (K : ℝ) (n : ℤ) (hK : 0 ≤ K) :
    (if (n : ℝ) = 0 then Real.exp (-K * Real.log 2) else K * weight K (n : ℝ)) ≤
      integerEnvelope K := by
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero, ite_true]
    exact le_add_of_nonneg_right (mul_nonneg hK (Real.exp_pos _).le)
  · have hr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [if_neg hr]
    exact (mul_le_mul_of_nonneg_left (weight_int_le K n hK hn) hK).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- The uniform integer error envelope tends to zero. -/
theorem tendsto_integerEnvelope : Tendsto integerEnvelope atTop (𝓝 0) := by
  change Tendsto (fun K => Real.exp (-K * Real.log 2) + K * Real.exp (-K)) atTop (𝓝 0)
  simpa [detection_zero, weight] using
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_detection 0)).add
      (tendsto_mean_nonzero 1 one_ne_zero))

/-- Simultaneous integer classification has a bound depending only on candidate count. -/
theorem binaryLaw_integer_error_le {ι : Type*} [Fintype ι] (K : ℝ) (g : ι → ℤ) :
    (binaryLaw K (fun i => (g i : ℝ))).real
      {b | b ≠ zeroPattern (fun i => (g i : ℝ))} ≤
        (Fintype.card ι : ℝ) * integerEnvelope (max K 0) := by
  refine (binaryLaw_error_le K (fun i => (g i : ℝ))).trans ?_
  unfold errorBound
  calc
    _ ≤ ∑ _i : ι, integerEnvelope (max K 0) :=
      Finset.sum_le_sum fun i _ => integer_term_le (max K 0) (g i) (le_max_right K 0)
    _ = _ := by simp

/-- Integer data may vary arbitrarily with concentration, without a convergence assumption. -/
theorem tendsto_moving_integer_error {ι : Type*} [Fintype ι] (g : ℝ → ι → ℤ) :
    Tendsto (fun K => (binaryLaw K (fun i => (g K i : ℝ))).real
      {b | b ≠ zeroPattern (fun i => (g K i : ℝ))}) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => MeasureTheory.measureReal_nonneg)
    (Eventually.of_forall fun K => binaryLaw_integer_error_le K (g K)) ?_
  have he : Tendsto (fun K => (Fintype.card ι : ℝ) * integerEnvelope K) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_integerEnvelope.const_mul (Fintype.card ι : ℝ)
  apply he.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with K hK
  rw [max_eq_left hK]

/-- A proved integer zero criterion transfers uniform consistency to moving predicates. -/
theorem tendsto_moving_integer_classification {ι : Type*} [Fintype ι]
    (g : ℝ → ι → ℤ) (P : ℝ → ι → Prop) [∀ K, DecidablePred (P K)]
    (hP : ∀ K i, g K i = 0 ↔ P K i) :
    Tendsto (fun K => (binaryLaw K (fun i => (g K i : ℝ))).real
      {b | b ≠ fun i => decide (P K i)}) atTop (𝓝 0) := by
  have hp (K : ℝ) : zeroPattern (fun i => (g K i : ℝ)) = fun i => decide (P K i) := by
    funext i
    by_cases h : P K i <;> simp [zeroPattern, hP, h]
  simpa only [hp] using tendsto_moving_integer_error g

/-- The error envelope also dominates a linearly growing number of candidates. -/
theorem tendsto_mul_integerEnvelope :
    Tendsto (fun K => K * integerEnvelope K) atTop (𝓝 0) := by
  have ha : Tendsto (fun K : ℝ => K * Real.exp (-K * Real.log 2)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm, neg_mul, mul_neg] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (Real.log 2)
        (Real.log_pos (by norm_num))
  have hb : Tendsto (fun K : ℝ => K ^ 2 * Real.exp (-K)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, neg_one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 1 zero_lt_one
  have h := ha.add hb
  simp only [zero_add] at h
  apply h.congr'
  exact Eventually.of_forall fun K => by dsimp [integerEnvelope]; ring

/-- Concentration `n` classifies `n` arbitrary integer candidates simultaneously. -/
theorem tendsto_expanding_integer_error (g : (n : ℕ) → Fin n → ℤ) :
    Tendsto (fun n : ℕ => (binaryLaw (n : ℝ) (fun i => (g n i : ℝ))).real
      {b | b ≠ zeroPattern (fun i => (g n i : ℝ))}) atTop (𝓝 0) := by
  have hb (n : ℕ) : (binaryLaw (n : ℝ) (fun i => (g n i : ℝ))).real
      {b | b ≠ zeroPattern (fun i => (g n i : ℝ))} ≤ (n : ℝ) * integerEnvelope n := by
    simpa [max_eq_left (Nat.cast_nonneg n)] using binaryLaw_integer_error_le (n : ℝ) (g n)
  exact squeeze_zero' (Eventually.of_forall fun _ => MeasureTheory.measureReal_nonneg)
    (Eventually.of_forall hb) (tendsto_mul_integerEnvelope.comp tendsto_natCast_atTop_atTop)

/-- Expanding integer candidate sets retain consistency for any proved zero criterion. -/
theorem tendsto_expanding_integer_classification
    (g : (n : ℕ) → Fin n → ℤ) (P : (n : ℕ) → Fin n → Prop)
    [∀ n, DecidablePred (P n)] (hP : ∀ n i, g n i = 0 ↔ P n i) :
    Tendsto (fun n : ℕ => (binaryLaw (n : ℝ) (fun i => (g n i : ℝ))).real
      {b | b ≠ fun i => decide (P n i)}) atTop (𝓝 0) := by
  have hp (n : ℕ) : zeroPattern (fun i => (g n i : ℝ)) = fun i => decide (P n i) := by
    funext i
    by_cases h : P n i <;> simp [zeroPattern, hP, h]
  simpa only [hp] using tendsto_expanding_integer_error g

end
end GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.int_cast_sq_ge_one
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.weight_int_le
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.detection_int_le_one
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.integer_term_le
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_integerEnvelope
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.binaryLaw_integer_error_le
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_moving_integer_error
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_moving_integer_classification
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_mul_integerEnvelope
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_expanding_integer_error
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_expanding_integer_classification
