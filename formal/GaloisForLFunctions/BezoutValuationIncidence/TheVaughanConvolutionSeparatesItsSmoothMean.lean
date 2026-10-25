import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicCancellationInTheVaughanConvolution
import GaloisForLFunctions.BezoutValuationIncidence.LogarithmicCancellationSurvivesTheDampedFloorTransform
import GaloisForLFunctions.BezoutValuationIncidence.VaughanPacketsHaveAnExactResidualEnergyDensity

/-!
# The uniform fluctuation of the Vaughan convolution

Subtracting the undamped harmonic mean leaves a divisor-square bounded family
with every logarithmic partial-sum and damped-prefix saving. Linearity separates
the centered convolution row into its unit pattern and this actual fluctuation.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The convolution coefficient after removing its undamped mean. -/
def pmVaughanConvolutionFluctuation (U V d : ℕ) : ℝ :=
  pmPronicVaughanSmallSmallCoeff U V d - deningerHarmonicPartial U * deningerHarmonicPartial V

/-- The damped receiver prefix of the convolution after removing its undamped mean. -/
def pmVaughanConvolutionFluctuationPrefix (ε : ℝ) (U V n : ℕ) : ℝ :=
  weightCenteredPrefix (dampedSignWeight (pmVaughanConvolutionFluctuation U V) ε)
    (∑' d : ℕ, dampedSignWeight (pmVaughanConvolutionFluctuation U V) ε d / d) n

/-- The coefficient fluctuation retains a common square-divisor majorant. -/
theorem abs_pmVaughanConvolutionFluctuation_le (U V : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    |pmVaughanConvolutionFluctuation U V d| ≤ 2 * (d.divisors.card : ℝ) ^ 2 := by
  have hμ : |deningerHarmonicPartial U * deningerHarmonicPartial V| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (abs_deningerHarmonicPartial_le_one U)
      (abs_deningerHarmonicPartial_le_one V) (abs_nonneg _) zero_le_one
  have hcard : (1 : ℝ) ≤ d.divisors.card := by
    exact_mod_cast (one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, by omega⟩⟩)
  have hsq : (1 : ℝ) ≤ (d.divisors.card : ℝ) ^ 2 := by nlinarith only [hcard]
  exact (abs_sub _ _).trans
    (by linarith only [abs_pmPronicVaughanSmallSmallCoeff_le U V d, hμ, hsq])

/-- Every positively damped coefficient fluctuation has an absolutely convergent reciprocal mass. -/
theorem summable_pmVaughanConvolutionFluctuation_div {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    Summable (fun d : ℕ => dampedSignWeight (pmVaughanConvolutionFluctuation U V) ε d / d) := by
  have hmajor := (summable_pmVaughanFloorMajorant_div hε).mul_left 2
  refine hmajor.of_norm_bounded fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.cast_zero, div_zero, norm_zero, mul_zero, le_refl]
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hd : (0 : ℝ) < d),
      dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (abs_pmVaughanConvolutionFluctuation_le U V hd)
        (Real.rpow_nonneg (Nat.cast_nonneg d) (-ε))) (Nat.cast_nonneg d)
    simpa only [pmVaughanFloorMajorant, mul_div_assoc, mul_assoc] using h

/-- The fluctuation partial sum is the exact error in the undamped convolution mean. -/
theorem sum_pmVaughanConvolutionFluctuation (U V n : ℕ) :
    (∑ d ∈ Icc 1 n, pmVaughanConvolutionFluctuation U V d) =
      pmUndampedVaughanConvolutionPrefix U V n -
        (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V := by
  simp only [pmVaughanConvolutionFluctuation, sum_sub_distrib, sum_const,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, pmUndampedVaughanConvolutionPrefix]
  ring

/-- The actual fluctuation family has every logarithmic partial-sum saving. -/
theorem exists_uniform_pmVaughanConvolutionFluctuation_log_rate (p : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ x : ℕ in atTop, ∀ U V : ℕ,
      |∑ d ∈ Icc 1 x, pmVaughanConvolutionFluctuation U V d| ≤
        B * x / Real.log (x : ℝ) ^ p := by
  simpa only [sum_pmVaughanConvolutionFluctuation] using
    exists_uniform_pmUndampedVaughanConvolutionPrefix_log_rate p

/-- Uniform logarithmic cancellation holds after damping and applying the floor transform. -/
theorem exists_uniform_pmVaughanConvolutionFluctuation_prefix_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ U V : ℕ,
      |weightCenteredPrefix (dampedSignWeight (pmVaughanConvolutionFluctuation U V) ε)
        (∑' d : ℕ, dampedSignWeight (pmVaughanConvolutionFluctuation U V) ε d / d) n| ≤
          K * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q := by
  have hS (p : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ x : ℕ in atTop, ∀ a : ℕ × ℕ,
      |∑ d ∈ Icc 1 x, pmVaughanConvolutionFluctuation a.1 a.2 d| ≤
        B * x / Real.log (x : ℝ) ^ p := by
    obtain ⟨B, hB, h⟩ := exists_uniform_pmVaughanConvolutionFluctuation_log_rate p
    refine ⟨B, hB, h.mono fun x hx a => hx a.1 a.2⟩
  obtain ⟨K, hK, h⟩ := exists_uniform_weightCenteredPrefix_dampedSign_log_rate_of_divisor_square
    (s := fun a : ℕ × ℕ => pmVaughanConvolutionFluctuation a.1 a.2) hε hε2
      (by norm_num : (0 : ℝ) ≤ 2)
      (fun a d hd => abs_pmVaughanConvolutionFluctuation_le a.1 a.2 hd)
      (fun a => summable_pmVaughanConvolutionFluctuation_div hε a.1 a.2) hS q
  exact ⟨K, hK, h.mono fun n hn U V => hn (U, V)⟩

/-- The damped small-small coefficient has finite reciprocal mass at every cutoff pair. -/
theorem summable_damped_pmPronicVaughanSmallSmallCoeff_div {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    Summable (fun d : ℕ => dampedSignWeight (pmPronicVaughanSmallSmallCoeff U V) ε d / d) := by
  refine (summable_pmVaughanFloorMajorant_div hε).of_norm_bounded fun d => ?_
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, dampedSignWeight, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (abs_pmPronicVaughanSmallSmallCoeff_le U V d)
      (Real.rpow_nonneg (Nat.cast_nonneg d) _)) (Nat.cast_nonneg d)

/-- The reciprocal mass of the convolution is the negative mean of the third Vaughan piece. -/
theorem tsum_damped_pmPronicVaughanSmallSmallCoeff_div {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    (∑' d : ℕ, dampedSignWeight (pmPronicVaughanSmallSmallCoeff U V) ε d / d) =
      -pmPronicVaughanMean ε U V 2 := by
  have h₁ := tendsto_pmFloorAverage (summable_damped_pmPronicVaughanSmallSmallCoeff_div hε U V)
  have h₂ := (tendsto_pmPronicVaughanPiece_div_nat hε U V 2).neg
  simp only [pmPronicVaughanPiece_smallSmall_eq_floorAverage, neg_neg] at h₂
  exact tendsto_nhds_unique h₁ h₂

/-- The centered convolution piece is the negative receiver prefix of its actual coefficient. -/
theorem pmPronicVaughanCentredPiece_smallSmall_eq_prefix {ε : ℝ} (hε : 0 < ε) (U V n : ℕ) :
    pmPronicVaughanCentredPiece ε U V n 2 =
      -weightCenteredPrefix (dampedSignWeight (pmPronicVaughanSmallSmallCoeff U V) ε)
        (∑' d : ℕ, dampedSignWeight (pmPronicVaughanSmallSmallCoeff U V) ε d / d) n := by
  rw [pmPronicVaughanCentredPiece, weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
    tsum_damped_pmPronicVaughanSmallSmallCoeff_div hε]
  have h := pmPronicVaughanPiece_smallSmall_eq_floorAverage ε U V n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pmPronicVaughanPiece]
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    unfold pmFloorAverage at h
    have heq := congrArg (fun x : ℝ => x * n) h
    simp only [neg_mul, div_mul_cancel₀ _ hn0] at heq
    rw [heq]
    simp only [dampedSignWeight]
    ring

/-- Removing the undamped mean leaves exactly the common smooth unit pattern and the fluctuating receiver. -/
theorem pmPronicVaughanCentredPiece_smallSmall_eq_unit_add_fluctuation
    {ε : ℝ} (hε : 0 < ε) (U V n : ℕ) :
    pmPronicVaughanCentredPiece ε U V n 2 =
      -(deningerHarmonicPartial U * deningerHarmonicPartial V) * patternPrefix ε unitSign n -
        weightCenteredPrefix (dampedSignWeight (pmVaughanConvolutionFluctuation U V) ε)
          (∑' d : ℕ, dampedSignWeight (pmVaughanConvolutionFluctuation U V) ε d / d) n := by
  let a := deningerHarmonicPartial U * deningerHarmonicPartial V
  have heq (d : ℕ) : dampedSignWeight (pmVaughanConvolutionFluctuation U V) ε d / d =
      dampedSignWeight (pmPronicVaughanSmallSmallCoeff U V) ε d / d -
        a * (dampedSignWeight unitSign ε d / d) := by
    simp only [dampedSignWeight, pmVaughanConvolutionFluctuation, unitSign, a]
    ring
  have hmass : (∑' d : ℕ, dampedSignWeight (pmVaughanConvolutionFluctuation U V) ε d / d) =
      (∑' d : ℕ, dampedSignWeight (pmPronicVaughanSmallSmallCoeff U V) ε d / d) -
        a * (∑' d : ℕ, dampedSignWeight unitSign ε d / d) := by
    simp_rw [heq]
    rw [(summable_damped_pmPronicVaughanSmallSmallCoeff_div hε U V).tsum_sub
      ((summable_unit_weight hε).mul_left a), tsum_mul_left]
  rw [pmPronicVaughanCentredPiece_smallSmall_eq_prefix hε, hmass, patternPrefix]
  simp only [weightCenteredPrefix, dampedSignWeight, pmVaughanConvolutionFluctuation,
    unitSign, sub_mul, sum_sub_distrib, ← mul_sum, a]
  ring

end GaloisForLFunctions.BezoutValuationIncidence
