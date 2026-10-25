import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicCancellationInTruncatedMobiusReceivers
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicEnergyFromPrefixCancellation
import GaloisForLFunctions.BezoutValuationIncidence.SignedVaughanTailsVanishAtTheirAbsoluteScale

/-!
# Logarithmic energy savings for the Möbius interior

The actual Möbius pattern has the reciprocal zeta density. Its centered
floor prefix inherits every logarithmic norm saving below half damping;
subtracting the bounded active increment preserves these rates.
-/


open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The Möbius pattern uses exactly the reciprocal zeta density of the centered divisor prefix. -/
theorem patternPrefix_moebius_eq_centeredDivisorPrefix {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    patternPrefix ε moebiusReal n = pmPowerDampedCenteredDivisorPrefix ε n := by
  have hmean : (∑' d : ℕ, dampedSignWeight moebiusReal ε d / d) =
      (pmPowerDampedDivisorDensity ε).re := (hasSum_pmPowerDampedRealWeight_div hε).tsum_eq
  rw [patternPrefix, weightCenteredPrefix, hmean, pmPowerDampedCenteredDivisorPrefix_eq]
  rfl

/-- Actual Möbius cancellation gives every logarithmic saving for its damped divisor prefix. -/
theorem exists_pmPowerDampedCenteredDivisorPrefix_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      |pmPowerDampedCenteredDivisorPrefix ε n| ≤
        B * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q := by
  have hdiv (_a : Unit) (d : ℕ) (hd : 1 ≤ d) :
      |moebiusReal d| ≤ 1 * (d.divisors.card : ℝ) ^ 2 := by
    have hcard : (1 : ℝ) ≤ d.divisors.card := by
      exact_mod_cast (one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, by omega⟩⟩)
    exact (abs_moebiusReal_le_one' d).trans (by nlinarith only [hcard])
  have hsum (p : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ _a : Unit,
      |∑ d ∈ Icc 1 n, moebiusReal d| ≤ B * n / Real.log (n : ℝ) ^ p := by
    obtain ⟨B, hB, h⟩ := exists_uniform_sum_truncatedMoebius_log_rate p
    refine ⟨B, hB, h.mono fun n hn _a => ?_⟩
    simpa only [sum_truncatedMoebius_eq_sum_min, min_self] using hn n
  obtain ⟨B, hB, h⟩ := exists_uniform_weightCenteredPrefix_dampedSign_log_rate_of_divisor_square
    (s := fun _a : Unit => moebiusReal) hε hε2 (by norm_num : (0 : ℝ) ≤ 1) hdiv
    (fun _a => summable_dampedSignWeight_div_of_abs_le_one hε abs_moebiusReal_le_one') hsum q
  refine ⟨B, hB, h.mono fun n hn => ?_⟩
  rw [← patternPrefix_moebius_eq_centeredDivisorPrefix hε]
  exact hn ()

/-- The actual centered divisor receiver inherits every logarithmic pronic norm saving. -/
theorem exists_pmPowerDampedCenteredDivisorPrefix_pronicNorm_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℕ in atTop,
      pronicNorm (pmPowerDampedCenteredDivisorPrefix ε) T ≤
        B * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q := by
  have h1ε : 0 < 1 - ε := by linarith only [hε2]
  have hglobal (_a : Unit) (n : ℕ) (hn : 1 ≤ n) :
      |pmPowerDampedCenteredDivisorPrefix ε n| ≤
        (1 + 1 / (1 - ε) + 1 / ε) * (n : ℝ) ^ (1 - ε) := by
    have hc : DampedClass 1 ε (dampedSignWeight moebiusReal ε) := by
      intro d
      rw [dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      exact mul_le_mul_of_nonneg_right (abs_moebiusReal_le_one' d)
        (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    rw [← patternPrefix_moebius_eq_centeredDivisorPrefix hε]
    simpa only [one_mul, patternPrefix] using
      abs_weightCenteredPrefix_le_of_dampedClass hε (by linarith only [hε2]) hc hn
  have hlog (p : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ _a : Unit,
      |pmPowerDampedCenteredDivisorPrefix ε n| ≤
        B * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ p := by
    obtain ⟨B, hB, h⟩ := exists_pmPowerDampedCenteredDivisorPrefix_log_rate hε hε2.le p
    exact ⟨B, hB, h.mono fun n hn _a => hn⟩
  obtain ⟨B, hB, h⟩ := exists_uniform_pronicNorm_log_rate_of_prefix_log_rate
    (f := fun _a : Unit => pmPowerDampedCenteredDivisorPrefix ε) hε hε2
    (by positivity : 0 ≤ 1 + 1 / (1 - ε) + 1 / ε) hglobal hlog q
  exact ⟨B, hB, h.mono fun T hT => hT ()⟩

/-- Removing the bounded active increment preserves every logarithmic interior norm saving. -/
theorem exists_pmBezoutInteriorPrefix_pronicNorm_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℕ in atTop,
      pronicNorm (pmBezoutInteriorPrefix ε) T ≤
        B * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q := by
  obtain ⟨B, hB, hprefix⟩ := exists_pmPowerDampedCenteredDivisorPrefix_pronicNorm_log_rate hε hε2 q
  have hactive := eventually_pronicNorm_log_rate_of_uniform_bound
    (f := fun _a : Unit => fun n => -addDiff (pmActiveSawtoothComponent ε) n)
    (by linarith only [hε2] : 0 < 1 - 2 * ε) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (fun _a T => pronicNorm_le_of_abs_le (by norm_num) (fun n => by
      simpa only [abs_neg] using abs_addDiff_pmActiveSawtoothComponent_le_half hε.le n) T) q
  have heq : pmBezoutInteriorPrefix ε = fun n =>
      pmPowerDampedCenteredDivisorPrefix ε n + (-addDiff (pmActiveSawtoothComponent ε) n) := by
    funext n
    rw [pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior]
    ring
  refine ⟨B + 1 / 2, by positivity, ?_⟩
  filter_upwards [hprefix, hactive] with T hT hA
  rw [heq]
  exact (pronicNorm_add_le _ _ T).trans ((add_le_add hT (hA ())).trans_eq (by ring))

end GaloisForLFunctions.BezoutValuationIncidence
