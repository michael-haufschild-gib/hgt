import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanCubicStatistics
import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanUniformSupport
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.Statistics.CharacterMoments
import GaloisForLFunctions.HTGeometry.KantorovichRubinsteinDuality

/-!
# A cubic lower bound for Kloosterman transport to Sato–Tate

Both laws live on the actual compact trace interval `[-2,2]`. The cubic
symmetric-power character is ten-Lipschitz there and has Sato–Tate mean zero.
Its exact nonzero Kloosterman mean therefore supplies a transport obstruction.
-/

open Finset MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

open GaloisForLFunctions.ArithmeticInnerFunctionTheory
open GaloisForLFunctions.HTGeometry

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- The compact trace space used by the Sato–Tate law. -/
abbrev SatoTateTraceInterval := Set.Icc (-2 : ℝ) 2

/-- Weil's bound places every normalized prime-field trace in the compact interval. -/
def compactKloostermanTrace (p : Nat.Primes) (a : ZMod p.val) : SatoTateTraceInterval :=
  ⟨satoTateKloostermanTrace p a, by
    have hp : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
    have hs : 0 < Real.sqrt (p.val : ℝ) := Real.sqrt_pos.mpr hp
    have hb : |satoTateKloostermanTrace p a| ≤ 2 := by
      rw [satoTateKloostermanTrace, abs_div, abs_of_pos hs]
      exact (div_le_iff₀ hs).mpr (abs_primeKloostermanTrace_le_two_sqrt p a)
    exact abs_le.mp hb⟩

/-- The trace of an angle is in `[-2,2]`, independently of the chosen representative. -/
def compactSatoTateTrace (theta : ℝ) : SatoTateTraceInterval :=
  ⟨2 * Real.cos theta, by
    constructor
    · linarith only [Real.neg_one_le_cos theta]
    · linarith only [Real.cos_le_one theta]⟩

private theorem continuous_compactSatoTateTrace : Continuous compactSatoTateTrace := by
  unfold compactSatoTateTrace
  fun_prop

/-- Empirical trace law with the singular parameter removed. -/
def puncturedKloostermanTraceLaw (p : Nat.Primes) : Measure SatoTateTraceInterval :=
  ((p.val - 1 : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ a ∈ (univ : Finset (ZMod p.val)).erase 0, Measure.dirac (compactKloostermanTrace p a)

instance (p : Nat.Primes) : IsProbabilityMeasure (puncturedKloostermanTraceLaw p) := by
  constructor
  have hp : (p.val : ℝ≥0∞) - 1 ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    exact_mod_cast p.property.one_lt
  simp [puncturedKloostermanTraceLaw, Measure.coe_finsetSum]
  exact ENNReal.inv_mul_cancel hp (by simp)

/-- Push the existing Sato–Tate angle measure into its compact trace interval. -/
def compactSatoTateLaw : Measure SatoTateTraceInterval :=
  satoTate.map compactSatoTateTrace

instance : IsProbabilityMeasure compactSatoTateLaw := by
  constructor
  rw [compactSatoTateLaw, Measure.map_apply continuous_compactSatoTateTrace.measurable
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- Integration against the punctured law retains each parameter's multiplicity. -/
theorem integral_puncturedKloostermanTraceLaw (p : Nat.Primes)
    (f : SatoTateTraceInterval → ℝ) :
    ∫ x, f x ∂puncturedKloostermanTraceLaw p =
      (∑ a ∈ (univ : Finset (ZMod p.val)).erase 0, f (compactKloostermanTrace p a)) /
        ((p.val : ℝ) - 1) := by
  rw [puncturedKloostermanTraceLaw, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Nat.cast_sub p.property.one_le, Nat.cast_one, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The limiting law kills the third symmetric-power character. -/
theorem integral_compactSatoTateLaw_cubic :
    ∫ x, cubicTraceCharacter x.val ∂compactSatoTateLaw = 0 := by
  rw [compactSatoTateLaw, integral_map continuous_compactSatoTateTrace.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : SatoTateTraceInterval => cubicTraceCharacter x.val)
      (satoTate.map compactSatoTateTrace) by unfold cubicTraceCharacter; fun_prop)]
  change (∫ theta, (2 * Real.cos theta) ^ 3 - 2 * (2 * Real.cos theta) ∂satoTate) = 0
  simp_rw [← cosSum_one]
  rw [integral_sub (integrable_cosSum_pow 1 3)
    (by simpa only [pow_one] using (integrable_cosSum_pow 1 1).const_mul 2),
    integral_const_mul, integral_cosSum_cube, integral_cosSum]
  norm_num

/-- Dividing the third character by ten produces an admissible transport test. -/
theorem lipschitz_cubicTraceCharacter_div_ten :
    LipschitzWith 1 (fun x : SatoTateTraceInterval => cubicTraceCharacter x.val / 10) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : (x.val : ℝ) ^ 2 ≤ 4 := by
    have h := mul_nonneg (sub_nonneg.mpr x.property.2)
      (show 0 ≤ x.val + 2 by linarith only [x.property.1])
    nlinarith only [h]
  have hy : (y.val : ℝ) ^ 2 ≤ 4 := by
    have h := mul_nonneg (sub_nonneg.mpr y.property.2)
      (show 0 ≤ y.val + 2 by linarith only [y.property.1])
    nlinarith only [h]
  have hc : |x.val ^ 2 + x.val * y.val + y.val ^ 2 - 2| ≤ 10 := by
    apply abs_le.mpr
    constructor
    · nlinarith only [sq_nonneg (x.val + y.val), sq_nonneg x.val, sq_nonneg y.val]
    · nlinarith only [hx, hy, sq_nonneg (x.val - y.val)]
  have he : cubicTraceCharacter x.val / 10 - cubicTraceCharacter y.val / 10 =
      (x.val - y.val) * ((x.val ^ 2 + x.val * y.val + y.val ^ 2 - 2) / 10) := by
    unfold cubicTraceCharacter
    ring
  change |cubicTraceCharacter x.val / 10 - cubicTraceCharacter y.val / 10| ≤
    1 * |x.val - y.val|
  rw [he, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10), one_mul]
  have hc' : |x.val ^ 2 + x.val * y.val + y.val ^ 2 - 2| / 10 ≤ 1 := by
    linarith only [hc]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc' (abs_nonneg (x.val - y.val))

/-- The exact cubic bias is a lower bound for the first Wasserstein distance. -/
theorem kloosterman_cubic_bias_le_wasserstein (p : Nat.Primes) :
    |∫ x, cubicTraceCharacter x.val ∂puncturedKloostermanTraceLaw p| / 10 ≤
      wassersteinOne (puncturedKloostermanTraceLaw p) compactSatoTateLaw := by
  have hp := (le_lipschitzDual (μ := puncturedKloostermanTraceLaw p)
    (ν := compactSatoTateLaw) lipschitz_cubicTraceCharacter_div_ten).trans
      lipschitzDual_le_wassersteinOne
  have hn := (le_lipschitzDual (μ := puncturedKloostermanTraceLaw p)
    (ν := compactSatoTateLaw) lipschitz_cubicTraceCharacter_div_ten.neg).trans
      lipschitzDual_le_wassersteinOne
  rw [integral_div, integral_div, integral_compactSatoTateLaw_cubic, zero_div, sub_zero] at hp
  change (∫ x, -(cubicTraceCharacter x.val / 10) ∂puncturedKloostermanTraceLaw p) -
    (∫ x, -(cubicTraceCharacter x.val / 10) ∂compactSatoTateLaw) ≤ _ at hn
  simp only [integral_neg, integral_div, integral_compactSatoTateLaw_cubic,
    zero_div, neg_zero, sub_zero] at hn
  have h := abs_le.mpr ⟨by linarith only [hn], hp⟩
  simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10)] using h

/-- Exact third-character mean, including the inseparable cyclotomic fiber. -/
theorem integral_puncturedKloostermanTraceLaw_cubic (p : Nat.Primes) :
    ∫ x, cubicTraceCharacter x.val ∂puncturedKloostermanTraceLaw p =
      (((cubicCyclotomicRoots (F := ZMod p.val)).card - 1 : ℝ) * (p.val : ℝ) ^ 2 + 1) /
        (((p.val : ℝ) - 1) * p.val * Real.sqrt (p.val : ℝ)) := by
  rw [integral_puncturedKloostermanTraceLaw]
  change (∑ a ∈ (univ : Finset (ZMod p.val)).erase 0,
    cubicTraceCharacter (satoTateKloostermanTrace p a)) / ((p.val : ℝ) - 1) = _
  rw [sum_primeKloosterman_cubic_character, div_div]
  congr 1
  ring

/-- Every prime-field law remains a positive Wasserstein distance from Sato–Tate. -/
theorem primeKloosterman_wasserstein_pos (p : Nat.Primes) :
    0 < wassersteinOne (puncturedKloostermanTraceLaw p) compactSatoTateLaw := by
  have hm : (∫ x, cubicTraceCharacter x.val ∂puncturedKloostermanTraceLaw p) ≠ 0 := by
    rw [integral_puncturedKloostermanTraceLaw]
    apply div_ne_zero
    · exact sum_primeKloosterman_cubic_character_ne_zero p
    · have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
      exact ne_of_gt (sub_pos.mpr hp)
  exact (div_pos (abs_pos.mpr hm) (by norm_num)).trans_le
    (kloosterman_cubic_bias_le_wasserstein p)

/-- Away from characteristic three, the cubic obstruction has square-root scale.
The exceptional inseparable fiber retains its exact smaller positive numerator. -/
theorem primeKloosterman_wasserstein_lower_bound (p : Nat.Primes) :
    (if (3 : ZMod p.val) = 0 then 1 else (p.val : ℝ) ^ 2 - 1) /
        (10 * (((p.val : ℝ) - 1) * p.val * Real.sqrt (p.val : ℝ))) ≤
      wassersteinOne (puncturedKloostermanTraceLaw p) compactSatoTateLaw := by
  have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hd : 0 < ((p.val : ℝ) - 1) * p.val * Real.sqrt (p.val : ℝ) :=
    mul_pos (mul_pos (sub_pos.mpr hp) (by linarith only [hp]))
      (Real.sqrt_pos.mpr (by linarith only [hp]))
  have hn : (if (3 : ZMod p.val) = 0 then 1 else (p.val : ℝ) ^ 2 - 1) ≤
      |((cubicCyclotomicRoots (F := ZMod p.val)).card - 1 : ℝ) *
        (p.val : ℝ) ^ 2 + 1| := by
    rw [cubicCyclotomicRoots_card]
    split_ifs <;> norm_num
    · linarith only [le_abs_self ((p.val : ℝ) ^ 2 + 1)]
    · nlinarith only [neg_le_abs (-(p.val : ℝ) ^ 2 + 1)]
  apply le_trans _ (kloosterman_cubic_bias_le_wasserstein p)
  rw [integral_puncturedKloostermanTraceLaw_cubic, abs_div, abs_of_pos hd,
    div_div, mul_comm _ 10]
  exact div_le_div_of_nonneg_right hn (mul_nonneg (by norm_num) hd.le)

#print axioms integral_compactSatoTateLaw_cubic
#print axioms lipschitz_cubicTraceCharacter_div_ten
#print axioms kloosterman_cubic_bias_le_wasserstein
#print axioms primeKloosterman_wasserstein_pos
#print axioms primeKloosterman_wasserstein_lower_bound

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
