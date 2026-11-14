import GaloisForLFunctions.ArithmeticInnerFunctionTheory.Statistics.CharacterMoments
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi

/-!
# Gaussian limits for independent Sato–Tate character sums

The countable product of the existing Sato–Tate measure gives a canonical
family with exact independence. Every nontrivial symmetric-power character
has mean zero and variance one, so its normalized sums converge to the
standard Gaussian. The local third and fourth moments remain explicit.
-/

open MeasureTheory ProbabilityTheory Filter
open GaloisForLFunctions.CompletedArithmeticForms (cosSum)
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

/-- Countably many independent Sato–Tate angles. -/
def satoTateSequenceMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => satoTate

instance : IsProbabilityMeasure satoTateSequenceMeasure := by
  unfold satoTateSequenceMeasure
  infer_instance

/-- The degree `m+1` character at the `i`-th angle. -/
def satoTateCharacterCoordinate (m i : ℕ) (ω : ℕ → ℝ) : ℝ :=
  cosSum (ω i) (m + 1)

theorem hasLaw_satoTate_eval (i : ℕ) :
    HasLaw (Function.eval i) satoTate satoTateSequenceMeasure :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => satoTate) i).hasLaw

/-- Every coordinate has exactly the one-angle character moments. -/
theorem integral_satoTateCharacterCoordinate_pow (m i r : ℕ) :
    ∫ ω, satoTateCharacterCoordinate m i ω ^ r ∂satoTateSequenceMeasure =
      ∫ θ, cosSum θ (m + 1) ^ r ∂satoTate := by
  exact (hasLaw_satoTate_eval i).integral_comp
    (((continuous_cosSum (m + 1)).pow r).aestronglyMeasurable)

theorem iIndepFun_satoTateCharacterCoordinate (m : ℕ) :
    iIndepFun (satoTateCharacterCoordinate m) satoTateSequenceMeasure :=
  iIndepFun_infinitePi (fun _ : ℕ => measurable_cosSum (m + 1))

theorem identDistrib_satoTateCharacterCoordinate (m i j : ℕ) :
    IdentDistrib (satoTateCharacterCoordinate m i) (satoTateCharacterCoordinate m j)
      satoTateSequenceMeasure satoTateSequenceMeasure :=
  ((hasLaw_satoTate_eval i).identDistrib (hasLaw_satoTate_eval j)).comp
    (measurable_cosSum (m + 1))

/-- Every nontrivial symmetric-power character has a standard Gaussian limit
under independent Sato–Tate sampling. All independence and moment inputs are proved. -/
theorem tendstoInDistribution_satoTateCharacter (m : ℕ) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        ∑ i ∈ Finset.range n, satoTateCharacterCoordinate m i ω)
      atTop (id : ℝ → ℝ) (fun _ => satoTateSequenceMeasure) (gaussianReal 0 1) := by
  apply tendstoInDistribution_inv_sqrt_mul_sum HasLaw.id
  · have h := integral_satoTateCharacterCoordinate_pow m 0 1
    simpa only [pow_one, integral_cosSum, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, if_false] using h
  · change (∫ ω, satoTateCharacterCoordinate m 0 ω ^ 2 ∂satoTateSequenceMeasure) = 1
    rw [integral_satoTateCharacterCoordinate_pow]
    exact (cosSum_fluctuation_moments m).2.1
  · exact iIndepFun_satoTateCharacterCoordinate m
  · intro i
    exact identDistrib_satoTateCharacterCoordinate m i 0

#print axioms integral_satoTateCharacterCoordinate_pow
#print axioms iIndepFun_satoTateCharacterCoordinate
#print axioms identDistrib_satoTateCharacterCoordinate
#print axioms tendstoInDistribution_satoTateCharacter

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
