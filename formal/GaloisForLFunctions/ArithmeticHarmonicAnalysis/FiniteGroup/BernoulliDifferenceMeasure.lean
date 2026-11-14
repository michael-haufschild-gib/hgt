import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.BernoulliSubproductMeasure
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.FiniteAutocorrelation
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.PopularDifferenceSets

/-!
# Positive difference measures and fourth-power character decay

Taking the quotient of two independent subproduct selections produces a probability
measure supported exactly on the subproduct difference set. Its character transform
is nonnegative, and its squared spectral mass contracts by `(9/16)^R` when `R` local
character values have real part at most one half.
-/

open Finset
open scoped Classical Pointwise

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

noncomputable section

variable {G ι : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [DecidableEq ι]

/-- Probability mass of the quotient of two independent subproduct selections. -/
def subproductDifferenceMass (q : ι → G) (I : Finset ι) (g : G) : ℝ :=
  finiteAutocorrelation (subproductMass q I) g

omit [DecidableEq ι] in
/-- Symmetrizing preserves total probability mass. -/
theorem sum_subproductDifferenceMass (q : ι → G) (I : Finset ι) :
    ∑ g, subproductDifferenceMass q I g = 1 := by
  simp only [subproductDifferenceMass, sum_finiteAutocorrelation, sum_subproductMass, one_pow]

omit [DecidableEq ι] in
/-- Every difference coefficient is nonnegative. -/
theorem subproductDifferenceMass_nonneg (q : ι → G) (I : Finset ι) (g : G) :
    0 ≤ subproductDifferenceMass q I g := by
  exact finiteAutocorrelation_nonneg
    (fun x => NNReal.mk (subproductMass q I x) (subproductMass_nonneg q I x)) g

/-- Positive difference mass is equivalent to actual representation as a quotient of subproducts. -/
theorem subproductDifferenceMass_pos_iff (q : ι → G) (I : Finset ι) (g : G) :
    0 < subproductDifferenceMass q I g ↔ g ∈ subproducts q I * (subproducts q I)⁻¹ := by
  have hsupport : positiveWeightSupport
      (fun x => NNReal.mk (subproductMass q I x) (subproductMass_nonneg q I x)) =
        subproducts q I := by
    ext x
    simp only [positiveWeightSupport, mem_filter, mem_univ, true_and, NNReal.coe_mk,
      subproductMass_pos_iff]
  have h := finiteAutocorrelation_pos_iff
    (fun x => NNReal.mk (subproductMass q I x) (subproductMass_nonneg q I x)) g
  simpa only [NNReal.coe_mk, hsupport, subproductDifferenceMass] using h

omit [DecidableEq ι] in
/-- The difference measure has the squared Bernoulli multiplier as its exact character transform. -/
theorem sum_subproductDifferenceMass_character (q : ι → G) (I : Finset ι) (χ : G →* Circle) :
    ∑ g, (subproductDifferenceMass q I g : ℂ) * (χ g : ℂ) =
      (Complex.normSq (bernoulliCharacterProduct χ q I) : ℂ) := by
  simp only [subproductDifferenceMass]
  rw [finiteAutocorrelation_character, sum_subproductMass_character]

omit [DecidableEq ι] in
/-- The actual difference-measure transform obeys fourth-power character decay. -/
theorem subproductDifferenceMass_fourth_decay (q : ι → G) (I : Finset ι) (χ : G →* Circle) :
    Complex.normSq (∑ g, (subproductDifferenceMass q I g : ℂ) * (χ g : ℂ)) ≤
      (9 / 16 : ℝ) ^ (I.filter fun i => (χ (q i) : ℂ).re ≤ 1 / 2).card := by
  rw [sum_subproductDifferenceMass_character, Complex.normSq_ofReal, ← pow_two]
  exact bernoulliCharacterProduct_fourth_decay χ q I

/-- A zero difference coefficient forces the original subproduct set below half-density. -/
theorem subproductDifferenceMass_positive_or_half (q : ι → G) (I : Finset ι) (g : G) :
    0 < subproductDifferenceMass q I g ∨ 2 * (subproducts q I).card ≤ Fintype.card G := by
  rcases difference_hit_or_half (subproducts q I) g with hg | hsmall
  · exact Or.inl ((subproductDifferenceMass_pos_iff q I g).mpr hg)
  · exact Or.inr hsmall

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.sum_subproductDifferenceMass
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subproductDifferenceMass_nonneg
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subproductDifferenceMass_pos_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.sum_subproductDifferenceMass_character
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subproductDifferenceMass_fourth_decay
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subproductDifferenceMass_positive_or_half
