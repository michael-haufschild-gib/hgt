import GaloisForLFunctions.RHTower.MaassHomogeneousSpaceCorrespondence
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.MetricSpace.Polish

/-!
# Haar measure on the actual real special linear group

Algebraic perfectness of SL2(R) kills every commutative character, including
Haar's modular character. Thus actual right translations preserve Haar measure.
No continuity theorem for the modular character is needed. This supplies the
unimodularity input to the congruence-quotient construction; it does not assert
a quotient fundamental domain or temperedness.
-/

open MeasureTheory
namespace GaloisForLFunctions.RHTower

instance realSL2LocallyCompactSpace : LocallyCompactSpace SL2R := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
instance realSL2SecondCountableTopology : SecondCountableTopology SL2R := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology
instance realSL2PolishSpace : PolishSpace SL2R := by
  haveI : PolishSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (PolishSpace (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace
instance realSL2MeasurableSpace : MeasurableSpace SL2R := borel SL2R
instance realSL2BorelSpace : BorelSpace SL2R := ⟨rfl⟩

/-- The actual real special linear group is algebraically perfect. -/
theorem realSL2_commutator_eq_top : commutator SL2R = ⊤ :=
  Matrix.SL2.commutator_eq_top (a := (2 : ℝ)) (by norm_num) (by norm_num)

/-- Perfectness kills every character into a commutative monoid. -/
theorem realSL2_commutativeCharacter_trivial {M : Type*} [CommMonoid M]
    (χ : SL2R →* M) (g : SL2R) : χ g = 1 := by
  have hg : χ.toHomUnits g = 1 :=
    Abelianization.commutator_subset_ker χ.toHomUnits
      (by rw [realSL2_commutator_eq_top]; trivial)
  exact congrArg (fun u : Mˣ => (u : M)) hg

/-- Unconditional triviality of the actual Haar modular character. -/
theorem realSL2_modularCharacter_eq_one (g : SL2R) :
    Measure.modularCharacter g = 1 :=
  realSL2_commutativeCharacter_trivial Measure.modularCharacter g

/-- Haar measure for the standard topology and Borel structure on SL2(R). -/
noncomputable def realSL2Haar : Measure SL2R := Measure.haar

instance realSL2Haar_isHaarMeasure : realSL2Haar.IsHaarMeasure :=
  inferInstanceAs (Measure.haar : Measure SL2R).IsHaarMeasure
instance realSL2Haar_innerRegular : realSL2Haar.InnerRegular :=
  inferInstanceAs (Measure.haar : Measure SL2R).InnerRegular

instance realSL2Haar_sigmaFinite : SigmaFinite realSL2Haar :=
  inferInstanceAs (SigmaFinite (Measure.haar : Measure SL2R))

instance realSL2Haar_rightInvariant : realSL2Haar.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
    change Measure.modularCharacter g • realSL2Haar = realSL2Haar
    rw [realSL2_modularCharacter_eq_one, one_smul]

/-- Actual right multiplication preserves Haar measure. -/
theorem realSL2Haar_rightTranslation (g : SL2R) :
    MeasurePreserving (fun x : SL2R => x * g) realSL2Haar realSL2Haar :=
  measurePreserving_mul_right realSL2Haar g
end GaloisForLFunctions.RHTower
