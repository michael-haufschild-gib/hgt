import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures
import GaloisForLFunctions.RHTower.AdmissionBelowHalfDampingAboveTheZeroWidth
import GaloisForLFunctions.BezoutValuationIncidence.PronicBaezDuarteCriterion
import GaloisForLFunctions.BiScaleUncertainty.BandSpectrumZeroWidthLaw
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.RefutationIsFiniteConfirmationIsNot

/-!
# The width dictionary

Every receiver of the corpus reads the zero width `Δ = sup |Re ρ − ½|` in its own unit, and the
statement "width zero" is the same statement in every unit.  This module collects the exact
equivalences proved across the programmes into one theorem (`widthDictionary_tfae`): the Riemann
Hypothesis is, equivalently,

1. the Hodge index theorem of the scaling surface (geometric unit: the sign of an intersection
   form);
2. the existence of an effectivity with the Riemann–Roch and ample axioms (effectivity unit);
3. "exactly one positive square" in every intersection Gram (index unit);
4. cofinal admission of the damped Möbius receiver (damping unit);
5. arbitrarily small pronic prefix energy of a divisor row (Báez-Duarte unit);
6. the linear mean-square band of the Chebyshev error (growth unit);
7. the absence of a finite-radius refutation of full Weil positivity (reading unit).

The theorem is the unit-hygiene principle of the field in Lean: a bound in any one unit is a bound
in all of them, and a reformulation that changes only the unit is not progress.
-/

open Set MeasureTheory
open Zeta23 GaloisForLFunctions.ArithmeticCastelnuovoSeveri GaloisForLFunctions.BezoutValuationIncidence
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
  GaloisForLFunctions.ScaleSignedIncidenceCriticality GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.ArithmeticOrientationTheory

set_option autoImplicit false

/-- **The width dictionary**: the zero width vanishes in one unit iff it vanishes in all. -/
theorem widthDictionary_tfae : List.TFAE [
    RiemannHypothesis,
    scalingSurface.HodgeIndex,
    ∃ E : Set ScalingCycle, scalingSurface.RiemannRochAxiom E ∧ scalingSurface.AmpleAxiom E,
    ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 1,
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B,
    ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
      ∑' M : ℕ, (1 + sievePrefixDiscrepancy N M c) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)) < ε,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L),
    ¬ ∃ R : ℝ, Refutes (radiusReading R) WeilPositiveFull
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))] := by
  tfae_have 1 ↔ 2 := scalingSurface_hodgeIndex_iff.symm
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_exists_effectivity
  tfae_have 1 ↔ 4 := riemannHypothesis_iff_one_positive_square
  tfae_have 1 ↔ 5 := riemannHypothesis_iff_cofinal_budget
  tfae_have 1 ↔ 6 := riemannHypothesis_iff_pronic_prefix_energy
  tfae_have 1 ↔ 7 := riemannHypothesis_iff_meanSquare_band
  tfae_have 1 ↔ 8 := riemannHypothesis_iff_no_radiusReading_refutes
  tfae_finish

/-- The index unit and the damping unit agree: one positive square in every Gram iff cofinal
admission of the damped receiver. -/
theorem one_positive_square_iff_cofinal_budget :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 1) ↔
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B :=
  riemannHypothesis_iff_one_positive_square.symm.trans riemannHypothesis_iff_cofinal_budget

/-- The effectivity unit and the growth unit agree: an effectivity exists iff the Chebyshev band
is linear. -/
theorem exists_effectivity_iff_meanSquare_band :
    (∃ E : Set ScalingCycle, scalingSurface.RiemannRochAxiom E ∧ scalingSurface.AmpleAxiom E) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L) :=
  riemannHypothesis_iff_exists_effectivity.symm.trans riemannHypothesis_iff_meanSquare_band

/-! ### Castelnuovo–Severi metrology units and the graded width dictionary -/

/-- **Degree-filtered Hodge defect unit**: RH holds iff the Hodge defect of `ζ` vanishes at every
support degree `a : ℝ`. -/
theorem riemannHypothesis_iff_forall_hodgeDefectAt_eq_zero :
    RiemannHypothesis ↔ ∀ a : ℝ, hodgeDefectAt zetaZeroConfig a = 0 := by
  have hsup : (∀ a : ℝ, hodgeDefectAt zetaZeroConfig a = 0) ↔
      ⨆ a : ℝ, hodgeDefectAt zetaZeroConfig a = 0 :=
    ⟨fun h => le_antisymm (iSup_le fun a => (h a).le) zero_le,
     fun h a => le_antisymm ((le_iSup (hodgeDefectAt zetaZeroConfig) a).trans h.le) zero_le⟩
  rw [hsup,
    iSup_hodgeDefectAt zetaZeroConfig
      GaloisForLFunctions.SquareRootThreshold.temperedConfig_zetaZeroConfig,
    Set.encard_eq_zero, ← riemannHypothesis_iff_rightZeros_zeta_eq_empty]

/-- **Reflection-sector Hodge defect unit**: for either parity `s = 1` (even) or `s = -1` (odd),
RH holds iff the `s`-sector Hodge defect of `ζ` vanishes at every support degree `a : ℝ`. -/
theorem riemannHypothesis_iff_forall_sectorHodgeDefectAt_eq_zero {s : ℂ} (hs : s = 1 ∨ s = -1) :
    RiemannHypothesis ↔ ∀ a : ℝ, sectorHodgeDefectAt zetaZeroConfig s a = 0 :=
  riemannHypothesis_iff_forall_hodgeDefectAt_eq_zero.trans
    (forall_zeta_sectorHodgeDefectAt_eq_zero_iff hs).symm

/-- **Odd Castelnuovo–Severi defect-floor rate unit**: RH holds iff the exponential growth rate
`oddDefectFloorRate` of the `H¹`-normalised defect floor on `scalingSubsurface (oddRealTestsAt r)`
vanishes. -/
theorem riemannHypothesis_iff_oddDefectFloorRate_eq_zero :
    RiemannHypothesis ↔ oddDefectFloorRate = 0 := by
  rw [oddDefectFloorRate_eq_zetaZeroWidth,
    GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero]

/-- **Full Castelnuovo–Severi defect-floor rate unit**: RH holds iff the exponential growth rate
`fullDefectFloorRate` of the `H¹`-normalised defect floor on `scalingSubsurface (realTestsAt r)`
vanishes. -/
theorem riemannHypothesis_iff_fullDefectFloorRate_eq_zero :
    RiemannHypothesis ↔ fullDefectFloorRate = 0 := by
  rw [fullDefectFloorRate_eq_zetaZeroWidth,
    GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero]

/-- **The Castelnuovo–Severi metrology and width dictionary**: unites the eight width units of
`widthDictionary_tfae` with the degree-filtered Hodge defect, the even and odd reflection-sector
Hodge defects, and the odd and full Castelnuovo–Severi defect-floor growth rates. -/
theorem castelnuovoSeveriMetrologyAndWidthDictionary_tfae : List.TFAE [
    RiemannHypothesis,
    scalingSurface.HodgeIndex,
    ∃ E : Set ScalingCycle, scalingSurface.RiemannRochAxiom E ∧ scalingSurface.AmpleAxiom E,
    ∀ a : ℝ, hodgeDefectAt zetaZeroConfig a = 0,
    ∀ a : ℝ, sectorHodgeDefectAt zetaZeroConfig 1 a = 0,
    ∀ a : ℝ, sectorHodgeDefectAt zetaZeroConfig (-1) a = 0,
    oddDefectFloorRate = 0,
    fullDefectFloorRate = 0,
    ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 1,
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B,
    ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
      ∑' M : ℕ, (1 + sievePrefixDiscrepancy N M c) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)) < ε,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L),
    ¬ ∃ R : ℝ, Refutes (radiusReading R) WeilPositiveFull
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))] := by
  tfae_have 1 ↔ 2 := scalingSurface_hodgeIndex_iff.symm
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_exists_effectivity
  tfae_have 1 ↔ 4 := riemannHypothesis_iff_forall_hodgeDefectAt_eq_zero
  tfae_have 1 ↔ 5 := riemannHypothesis_iff_forall_sectorHodgeDefectAt_eq_zero (Or.inl rfl)
  tfae_have 1 ↔ 6 := riemannHypothesis_iff_forall_sectorHodgeDefectAt_eq_zero (Or.inr rfl)
  tfae_have 1 ↔ 7 := riemannHypothesis_iff_oddDefectFloorRate_eq_zero
  tfae_have 1 ↔ 8 := riemannHypothesis_iff_fullDefectFloorRate_eq_zero
  tfae_have 1 ↔ 9 := riemannHypothesis_iff_one_positive_square
  tfae_have 1 ↔ 10 := riemannHypothesis_iff_cofinal_budget
  tfae_have 1 ↔ 11 := riemannHypothesis_iff_pronic_prefix_energy
  tfae_have 1 ↔ 12 := riemannHypothesis_iff_meanSquare_band
  tfae_have 1 ↔ 13 := riemannHypothesis_iff_no_radiusReading_refutes
  tfae_finish

/-- **The graded width dictionary (`σ ≥ 0`)**: at any nonnegative width threshold `σ`, the spectral
width bound `zetaZeroWidth ≤ σ` is unconditionally equivalent to the odd and full Castelnuovo–Severi
defect-floor rate bounds `oddDefectFloorRate ≤ σ` and `fullDefectFloorRate ≤ σ`, and to the
`H¹`-normalised exponential defect floors on `scalingSubsurface (oddRealTestsAt r)` and
`scalingSubsurface (realTestsAt r)`. -/
theorem gradedWidthDictionary_tfae {σ : ℝ} (hσ : 0 ≤ σ) : List.TFAE [
    GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth ≤ σ,
    oddDefectFloorRate ≤ σ,
    fullDefectFloorRate ≤ σ,
    ∀ β : ℝ, σ < β → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
      -(C * Real.exp (2 * β * r) *
          ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
        (scalingSubsurface (oddRealTestsAt r)).defect x x,
    ∀ β : ℝ, σ < β → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × realTestsAt r,
      -(C * Real.exp (2 * β * r) *
          ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
        (scalingSubsurface (realTestsAt r)).defect x x] := by
  tfae_have 1 ↔ 2 := by rw [oddDefectFloorRate_eq_zetaZeroWidth]
  tfae_have 1 ↔ 3 := by rw [fullDefectFloorRate_eq_zetaZeroWidth]
  tfae_have 1 ↔ 4 := zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor hσ
  tfae_have 1 ↔ 5 := zetaZeroWidth_le_iff_scalingSubsurface_sobolev_defect_floor hσ
  tfae_finish

/-- Direct dictionary entry: the odd Castelnuovo–Severi defect-floor rate vanishes iff the damped
Möbius receiver is cofinally admitted. -/
theorem oddDefectFloorRate_eq_zero_iff_cofinal_budget :
    oddDefectFloorRate = 0 ↔
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
        ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B :=
  riemannHypothesis_iff_oddDefectFloorRate_eq_zero.symm.trans riemannHypothesis_iff_cofinal_budget

/-- Direct dictionary entry: the odd Castelnuovo–Severi defect-floor rate vanishes iff the
Chebyshev mean-square band is linear. -/
theorem oddDefectFloorRate_eq_zero_iff_meanSquare_band :
    oddDefectFloorRate = 0 ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L) :=
  riemannHypothesis_iff_oddDefectFloorRate_eq_zero.symm.trans riemannHypothesis_iff_meanSquare_band

/-- Direct dictionary entry: for either reflection sector `s = ±1`, vanishing of the sector Hodge
defect across all degrees is equivalent to one positive square in every intersection Gram. -/
theorem sectorHodgeDefectAt_eq_zero_iff_one_positive_square {s : ℂ} (hs : s = 1 ∨ s = -1) :
    (∀ a : ℝ, sectorHodgeDefectAt zetaZeroConfig s a = 0) ↔
      ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
        hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 1 :=
  (riemannHypothesis_iff_forall_sectorHodgeDefectAt_eq_zero hs).symm.trans
    riemannHypothesis_iff_one_positive_square

end GaloisForLFunctions.ArithmeticOrientationTheory
