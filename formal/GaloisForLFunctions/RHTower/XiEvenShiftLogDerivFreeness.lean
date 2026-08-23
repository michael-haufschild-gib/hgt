import GaloisForLFunctions.RHTower.XiTranslationOrbitFreeness

/-!
# Even-shift freeness of the completed logarithmic derivative

This is the exact constant-coefficient specialization of the full finite
differential-translation freeness theorem.  In rotated upper-end coordinate
`s = -I z`, `upperEndTranslationMeroEquiv (I * (2k))` is the ordinary shift
`s ↦ s + 2k`; hence `xiEvenShiftLogDerivFilter P` is precisely
`P(T)(xi' / xi)` represented in the genuine rational upper-end meromorphic
field.  Every nonzero finite filter is hypertranscendental over that rational
coordinate field.
-/

namespace RHTower

open Complex Filter
open scoped Differential

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

local instance xiEvenFilterUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiEvenFilterUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiEvenFilterUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiEvenFilterRationalBaseDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiEvenFilterRationalBaseAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField :=
  ⟨fun x => derivationClosedDifferential_apply
    upperEndRationalCoordinateField upperEndRationalCoordinateField_derivationClosed x⟩

/-- The finite even-shift filter `P(T)(xi'/xi)` in rotated upper-end coordinates. -/
def xiEvenShiftLogDerivFilter (P : Polynomial ℂ) : upperEndMeroField :=
  ∑ j : Fin (P.natDegree + 1),
    P.coeff j • upperEndTranslationMeroEquiv (Complex.I * (2 * (j : ℕ) : ℂ))
      xiLogDerivRotatedUpperEndCarrier

private def xiEvenShiftLogDerivBlocks (P : Polynomial ℂ) :
    Fin (P.natDegree + 1) → Polynomial ℂ :=
  fun j => Polynomial.C (P.coeff j)

private def xiEvenShiftLogDerivShifts (P : Polynomial ℂ) :
    Fin (P.natDegree + 1) → ℂ :=
  fun j => (2 * (j : ℕ) : ℂ)

private theorem xiEvenShiftLogDerivFilter_eq_orbitCombination (P : Polynomial ℂ) :
    xiEvenShiftLogDerivFilter P =
      upperEndOrbitCombination (xiEvenShiftLogDerivShifts P)
        (xiEvenShiftLogDerivBlocks P) xiLogDerivRotatedUpperEndCarrier := by
  unfold xiEvenShiftLogDerivFilter upperEndOrbitCombination xiEvenShiftLogDerivBlocks
    xiEvenShiftLogDerivShifts
  simp

private theorem injective_xiEvenShiftLogDerivShifts (P : Polynomial ℂ) :
    Function.Injective (xiEvenShiftLogDerivShifts P) := by
  intro i j hij
  apply Fin.ext
  apply Nat.cast_injective (R := ℂ)
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  dsimp [xiEvenShiftLogDerivShifts] at hij
  exact mul_left_cancel₀ htwo hij

private theorem exists_nonzero_xiEvenShiftLogDerivBlock {P : Polynomial ℂ} (hP : P ≠ 0) :
    ∃ j, xiEvenShiftLogDerivBlocks P j ≠ 0 := by
  refine ⟨Fin.last P.natDegree, ?_⟩
  rw [xiEvenShiftLogDerivBlocks, Polynomial.C_ne_zero]
  simpa [Polynomial.coeff_natDegree] using (Polynomial.leadingCoeff_ne_zero.mpr hP)

/-- **Unconditional even-shift freeness.** Every nonzero polynomial filter of the completed
logarithmic derivative is hypertranscendental over the rational coordinate field. -/
theorem xiEvenShiftLogDerivFilter_hypertranscendentalOver {P : Polynomial ℂ} (hP : P ≠ 0) :
    HypertranscendentalOver upperEndRationalCoordinateField (xiEvenShiftLogDerivFilter P) := by
  rw [xiEvenShiftLogDerivFilter_eq_orbitCombination]
  exact xiLogDerivRotatedUpperEndCarrier_orbitCombination_hypertranscendentalOver'
    (xiEvenShiftLogDerivShifts P) (xiEvenShiftLogDerivBlocks P)
    (injective_xiEvenShiftLogDerivShifts P) (exists_nonzero_xiEvenShiftLogDerivBlock hP)

end

end RHTower
