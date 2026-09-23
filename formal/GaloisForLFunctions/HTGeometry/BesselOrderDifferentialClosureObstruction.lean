import GaloisForLFunctions.HTGeometry.BesselOrderImprimitivityBaseField
import GaloisForLFunctions.HTGeometry.DifferentiallyClosedAlgClosed
import GaloisForLFunctions.HTGeometry.DifferentiallyClosedNoUniversalJetRelation

/-!
# Concrete Bessel obstructions over a differential closure of the constants

The Bessel slope is embedded in the corpus's differential closure of the complex numbers equipped
with the zero derivation.  This discharges differential closedness, characteristic zero, slope
nonvanishing, and slope constancy internally: none is exposed as a premise of the concrete
Riccati or isomonodromy theorem.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

noncomputable section

/-- The complex constants with zero derivation. -/
@[reducible] def complexZeroDifferential : Differential ℂ where
  deriv := 0

local instance besselOrderDifferentialClosureObstructionLocalInst1 : Differential ℂ := complexZeroDifferential

/-- A concrete differentially closed extension of the complex constant field. -/
abbrev Constants : Type := diffClosure ℂ

noncomputable instance : CharZero Constants :=
  charZero_of_injective_ringHom (algebraMap ℚ Constants).injective

noncomputable instance : IsAlgClosed Constants :=
  isAlgClosed_of_isDifferentiallyClosed Constants

/-- Physical Bessel slope in the concrete differential closure. -/
def slope (s : ℝ) : Constants :=
  algebraMap ℂ Constants (2 / (s : ℂ))

theorem slope_ne_zero {s : ℝ} (hs : 0 < s) : slope s ≠ 0 := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have hbase : (2 / (s : ℂ) : ℂ) ≠ 0 := div_ne_zero (by norm_num) hsC
  intro h
  exact hbase ((algebraMap ℂ Constants).injective (by rw [slope] at h; simpa using h))

theorem deriv_slope_eq_zero (s : ℝ) : Differential.deriv (slope s) = 0 := by
  rw [slope, algebraMap_diffClosure, deriv_diffTowerLimitHom]
  change diffTowerLimitHom ℂ 0 0 = 0
  exact map_zero _

/-- The concrete constant extension used below is differentially closed. -/
theorem constants_isDifferentiallyClosed : IsDifferentiallyClosed Constants := by
  infer_instance

/-- No nonzero finite linear differential operator annihilates every element of the concrete
differential closure. -/
theorem constants_noUniversalJetRelation : NoUniversalJetRelation Constants :=
  noUniversalJetRelation_of_isDifferentiallyClosed

/-- No rational Riccati solution exists over the actual differential closure of the complex
constants, for every physical Bessel slope. -/
theorem modifiedBesselOrder_no_riccati_in_differentialClosure :
    ∀ s : ℝ, 0 < s →
      ¬ ∃ u : RatFunc Constants,
        u * FieldShift.ratShift u -
          algebraMap (Polynomial Constants) (RatFunc Constants)
            (Polynomial.C (slope s) * (Polynomial.X + Polynomial.C 1)) * u - 1 = 0 := by
  intro s hs
  exact FieldShift.orderBesselRiccati_no_ratFunc_solution (slope_ne_zero hs)

/-- The physical Bessel order module is not imprimitive over the actual differential closure. -/
theorem modifiedBesselOrder_no_imprimitive_pair_in_differentialClosure :
    ∀ s : ℝ, 0 < s →
      ¬ ∃ e p : RatFunc Constants,
        p ≠ 0 ∧
          FieldShift.ratShift e =
            e / p + 2 * FieldShift.orderShiftCoeff (slope s) ∧
          p * FieldShift.ratShift p =
            1 + FieldShift.orderShiftCoeff (slope s) * e +
              FieldShift.orderShiftCoeff (slope s) ^ (2 : ℕ) * p := by
  intro s hs
  rintro ⟨e, p, hp, hE, hP⟩
  exact FieldShift.orderBessel_no_imprimitive_pair (slope_ne_zero hs) hp hE hP

/-- The actual Bessel companion acquires no rational parameter connection after passing to the
differential closure of `ℂ`. Differential closedness and constancy of the physical slope are
discharged by construction. -/
theorem modifiedBesselOrder_no_isomonodromy_in_differentialClosure :
    ∀ s : ℝ, 0 < s →
      letI := coordinateTotalDifferential (K := Constants)
      ¬ ∃ B : Matrix (Fin 2) (Fin 2) (RatFunc Constants),
        B.map FieldShift.ratShift * FieldShift.besselOrderCompanion (slope s) =
          matrixDeriv (FieldShift.besselOrderCompanion (slope s)) +
            FieldShift.besselOrderCompanion (slope s) * B := by
  intro s hs
  exact FieldShift.besselOrder_no_matrix_isomonodromy
    (slope_ne_zero hs) (deriv_slope_eq_zero s)

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
