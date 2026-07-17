import GaloisForLFunctions.HTGeometry.GammaOrientationQuotientBoundary

/-!
# Separated-center Gamma reflection clocks

The mirror quotient `Gamma(-z+a) / Gamma(z+a)` is the basic value observable of many reflection
and scattering clocks.  Euler reflection moves its two contributions to positive-slope
translation orbits represented by `a` and `1-a`.  Distinct orbits each have charge `-1`; when the
orbits collide, they merge to charge `-2`.  Hence the quotient is unconditionally
hypertranscendental.  The older separated-center theorem remains as the explicit two-orbit branch.

This is an observability theorem, not an evolution theorem.  It supplies the reusable bridge from
a reflected Gamma value relation to the existing oriented-orbit superselection classifier.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance gammaReflectionRatioDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance gammaReflectionRatioIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring Set.univ) := Ring.toIntAlgebra _

local instance gammaReflectionRatioIntAlgebraMero :
    Algebra ℤ (meroField Set.univ) := Ring.toIntAlgebra _

local instance gammaReflectionRatioIntAlgebraRatFunc :
    Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _

local instance gammaReflectionRatioDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance gammaReflectionRatioRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance gammaReflectionRatioRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance gammaReflectionRatioDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance gammaReflectionRatioCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- The reflected Gamma value clock `Gamma(-z+a) / Gamma(z+a)`. -/
def gammaReflectionRatioMero (a : ℂ) : meroField Set.univ :=
  gammaNegativeShiftMero a / gammaShiftMero a

/-- The reflected quotient has two oriented cells: a positive-slope denominator at orbit `a`
and a negative-slope numerator whose reflected orbit is `1-a`. -/
theorem gammaReflectionRatioMero_eq_orientedProduct (a : ℂ) :
    gammaReflectionRatioMero a =
      gammaOrientedProductMero
        ![a, 1 - a]
        (fun _ : Fin 2 => ![0])
        (fun c : Fin 2 => ![![(-1 : ℤ)], ![(0 : ℤ)]] c)
        (fun c : Fin 2 => ![![(0 : ℤ)], ![(1 : ℤ)]] c) := by
  simp [gammaReflectionRatioMero, gammaOrientedProductMero, div_eq_mul_inv]
  ring

/-- **Separated-center reflection theorem.**  If the positive and reflected Gamma centers are
not integer translates, their two nonzero charges force the mirror quotient to be
hypertranscendental over `ℂ(X)`. -/
theorem hypertranscendentalOver_gammaReflectionRatioMero_of_separated
    (a : ℂ) (hsep : ∀ k : ℤ, 2 * a - 1 ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ) (gammaReflectionRatioMero a) := by
  rw [gammaReflectionRatioMero_eq_orientedProduct]
  let b : Fin 2 → ℂ := ![a, 1 - a]
  let nn : Fin 2 → Fin 1 → ℕ := fun _ => ![0]
  let p : Fin 2 → Fin 1 → ℤ := fun c => ![![(-1 : ℤ)], ![(0 : ℤ)]] c
  let n : Fin 2 → Fin 1 → ℤ := fun c => ![![(0 : ℤ)], ![(1 : ℤ)]] c
  have horbit : ∀ c c', c ≠ c' → ∀ k : ℤ, b c - b c' ≠ (k : ℂ) := by
    intro c c' hcc k
    fin_cases c <;> fin_cases c'
    · exact (hcc rfl).elim
    · intro hk
      apply hsep k
      calc
        2 * a - 1 = a - (1 - a) := by ring
        _ = (k : ℂ) := by simpa [b] using hk
    · intro hk
      apply hsep (-k)
      calc
        2 * a - 1 = -((1 - a) - a) := by ring
        _ = -(k : ℂ) := by simpa [b] using congrArg Neg.neg hk
        _ = ((-k : ℤ) : ℂ) := by simp
    · exact (hcc rfl).elim
  have h :=
    (hypertranscendentalOver_mul_gammaOrientedProductMero_iff_exists_charge_ne_zero
      b nn p n 1 one_ne_zero
      (by simpa using
        (HTGeometry.differentialAlgebraicOver_algebraMap
          (F := RatFunc ℂ) (E := meroField Set.univ) 1)) horbit).2
      (by
        refine ⟨0, ?_⟩
        norm_num [gammaOrientedOrbitCharge, p, n])
  simpa [b, nn, p, n] using h

/-- The reflected quotient is the inverse of the positive-over-negative orientation quotient at
the same center. -/
theorem gammaReflectionRatioMero_eq_inv_oppositeShiftQuotient (a : ℂ) :
    gammaReflectionRatioMero a = (gammaOppositeShiftQuotientMero a a)⁻¹ := by
  have hneg : gammaNegativeShiftMero a ≠ 0 := by
    rw [gammaNegativeShiftMero_reflection]
    exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero a)
      (inv_ne_zero (gammaShiftMero_ne_zero (1 - a)))
  rw [gammaReflectionRatioMero, gammaOppositeShiftQuotientMero]
  field_simp [gammaShiftMero_ne_zero a, hneg]

/-- **Unconditional reflection-clock theorem.**  Every reflected Gamma ratio is HT.  Distinct
centers give two nonzero orbits; when the centers collide modulo integer translation, their
equal-sign charges merge and remain nonzero. -/
theorem hypertranscendentalOver_gammaReflectionRatioMero (a : ℂ) :
    HypertranscendentalOver (RatFunc ℂ) (gammaReflectionRatioMero a) := by
  rw [gammaReflectionRatioMero_eq_inv_oppositeShiftQuotient]
  exact HTGeometry.hypertranscendentalOver_inv_iff.mpr
    (hypertranscendentalOver_gammaOppositeShiftQuotientMero a a)

end

end GaloisForLFunctions
