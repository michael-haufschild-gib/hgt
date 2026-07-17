import GaloisForLFunctions.HTGeometry.MeromorphicGammaReflection
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.GammaSameSignProductBoundary

/-!
# Gamma orientation-quotient boundary

Euler reflection turns a positive-orientation Gamma clock divided by a negative-orientation one
into a nonzero DA sine gauge times two positive-orientation Gamma clocks.  Equal-sign charges
cannot cancel: separated shifts give two charge-one orbits and integer-related shifts merge into
one charge-two orbit.  This module proves the resulting unconditional HT parent law independently
of any particular physical application.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance gammaOrientationQuotientDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance gammaOrientationQuotientDifferential :
    Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance gammaOrientationQuotientRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance gammaOrientationQuotientRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance gammaOrientationQuotientDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance gammaOrientationQuotientCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- A pair of positive-orientation shifted Gamma clocks. -/
def gammaPositiveShiftPairMero (a c : ℂ) : meroField Set.univ :=
  gammaShiftMero a * gammaShiftMero c

/-- Two shifts on distinct integer-translation orbits give two surviving charge-one sectors. -/
theorem hypertranscendentalOver_gammaPositiveShiftPairMero_of_nonintegerSeparation
    (a c : ℂ) (hsep : ∀ k : ℤ, c - a ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ) (gammaPositiveShiftPairMero a c) := by
  let shifts : Fin 2 → ℂ := ![a, c]
  let charges : Fin 2 → ℤ := ![1, 1]
  have hproduct : HypertranscendentalOver (RatFunc ℂ)
      (gammaOrbitProductMero shifts charges) := by
    apply hypertranscendentalOver_gammaOrbitProductMero shifts charges 0
    · simp [charges]
    · intro i hi k
      fin_cases i
      · exact (hi rfl).elim
      · simpa [shifts] using hsep k
  simpa [gammaPositiveShiftPairMero, gammaOrbitProductMero, shifts, charges] using hproduct

/-- Integer-separated positive shifts merge into one orbit of total charge two, so collision
strengthens rather than removes the HT obstruction. -/
theorem hypertranscendentalOver_gammaPositiveShiftPairMero_of_integerSeparation
    (a c : ℂ) (hinteger : ∃ k : ℤ, c - a = (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ) (gammaPositiveShiftPairMero a c) := by
  obtain ⟨k, hk⟩ := hinteger
  cases k with
  | ofNat n =>
      let base : Fin 1 → ℂ := fun _ => a
      let offsets : Fin 1 → Fin 2 → ℕ := fun _ => ![0, n]
      let charges : Fin 1 → Fin 2 → ℤ := fun _ => ![1, 1]
      have hcommon : HypertranscendentalOver (RatFunc ℂ)
          (gammaCommonScaleProductMero base offsets charges) := by
        exact (hypertranscendentalOver_gammaCommonScaleProductMero_iff_exists_charge_ne_zero
          base offsets charges
          (fun i j hij => (hij (Subsingleton.elim i j)).elim)).2
          (by
            refine ⟨0, ?_⟩
            norm_num [gammaCommonScaleOrbitCharge, charges])
      have hc : c = a + (n : ℂ) := by
        norm_num at hk
        linear_combination hk
      simpa [gammaPositiveShiftPairMero, gammaCommonScaleProductMero,
        base, offsets, charges, hc] using hcommon
  | negSucc n =>
      let base : Fin 1 → ℂ := fun _ => c
      let offsets : Fin 1 → Fin 2 → ℕ := fun _ => ![n + 1, 0]
      let charges : Fin 1 → Fin 2 → ℤ := fun _ => ![1, 1]
      have hcommon : HypertranscendentalOver (RatFunc ℂ)
          (gammaCommonScaleProductMero base offsets charges) := by
        exact (hypertranscendentalOver_gammaCommonScaleProductMero_iff_exists_charge_ne_zero
          base offsets charges
          (fun i j hij => (hij (Subsingleton.elim i j)).elim)).2
          (by
            refine ⟨0, ?_⟩
            norm_num [gammaCommonScaleOrbitCharge, charges])
      rw [Int.cast_negSucc] at hk
      have ha : a = c + ((n + 1 : ℕ) : ℂ) := by
        have hncast : (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + 1 := by
          push_cast
          ring
        rw [hncast] at hk ⊢
        linear_combination -hk
      simpa [gammaPositiveShiftPairMero, gammaCommonScaleProductMero,
        base, offsets, charges, ha] using hcommon

/-- **Same-orientation pair theorem.**  Every product of two shifted Gamma clocks is HT, whether
the shifts occupy distinct translation orbits or collide on one orbit. -/
theorem hypertranscendentalOver_gammaPositiveShiftPairMero (a c : ℂ) :
    HypertranscendentalOver (RatFunc ℂ) (gammaPositiveShiftPairMero a c) := by
  let shifts : Fin 2 → ℂ := ![a, c]
  let charges : Fin 2 → ℤ := ![1, 1]
  have hproduct : HypertranscendentalOver (RatFunc ℂ)
      (gammaFintypeOrbitProductMero shifts charges) :=
    hypertranscendentalOver_gammaFintypeOrbitProductMero_of_pos
      shifts charges (by simp [charges])
  simpa [gammaPositiveShiftPairMero, gammaFintypeOrbitProductMero,
    shifts, charges] using hproduct

/-- A positive-orientation Gamma clock divided by a negative-orientation one. -/
def gammaOppositeShiftQuotientMero (a b : ℂ) : meroField Set.univ :=
  gammaShiftMero a / gammaNegativeShiftMero b

/-- Euler reflection converts the quotient into a nonzero DA inverse-sine gauge times two
positive-orientation Gamma clocks. -/
theorem gammaOppositeShiftQuotientMero_reflectionNormalForm (a b : ℂ) :
    gammaOppositeShiftQuotientMero a b =
      (gammaReflectionGaugeMero b)⁻¹ *
        gammaPositiveShiftPairMero a (1 - b) := by
  rw [gammaOppositeShiftQuotientMero, gammaNegativeShiftMero_reflection,
    gammaPositiveShiftPairMero]
  field_simp [gammaReflectionGaugeMero_ne_zero b,
    gammaShiftMero_ne_zero (1 - b)]

/-- **Opposite-orientation quotient boundary.**  The quotient is unconditionally HT: reflection
makes both Gamma charges have the same sign. -/
theorem hypertranscendentalOver_gammaOppositeShiftQuotientMero (a b : ℂ) :
    HypertranscendentalOver (RatFunc ℂ) (gammaOppositeShiftQuotientMero a b) := by
  rw [gammaOppositeShiftQuotientMero_reflectionNormalForm, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (HTGeometry.differentialAlgebraicOver_inv
      (differentialAlgebraicOver_gammaReflectionGaugeMero b))
    (inv_ne_zero (gammaReflectionGaugeMero_ne_zero b))).2
      (hypertranscendentalOver_gammaPositiveShiftPairMero a (1 - b))

end

end GaloisForLFunctions
