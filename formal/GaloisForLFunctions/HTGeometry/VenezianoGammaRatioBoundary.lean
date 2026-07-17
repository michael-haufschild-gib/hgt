import GaloisForLFunctions.HTGeometry.MeromorphicGammaSuperselection

/-!
# Veneziano Gamma-ratio differential boundary

The Euler beta factor in the Veneziano/open-string four-point amplitude is, up to a nonzero
constant in one fixed channel, a translated Gamma ratio.  This module specializes the genuine
meromorphic Gamma-orbit theorem to that ratio.

The result is exact: the reduced amplitude is differentially algebraic precisely when the fixed
channel separation is an integer.  Otherwise it is hypertranscendental.  Thus the selector is the
translation-orbit relation seen by the scattering observable, not a temporal evolution law.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance venezianoGammaRatioDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance venezianoGammaRatioIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring Set.univ) := Ring.toIntAlgebra _

local instance venezianoGammaRatioIntAlgebraMero :
    Algebra ℤ (meroField Set.univ) := Ring.toIntAlgebra _

local instance venezianoGammaRatioIntAlgebraRatFunc :
    Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _

local instance venezianoGammaRatioDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance venezianoGammaRatioRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance venezianoGammaRatioRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance venezianoGammaRatioDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance venezianoGammaRatioCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- The variable-channel part of the Euler beta/Veneziano amplitude:
`Γ(z+a) / Γ(z+a+b)`.  The omitted factor `Γ(b)` is constant in `z`. -/
def reducedVenezianoAmplitudeMero (a b : ℂ) : meroField Set.univ :=
  gammaShiftMero a / gammaShiftMero (a + b)

/-- At a nonnegative integer channel separation, the reduced amplitude is the reciprocal of the
Pochhammer rational factor. -/
theorem reducedVenezianoAmplitudeMero_natShift (a : ℂ) (n : ℕ) :
    reducedVenezianoAmplitudeMero a (n : ℂ) =
      algebraMap (RatFunc ℂ) (meroField Set.univ) (gammaOrbitNatFactor a n)⁻¹ := by
  rw [reducedVenezianoAmplitudeMero, gammaShiftMero_add_nat]
  rw [map_inv₀]
  have hg : gammaShiftMero a ≠ 0 := gammaShiftMero_ne_zero a
  have hr : algebraMap (RatFunc ℂ) (meroField Set.univ) (gammaOrbitNatFactor a n) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective).mpr
      (gammaOrbitNatFactor_ne_zero a n)
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    gammaShiftMero a *
          ((gammaShiftMero a)⁻¹ *
          (algebraMap (RatFunc ℂ) (meroField Set.univ) (gammaOrbitNatFactor a n))⁻¹) =
        (gammaShiftMero a * (gammaShiftMero a)⁻¹) *
          (algebraMap (RatFunc ℂ) (meroField Set.univ) (gammaOrbitNatFactor a n))⁻¹ := by ring
    _ =
        (algebraMap (RatFunc ℂ) (meroField Set.univ) (gammaOrbitNatFactor a n))⁻¹ := by
          rw [mul_inv_cancel₀ hg, one_mul]
    _ = _ := rfl

/-- At a negative integer separation, the reduced amplitude is a Pochhammer rational factor. -/
theorem reducedVenezianoAmplitudeMero_negSuccShift (a : ℂ) (n : ℕ) :
    reducedVenezianoAmplitudeMero a (-((n + 1 : ℕ) : ℂ)) =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
        (gammaOrbitNatFactor (a - (n + 1 : ℕ)) (n + 1)) := by
  let b : ℂ := a - (n + 1 : ℕ)
  have hrec := gammaShiftMero_add_nat b (n + 1)
  have hba : b + ((n + 1 : ℕ) : ℂ) = a := by
    dsimp [b]
    ring
  rw [hba] at hrec
  rw [reducedVenezianoAmplitudeMero]
  have hab : a + -((n + 1 : ℕ) : ℂ) = b := by
    dsimp [b]
    ring
  rw [hab, hrec]
  have hg : gammaShiftMero b ≠ 0 := gammaShiftMero_ne_zero b
  change
    (algebraMap (RatFunc ℂ) (meroField Set.univ)
        (gammaOrbitNatFactor b (n + 1)) * gammaShiftMero b) /
      gammaShiftMero b = _
  field_simp [hg]
  simp [b]

/-- Every integer channel separation makes the reduced Veneziano amplitude differentially
algebraic over the rational function field. -/
theorem differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_of_integerShift
    (a b : ℂ) (hinteger : ∃ k : ℤ, b = (k : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ) (reducedVenezianoAmplitudeMero a b) := by
  obtain ⟨k, rfl⟩ := hinteger
  cases k with
  | ofNat n =>
      change DifferentialAlgebraicOver (RatFunc ℂ)
        (reducedVenezianoAmplitudeMero a (n : ℂ))
      rw [reducedVenezianoAmplitudeMero_natShift]
      exact HTGeometry.differentialAlgebraicOver_algebraMap
        ((gammaOrbitNatFactor a n)⁻¹)
  | negSucc n =>
      rw [Int.cast_negSucc, reducedVenezianoAmplitudeMero_negSuccShift]
      exact HTGeometry.differentialAlgebraicOver_algebraMap
        (gammaOrbitNatFactor (a - (n + 1 : ℕ)) (n + 1))

/-- A noninteger channel separation puts the two Gamma factors on distinct translation orbits,
so the reduced amplitude is hypertranscendental. -/
theorem hypertranscendentalOver_reducedVenezianoAmplitudeMero_of_nonintegerShift
    (a b : ℂ) (hnoninteger : ∀ k : ℤ, b ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ) (reducedVenezianoAmplitudeMero a b) := by
  let shifts : Fin 2 → ℂ := ![a, a + b]
  let charges : Fin 2 → ℤ := ![1, -1]
  have hproduct : HypertranscendentalOver (RatFunc ℂ)
      (gammaOrbitProductMero shifts charges) := by
    apply hypertranscendentalOver_gammaOrbitProductMero shifts charges 0
    · simp [charges]
    · intro c hc k
      fin_cases c
      · exact (hc rfl).elim
      · simpa [shifts] using hnoninteger k
  simpa [gammaOrbitProductMero, shifts, charges, reducedVenezianoAmplitudeMero,
    div_eq_mul_inv] using hproduct

/-- **Exact scattering boundary.**  The reduced Veneziano Gamma ratio is differentially
algebraic exactly at integer channel separation. -/
theorem differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
    (a b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (reducedVenezianoAmplitudeMero a b) ↔
      ∃ k : ℤ, b = (k : ℂ) := by
  constructor
  · intro hDA
    by_contra hnoninteger
    push Not at hnoninteger
    exact hypertranscendentalOver_reducedVenezianoAmplitudeMero_of_nonintegerShift
      a b hnoninteger hDA
  · exact differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_of_integerShift a b

/-- Hypertranscendence is the complementary noninteger channel sector. -/
theorem hypertranscendentalOver_reducedVenezianoAmplitudeMero_iff_nonintegerShift
    (a b : ℂ) :
    HypertranscendentalOver (RatFunc ℂ) (reducedVenezianoAmplitudeMero a b) ↔
      ∀ k : ℤ, b ≠ (k : ℂ) := by
  rw [HypertranscendentalOver,
    differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift]
  push Not
  rfl

end

end GaloisForLFunctions
