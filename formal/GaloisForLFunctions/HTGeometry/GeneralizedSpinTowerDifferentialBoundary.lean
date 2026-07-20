import GaloisForLFunctions.HTGeometry.VenezianoGammaRatioBoundary
import GaloisForLFunctions.HTGeometry.MeromorphicGammaReflection
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence

/-!
# Generalized finite-spin-tower differential boundary

A 2026 maximally supersymmetric gravitational-EFT construction introduces, in each channel, the
Gamma multiplier

`Gamma(1-z) Gamma(1+z+N) / (Gamma(1+z) Gamma(1-z+N))`.

Euler reflection reduces this multiplier to a nonzero differentially algebraic sine gauge times a
four-Gamma carrier.  The carrier has charge `-2` on the integer-translation orbit of `0`, while its
two numerator clocks lie on the orbits of `-N` and `N`.  Thus the multiplier is differentially
algebraic exactly when `N` is an integer and is hypertranscendental otherwise.  The proof allows the
two numerator orbits to collide with each other; only their separation from the charged central
orbit matters.

This is an unconditional differential-algebra classification of the exact per-channel formula.
Its use as a string-amplitude statement is external to Lean.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance generalizedSpinTowerDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance generalizedSpinTowerIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring Set.univ) := Ring.toIntAlgebra _

local instance generalizedSpinTowerIntAlgebraMero :
    Algebra ℤ (meroField Set.univ) := Ring.toIntAlgebra _

local instance generalizedSpinTowerIntAlgebraRatFunc :
    Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _

local instance generalizedSpinTowerDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance generalizedSpinTowerRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance generalizedSpinTowerRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance generalizedSpinTowerDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance generalizedSpinTowerCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- The exact variable-channel multiplier in the analytically continued generalized finite-spin
tower: `Gamma(1-z) Gamma(1+z+N) / (Gamma(1+z) Gamma(1-z+N))`. -/
def generalizedSpinTowerChannelMero (N : ℂ) : meroField Set.univ :=
  (gammaNegativeShiftMero 1 * gammaShiftMero (1 + N)) /
    (gammaShiftMero 1 * gammaNegativeShiftMero (1 + N))

/-- The sine quotient produced by reflecting the two negative-orientation Gamma clocks. -/
def generalizedSpinTowerReflectionGaugeMero (N : ℂ) : meroField Set.univ :=
  gammaReflectionGaugeMero 1 / gammaReflectionGaugeMero (1 + N)

/-- The positive-orientation four-Gamma carrier left after Euler reflection. -/
def generalizedSpinTowerGammaCarrierMero (N : ℂ) : meroField Set.univ :=
  (gammaShiftMero (-N) * gammaShiftMero (1 + N)) /
    (gammaShiftMero 0 * gammaShiftMero 1)

theorem generalizedSpinTowerReflectionGaugeMero_ne_zero (N : ℂ) :
    generalizedSpinTowerReflectionGaugeMero N ≠ 0 := by
  exact div_ne_zero (gammaReflectionGaugeMero_ne_zero 1)
    (gammaReflectionGaugeMero_ne_zero (1 + N))

theorem differentialAlgebraicOver_generalizedSpinTowerReflectionGaugeMero (N : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (generalizedSpinTowerReflectionGaugeMero N) := by
  exact HTGeometry.differentialAlgebraicOver_div
    (differentialAlgebraicOver_gammaReflectionGaugeMero 1)
    (differentialAlgebraicOver_gammaReflectionGaugeMero (1 + N))

/-- Euler reflection separates the physical multiplier into a nonzero DA gauge and its complete
Gamma-orbit carrier. -/
theorem generalizedSpinTowerChannelMero_eq_gauge_mul_carrier (N : ℂ) :
    generalizedSpinTowerChannelMero N =
      generalizedSpinTowerReflectionGaugeMero N *
        generalizedSpinTowerGammaCarrierMero N := by
  rw [generalizedSpinTowerChannelMero,
    generalizedSpinTowerReflectionGaugeMero,
    generalizedSpinTowerGammaCarrierMero,
    gammaNegativeShiftMero_reflection,
    gammaNegativeShiftMero_reflection]
  rw [show 1 - (1 : ℂ) = 0 by ring,
    show 1 - (1 + N) = -N by ring]
  field_simp [gammaShiftMero_ne_zero, gammaReflectionGaugeMero_ne_zero]

/-- The carrier is a product of two translated Veneziano ratios, one inverted. -/
theorem generalizedSpinTowerGammaCarrierMero_eq_veneziano (N : ℂ) :
    generalizedSpinTowerGammaCarrierMero N =
      reducedVenezianoAmplitudeMero (-N) N *
        (reducedVenezianoAmplitudeMero 1 N)⁻¹ := by
  rw [generalizedSpinTowerGammaCarrierMero, reducedVenezianoAmplitudeMero,
    reducedVenezianoAmplitudeMero]
  rw [show -N + N = 0 by ring]
  field_simp [gammaShiftMero_ne_zero]

/-- Integer tower length reduces both translated ratios to rational Pochhammer factors. -/
theorem differentiallyAlgebraicOver_generalizedSpinTowerGammaCarrierMero_of_integer
    (N : ℂ) (hinteger : ∃ k : ℤ, N = (k : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (generalizedSpinTowerGammaCarrierMero N) := by
  rw [generalizedSpinTowerGammaCarrierMero_eq_veneziano]
  exact HTGeometry.differentialAlgebraicOver_mul
    ((differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
      (-N) N).2 hinteger)
    (HTGeometry.differentialAlgebraicOver_inv
      ((differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
        1 N).2 hinteger))

/-- A noninteger tower parameter separates the charge `-2` central orbit from both numerator
orbits.  The numerator orbits may coincide with one another without weakening the obstruction. -/
theorem hypertranscendentalOver_generalizedSpinTowerGammaCarrierMero_of_noninteger
    (N : ℂ) (hnoninteger : ∀ k : ℤ, N ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (generalizedSpinTowerGammaCarrierMero N) := by
  let base : Fin 3 → ℂ := ![0, -N, N]
  let offsets : Fin 3 → Fin 2 → ℕ := ![![0, 1], ![0, 0], ![1, 0]]
  let charges : Fin 3 → Fin 2 → ℤ := ![![-1, -1], ![1, 0], ![1, 0]]
  have hproduct : HypertranscendentalOver (RatFunc ℂ)
      (gammaCommonScaleProductMero base offsets charges) := by
    apply hypertranscendentalOver_gammaCommonScaleProductMero_of_charge_ne_zero
      base offsets charges 0
    · norm_num [gammaCommonScaleOrbitCharge, charges]
    · intro c hc k
      fin_cases c
      · exact (hc rfl).elim
      · intro h
        apply hnoninteger (-k)
        push_cast
        simpa [base] using congrArg Neg.neg h
      · simpa [base] using hnoninteger k
  have hrefined : generalizedSpinTowerGammaCarrierMero N =
      gammaCommonScaleProductMero base offsets charges := by
    rw [generalizedSpinTowerGammaCarrierMero, gammaCommonScaleProductMero]
    norm_num [base, offsets, charges, div_eq_mul_inv, Fin.prod_univ_succ]
    ring_nf
  rw [hrefined]
  exact hproduct

theorem differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_of_integer
    (N : ℂ) (hinteger : ∃ k : ℤ, N = (k : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (generalizedSpinTowerChannelMero N) := by
  rw [generalizedSpinTowerChannelMero_eq_gauge_mul_carrier]
  exact HTGeometry.differentialAlgebraicOver_mul
    (differentialAlgebraicOver_generalizedSpinTowerReflectionGaugeMero N)
    (differentiallyAlgebraicOver_generalizedSpinTowerGammaCarrierMero_of_integer N hinteger)

theorem hypertranscendentalOver_generalizedSpinTowerChannelMero_of_noninteger
    (N : ℂ) (hnoninteger : ∀ k : ℤ, N ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (generalizedSpinTowerChannelMero N) := by
  rw [generalizedSpinTowerChannelMero_eq_gauge_mul_carrier]
  have hproduct : HypertranscendentalOver (RatFunc ℂ)
      (generalizedSpinTowerGammaCarrierMero N *
        generalizedSpinTowerReflectionGaugeMero N) :=
    (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_generalizedSpinTowerReflectionGaugeMero N)
      (generalizedSpinTowerReflectionGaugeMero_ne_zero N)).2
      (hypertranscendentalOver_generalizedSpinTowerGammaCarrierMero_of_noninteger
        N hnoninteger)
  simpa [mul_comm] using hproduct

/-- **Exact generalized-spin-tower differential boundary.**  The analytically continued channel
multiplier is DA exactly at integer tower parameter. -/
theorem differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_iff_integer
    (N : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (generalizedSpinTowerChannelMero N) ↔
      ∃ k : ℤ, N = (k : ℂ) := by
  constructor
  · intro hDA
    by_contra hnoninteger
    push Not at hnoninteger
    exact hypertranscendentalOver_generalizedSpinTowerChannelMero_of_noninteger
      N hnoninteger hDA
  · exact differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_of_integer N

/-- The complementary noninteger sector is exactly the HT sector. -/
theorem hypertranscendentalOver_generalizedSpinTowerChannelMero_iff_noninteger
    (N : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (generalizedSpinTowerChannelMero N) ↔
      ∀ k : ℤ, N ≠ (k : ℂ) := by
  rw [HypertranscendentalOver,
    differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_iff_integer]
  push Not
  rfl

end

end GaloisForLFunctions
