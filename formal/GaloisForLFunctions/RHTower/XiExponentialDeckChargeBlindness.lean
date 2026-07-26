import GaloisForLFunctions.RHTower.XiDeckChargeUnitGaugeClassifierUniversalityLaw
import GaloisForLFunctions.RHTower.XiHypertranscendenceUnconditional
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Explicit hypertranscendental unit for deck-charge blindness

The abstract deck-charge blindness theorem requires a function which is both nowhere zero and
hypertranscendental.  Completed Xi is unconditionally hypertranscendental, and its pointwise
exponential is an entire unit.  The existing upper-end realization of Xi and the exponential
logarithmic-derivative transfer prove that this explicit unit remains hypertranscendental.

Consequently the deck-charge tower provably assigns the same values to the differentially
algebraic constant `1` and the hypertranscendental function `exp(xi)`.  No witness hypothesis
remains in the resulting class-blindness and unit-gauge classifier theorems.
-/

namespace RHTower

open Complex Filter Function Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

open scoped UpperEndDifferentialInstances
open scoped UpperEndComplexTowerInstances

/-- A concrete entire unit obtained by exponentiating completed Xi. -/
def xiExponential (z : ℂ) : ℂ :=
  Complex.exp (xi z)

theorem xiExponential_analyticOnNhd_univ :
    AnalyticOnNhd ℂ xiExponential Set.univ :=
  xi_analyticOnNhd_univ.cexp

/-- Upper-end analytic realization of the rotated Xi exponential. -/
def xiExponentialRotatedUpperEndAnalytic : upperEndAnalyticSubring :=
  rotatedEntireUpperEndAnalytic
    xiExponential xiExponential_analyticOnNhd_univ (-I)

/-- Upper-end meromorphic realization of the rotated Xi exponential. -/
def xiExponentialRotatedUpperEndCarrier : upperEndMeroField :=
  rotatedEntireUpperEndMero
    xiExponential xiExponential_analyticOnNhd_univ (-I)

theorem upperEndAnalyticDeriv_xiExponentialRotatedUpperEndAnalytic :
    upperEndAnalyticDeriv xiExponentialRotatedUpperEndAnalytic =
      xiExponentialRotatedUpperEndAnalytic *
        upperEndAnalyticDeriv
          (rotatedEntireUpperEndAnalytic xi xi_analyticOnNhd_univ (-I)) := by
  apply Subtype.ext
  change upperEndGermDeriv
      ((fun z : ℂ ↦ Complex.exp (xi (-I * z))) : Germ upperEndFilter ℂ) =
    ((fun z : ℂ ↦ Complex.exp (xi (-I * z))) : Germ upperEndFilter ℂ) *
      upperEndGermDeriv
        ((fun z : ℂ ↦ xi (-I * z)) : Germ upperEndFilter ℂ)
  rw [upperEndGermDeriv_coe, upperEndGermDeriv_coe, ← Germ.coe_mul]
  apply Germ.coe_eq.mpr
  filter_upwards [] with z
  change deriv (fun w : ℂ ↦ Complex.exp (xi (-I * w))) z =
    Complex.exp (xi (-I * z)) * deriv (fun w : ℂ ↦ xi (-I * w)) z
  exact ((xi_analyticOnNhd_univ (-I * z) (Set.mem_univ _)).comp
    (analyticAt_const.mul analyticAt_id)).differentiableAt.hasDerivAt.cexp.deriv

theorem xiExponentialRotatedUpperEndAnalytic_ne_zero :
    xiExponentialRotatedUpperEndAnalytic ≠ 0 := by
  intro hzero
  have hgerm := congrArg Subtype.val hzero
  change ((fun z : ℂ ↦ Complex.exp (xi (-I * z))) : Germ upperEndFilter ℂ) = 0 at hgerm
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  change ∀ᶠ z in upperEndFilter, Complex.exp (xi (-I * z)) = 0 at hgerm
  rw [upperEndFilter_basis.eventually_iff] at hgerm
  obtain ⟨H, -, hH⟩ := hgerm
  let z : ℂ := ((H + 1 : ℝ) : ℂ) * I
  have hz : H < z.im := by simp [z]
  exact Complex.exp_ne_zero (xi (-I * z)) (hH hz)

theorem xiExponentialRotatedUpperEndCarrier_ne_zero :
    xiExponentialRotatedUpperEndCarrier ≠ 0 := by
  intro hzero
  apply xiExponentialRotatedUpperEndAnalytic_ne_zero
  apply IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
  simpa [xiExponentialRotatedUpperEndCarrier,
    rotatedEntireUpperEndMero] using hzero

/-- The concrete exponential phase has logarithmic derivative equal to that of its latent
rotated Xi clock. -/
theorem xiExponentialRotatedUpperEndCarrier_logDeriv :
    xiExponentialRotatedUpperEndCarrier′ /
        xiExponentialRotatedUpperEndCarrier =
      (rotatedEntireUpperEndMero xi xi_analyticOnNhd_univ (-I))′ := by
  have hphase :
      algebraMap upperEndAnalyticSubring upperEndMeroField
          xiExponentialRotatedUpperEndAnalytic ≠ 0 := by
    simpa [xiExponentialRotatedUpperEndCarrier,
      rotatedEntireUpperEndMero] using
        xiExponentialRotatedUpperEndCarrier_ne_zero
  change
    Differential.deriv
        (algebraMap upperEndAnalyticSubring upperEndMeroField
          xiExponentialRotatedUpperEndAnalytic) /
      algebraMap upperEndAnalyticSubring upperEndMeroField
        xiExponentialRotatedUpperEndAnalytic =
    Differential.deriv
      (algebraMap upperEndAnalyticSubring upperEndMeroField
        (rotatedEntireUpperEndAnalytic xi xi_analyticOnNhd_univ (-I)))
  rw [upperEndMeroFieldDifferential_algebraMap,
    upperEndMeroFieldDifferential_algebraMap,
    upperEndAnalyticDeriv_xiExponentialRotatedUpperEndAnalytic, map_mul]
  field_simp [hphase]

/-- Exponentiating Xi leaves an unconditional hypertranscendental unit at the upper end. -/
theorem xiExponentialRotatedUpperEndCarrier_hypertranscendentalOver :
    HypertranscendentalOver upperEndRationalCoordinateField
      xiExponentialRotatedUpperEndCarrier := by
  have hsource : HypertranscendentalOver upperEndRationalCoordinateField
      (rotatedEntireUpperEndMero xi xi_analyticOnNhd_univ (-I)) := by
    rw [← xiRotatedUpperEndCarrier_eq_rotatedEntireUpperEndMero]
    exact xiRotatedUpperEndCarrier_hypertranscendentalOver
  exact hypertranscendentalOver_phase_of_logDeriv_eq_deriv hsource
    xiExponentialRotatedUpperEndCarrier_logDeriv

theorem xiExponentialRotatedUpperEndCarrier_hypertranscendentalOver_ratFunc :
    letI : Algebra (RatFunc ℂ) upperEndRationalCoordinateField :=
      upperEndRatfuncToRationalCoordinateField.toAlgebra
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    HypertranscendentalOver (RatFunc ℂ)
      xiExponentialRotatedUpperEndCarrier := by
  letI : Algebra (RatFunc ℂ) upperEndRationalCoordinateField :=
    upperEndRatfuncToRationalCoordinateField.toAlgebra
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI : IsScalarTower (RatFunc ℂ) upperEndRationalCoordinateField upperEndMeroField :=
    .of_algebraMap_eq fun _ ↦ rfl
  have h := xiExponentialRotatedUpperEndCarrier_hypertranscendentalOver
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton] at h ⊢
  exact DifferentialIndependent.restrictScalars
    (F := RatFunc ℂ)
    (K := upperEndRationalCoordinateField)
    (E := upperEndMeroField)
    h

/-- The explicit entire unit `exp(xi)` is globally hypertranscendental. -/
theorem xiExponential_hypertranscendental :
    Hypertranscendental xiExponential := by
  apply hypertranscendental_of_rotatedEntireUpperEnd_hypertranscendentalOver
    xiExponential_analyticOnNhd_univ (neg_ne_zero.mpr I_ne_zero)
  exact xiExponentialRotatedUpperEndCarrier_hypertranscendentalOver_ratFunc

theorem xiExponential_ne_zero (z : ℂ) :
    xiExponential z ≠ 0 :=
  Complex.exp_ne_zero _

/-- Unconditional class-blindness witness for the deck-charge tower. -/
theorem xiExponential_deckCharge_classBlindness :
    DifferentiallyAlgebraic (fun _ : ℂ => (1 : ℂ)) ∧
      Hypertranscendental xiExponential ∧
      ∀ k ρ, deckCharge xiExponential k ρ =
        deckCharge (fun _ : ℂ => (1 : ℂ)) k ρ :=
  deckCharge_blind_to_class xiExponential xiExponential_ne_zero
    xiExponential_hypertranscendental

/-- The Xi deck-charge classifier and its failure to detect differential class now require no
abstract hypertranscendental witness. -/
theorem xiDeckCharge_unitGaugeRHClassifier_and_xiExponentialBlindness
    (u : ℂ → ℂ)
    (hu : ∀ ρ ∈ rightHalf, AnalyticAt ℂ u ρ)
    (hu0 : ∀ ρ ∈ rightHalf, u ρ ≠ 0) :
    (RiemannHypothesis ↔
      ∀ k, ∀ ρ ∈ rightHalf, (xi * u) ρ = 0 →
        deckCharge (xi * u) k ρ = 1) ∧
      DifferentiallyAlgebraic (fun _ : ℂ => (1 : ℂ)) ∧
      Hypertranscendental xiExponential ∧
      ∀ k ρ, deckCharge xiExponential k ρ =
        deckCharge (fun _ : ℂ => (1 : ℂ)) k ρ :=
  xiDeckCharge_unitGaugeRHClassifier_and_classBlindness
    u hu hu0 xiExponential xiExponential_ne_zero
      xiExponential_hypertranscendental

end

end RHTower
