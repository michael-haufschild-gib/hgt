import GaloisForLFunctions.HTGeometry.MeromorphicGammaNatScale
import GaloisForLFunctions.HTGeometry.VenezianoGammaRatioBoundary
import GaloisForLFunctions.HTGeometry.WignerSmithLogClockObservability

/-!
# Sauter Bogoliubov Gamma boundary

For the scalar Sauter pulse, equation (62) of S. P. Kim, H. K. Lee, and Y. Yoon,
*Effective Action of QED in Electric Field Backgrounds*, arXiv:0807.2696, gives the exact
in/out Bogoliubov coefficient as a quotient of four Gamma values.  If the incoming-frequency
parameter is written as `z = -i*tau*omega_in/2`, its nonconstant Gamma carrier has the form

`Gamma(2*z+1) / (Gamma(z+a) * Gamma(z+b))`.

The factors omitted from this carrier are independent of `z`; the paper separately removes the
dynamical phase before forming the observable effective action.  Thus this is a differential
boundary in the observable spectral parameter, not a statement about temporal propagation.

Gauss duplication refines the numerator into the two translation orbits represented by `1/2`
and `1`.  The carrier is differentially algebraic exactly when the denominator orbits match those
two numerator orbits, in either order.  Everywhere else it is hypertranscendental.  This exact
mixed-scale classification is reusable for any hypergeometric connection coefficient with the
same `2:1:1` Gamma-scale pattern.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance sauterBogoliubovGammaDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance sauterBogoliubovGammaComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance sauterBogoliubovGammaComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance sauterBogoliubovGammaDifferential :
    Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance sauterBogoliubovGammaRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance sauterBogoliubovGammaRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance sauterBogoliubovGammaDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance sauterBogoliubovGammaCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- The `2:1:1` Gamma carrier of the scalar Sauter in/out connection coefficient, viewed in the
incoming-frequency spectral parameter. -/
def sauterBogoliubovGammaCarrierMero (a b : ℂ) : meroField Set.univ :=
  gammaNatScaleMero 2 1 / (gammaShiftMero a * gammaShiftMero b)

theorem sauterBogoliubovGammaCarrierMero_ne_zero (a b : ℂ) :
    sauterBogoliubovGammaCarrierMero a b ≠ 0 := by
  exact div_ne_zero
    (gammaNatScaleMero_ne_zero (show 0 < 2 by norm_num) 1)
    (mul_ne_zero (gammaShiftMero_ne_zero a) (gammaShiftMero_ne_zero b))

/-- The two unit-scale Gamma ratios left after Gauss duplication of the Sauter carrier. -/
def sauterBogoliubovRefinedMero (a b : ℂ) : meroField Set.univ :=
  reducedVenezianoAmplitudeMero (1 / 2) (a - 1 / 2) *
    reducedVenezianoAmplitudeMero 1 (b - 1)

/-- **Exact `2:1:1` normal form.**  Gauss duplication is a nonzero DA gauge times two translated
Gamma ratios. -/
theorem sauterBogoliubovGammaCarrierMero_normalForm (a b : ℂ) :
    sauterBogoliubovGammaCarrierMero a b =
      gammaNatScaleGaussGaugeMero 2 1 * sauterBogoliubovRefinedMero a b := by
  rw [sauterBogoliubovGammaCarrierMero,
    gammaNatScaleMero_gauss (show 0 < 2 by norm_num) (1 : ℂ)]
  have hprod : gammaNatScaleGaussProductMero 2 1 =
      gammaShiftMero (1 / 2) * gammaShiftMero 1 := by
    norm_num [gammaNatScaleGaussProductMero, Finset.prod_range_succ]
  change
    (gammaNatScaleGaussGaugeMero 2 1 * gammaNatScaleGaussProductMero 2 1) /
        (gammaShiftMero a * gammaShiftMero b) =
      gammaNatScaleGaussGaugeMero 2 1 * sauterBogoliubovRefinedMero a b
  rw [hprod, sauterBogoliubovRefinedMero]
  simp only [reducedVenezianoAmplitudeMero]
  norm_num
  field_simp [gammaShiftMero_ne_zero a, gammaShiftMero_ne_zero b]

theorem sauterBogoliubovGammaCarrierMero_comm (a b : ℂ) :
    sauterBogoliubovGammaCarrierMero a b =
      sauterBogoliubovGammaCarrierMero b a := by
  rw [sauterBogoliubovGammaCarrierMero, sauterBogoliubovGammaCarrierMero]
  ring

/-- Matching the denominator shifts to the half- and unit-shift numerator orbits makes the exact
Sauter carrier differentially algebraic. -/
theorem differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_of_directMatching
    (a b : ℂ) (ha : ∃ m : ℤ, a - 1 / 2 = (m : ℂ))
    (hb : ∃ n : ℤ, b - 1 = (n : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (sauterBogoliubovGammaCarrierMero a b) := by
  rw [sauterBogoliubovGammaCarrierMero_normalForm]
  exact HTGeometry.differentialAlgebraicOver_mul
    (differentialAlgebraicOver_gammaNatScaleGaussGaugeMero 2 1)
    (HTGeometry.differentialAlgebraicOver_mul
      ((differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
        (1 / 2) (a - 1 / 2)).2 ha)
      ((differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
        1 (b - 1)).2 hb))

/-- The same DA matching law holds with the two denominator orbits exchanged. -/
theorem differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_of_crossMatching
    (a b : ℂ) (ha : ∃ m : ℤ, a - 1 = (m : ℂ))
    (hb : ∃ n : ℤ, b - 1 / 2 = (n : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (sauterBogoliubovGammaCarrierMero a b) := by
  rw [sauterBogoliubovGammaCarrierMero_comm]
  exact differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_of_directMatching
    b a hb ha

/-- If neither denominator factor occupies the half-shift orbit, that uncancelled numerator orbit
forces hypertranscendence. -/
theorem hypertranscendentalOver_sauterBogoliubovGammaCarrierMero_of_half_unmatched
    (a b : ℂ)
    (ha : ∀ m : ℤ, a - 1 / 2 ≠ (m : ℂ))
    (hb : ∀ n : ℤ, b - 1 / 2 ≠ (n : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (sauterBogoliubovGammaCarrierMero a b) := by
  let shifts : Fin 4 → ℂ := ![(1 / 2 : ℂ), 1, a, b]
  let charges : Fin 4 → ℤ := ![1, 1, -1, -1]
  let c0 : Fin 4 := 0
  have horbit : HypertranscendentalOver (RatFunc ℂ)
      (gammaOrbitProductMero shifts charges) := by
    apply hypertranscendentalOver_gammaOrbitProductMero shifts charges c0
    · norm_num [charges, c0]
    · intro c hc n
      fin_cases c
      · exact (hc rfl).elim
      · intro h
        have htwo := congrArg (fun z : ℂ => 2 * z) h
        norm_num [shifts, c0] at htwo
        have htwoZ : (1 : ℤ) = 2 * n := by exact_mod_cast htwo
        omega
      · simpa [shifts, c0] using ha n
      · simpa [shifts, c0] using hb n
  have hrefined : sauterBogoliubovRefinedMero a b =
      gammaOrbitProductMero shifts charges := by
    rw [sauterBogoliubovRefinedMero, gammaOrbitProductMero]
    simp only [reducedVenezianoAmplitudeMero]
    norm_num [shifts, charges, div_eq_mul_inv, Fin.prod_univ_succ]
    ring
  rw [sauterBogoliubovGammaCarrierMero_normalForm, hrefined, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_gammaNatScaleGaussGaugeMero 2 1)
    (gammaNatScaleGaussGaugeMero_ne_zero (show 0 < 2 by norm_num) 1)).2 horbit

/-- If neither denominator factor occupies the unit-shift orbit, that uncancelled numerator orbit
forces hypertranscendence. -/
theorem hypertranscendentalOver_sauterBogoliubovGammaCarrierMero_of_one_unmatched
    (a b : ℂ)
    (ha : ∀ m : ℤ, a - 1 ≠ (m : ℂ))
    (hb : ∀ n : ℤ, b - 1 ≠ (n : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (sauterBogoliubovGammaCarrierMero a b) := by
  let shifts : Fin 4 → ℂ := ![(1 / 2 : ℂ), 1, a, b]
  let charges : Fin 4 → ℤ := ![1, 1, -1, -1]
  let c0 : Fin 4 := 1
  have horbit : HypertranscendentalOver (RatFunc ℂ)
      (gammaOrbitProductMero shifts charges) := by
    apply hypertranscendentalOver_gammaOrbitProductMero shifts charges c0
    · norm_num [charges, c0]
    · intro c hc n
      fin_cases c
      · intro h
        have htwo := congrArg (fun z : ℂ => 2 * z) h
        norm_num [shifts, c0] at htwo
        have htwoZ : (-1 : ℤ) = 2 * n := by exact_mod_cast htwo
        omega
      · exact (hc rfl).elim
      · simpa [shifts, c0] using ha n
      · simpa [shifts, c0] using hb n
  have hrefined : sauterBogoliubovRefinedMero a b =
      gammaOrbitProductMero shifts charges := by
    rw [sauterBogoliubovRefinedMero, gammaOrbitProductMero]
    simp only [reducedVenezianoAmplitudeMero]
    norm_num [shifts, charges, div_eq_mul_inv, Fin.prod_univ_succ]
    ring
  rw [sauterBogoliubovGammaCarrierMero_normalForm, hrefined, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_gammaNatScaleGaussGaugeMero 2 1)
    (gammaNatScaleGaussGaugeMero_ne_zero (show 0 < 2 by norm_num) 1)).2 horbit

/-- A shift cannot simultaneously occupy the half- and unit-shift translation orbits. -/
theorem not_halfShift_and_oneShift_integerSeparated (a : ℂ) :
    ¬ ((∃ m : ℤ, a - 1 / 2 = (m : ℂ)) ∧
      ∃ n : ℤ, a - 1 = (n : ℂ)) := by
  rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  have hhalf : (1 / 2 : ℂ) = ((m - n : ℤ) : ℂ) := by
    push_cast
    linear_combination hm - hn
  have htwo := congrArg (fun z : ℂ => 2 * z) hhalf
  norm_num at htwo
  have htwoZ : (1 : ℤ) = 2 * (m - n) := by exact_mod_cast htwo
  omega

/-- **Exact Sauter/hypergeometric connection boundary.**  The carrier is DA precisely when the
two denominator translation orbits are the half- and unit-shift numerator orbits, in either
order. -/
theorem differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_iff_orbitMatching
    (a b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (sauterBogoliubovGammaCarrierMero a b) ↔
      (((∃ m : ℤ, a - 1 / 2 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 = (n : ℂ)) ∨
        ((∃ m : ℤ, a - 1 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 / 2 = (n : ℂ))) := by
  constructor
  · intro hDA
    by_contra hmatching
    by_cases haHalf : ∃ m : ℤ, a - 1 / 2 = (m : ℂ)
    · have haOne : ∀ m : ℤ, a - 1 ≠ (m : ℂ) := fun m hm =>
        not_halfShift_and_oneShift_integerSeparated a ⟨haHalf, ⟨m, hm⟩⟩
      have hbOne : ∀ n : ℤ, b - 1 ≠ (n : ℂ) := fun n hn =>
        hmatching (Or.inl ⟨haHalf, ⟨n, hn⟩⟩)
      exact (hypertranscendentalOver_sauterBogoliubovGammaCarrierMero_of_one_unmatched
        a b haOne hbOne) hDA
    · have haHalf' : ∀ m : ℤ, a - 1 / 2 ≠ (m : ℂ) := fun m hm =>
        haHalf ⟨m, hm⟩
      by_cases hbHalf : ∃ n : ℤ, b - 1 / 2 = (n : ℂ)
      · have haOne : ∀ m : ℤ, a - 1 ≠ (m : ℂ) := fun m hm =>
          hmatching (Or.inr ⟨⟨m, hm⟩, hbHalf⟩)
        have hbOne : ∀ n : ℤ, b - 1 ≠ (n : ℂ) := fun n hn =>
          not_halfShift_and_oneShift_integerSeparated b ⟨hbHalf, ⟨n, hn⟩⟩
        exact (hypertranscendentalOver_sauterBogoliubovGammaCarrierMero_of_one_unmatched
          a b haOne hbOne) hDA
      · have hbHalf' : ∀ n : ℤ, b - 1 / 2 ≠ (n : ℂ) := fun n hn =>
          hbHalf ⟨n, hn⟩
        exact (hypertranscendentalOver_sauterBogoliubovGammaCarrierMero_of_half_unmatched
          a b haHalf' hbHalf') hDA
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_of_directMatching
        a b ha hb
    · exact differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_of_crossMatching
        a b ha hb

/-- Hypertranscendence is exactly the failure of the two possible orbit matchings. -/
theorem hypertranscendentalOver_sauterBogoliubovGammaCarrierMero_iff_orbitMismatch
    (a b : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (sauterBogoliubovGammaCarrierMero a b) ↔
      ¬ ((((∃ m : ℤ, a - 1 / 2 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 = (n : ℂ)) ∨
        ((∃ m : ℤ, a - 1 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 / 2 = (n : ℂ)))) := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_iff_orbitMatching]

/-- An arbitrary elementary exponential phase/readout gauge leaves the exact orbit boundary
unchanged. -/
def sauterBogoliubovReadoutMero (a b lambda : ℂ) : meroField Set.univ :=
  sauterBogoliubovGammaCarrierMero a b * physicalExponentialMero lambda

/-- Wigner--Smith/logarithmic current of the bare Sauter Gamma carrier. -/
def sauterBogoliubovGammaWignerSmithLogClockMero
    (a b : ℂ) : meroField Set.univ :=
  HTGeometry.wignerSmithLogClock (sauterBogoliubovGammaCarrierMero a b)

/-- Wigner--Smith/logarithmic current after restoring the elementary phase readout. -/
def sauterBogoliubovReadoutWignerSmithLogClockMero
    (a b lambda : ℂ) : meroField Set.univ :=
  HTGeometry.wignerSmithLogClock (sauterBogoliubovReadoutMero a b lambda)

/-- **Sauter delay gauge law.**  Restoring the dynamical exponential phase shifts the observable
logarithmic delay by exactly the constant `lambda`. -/
theorem sauterBogoliubovReadoutWignerSmithLogClockMero_eq_carrier_add_const
    (a b lambda : ℂ) :
    sauterBogoliubovReadoutWignerSmithLogClockMero a b lambda =
      sauterBogoliubovGammaWignerSmithLogClockMero a b +
        algebraMap ℂ (meroField Set.univ) lambda := by
  unfold sauterBogoliubovReadoutWignerSmithLogClockMero
    sauterBogoliubovGammaWignerSmithLogClockMero HTGeometry.wignerSmithLogClock
    sauterBogoliubovReadoutMero
  rw [Differential.logDeriv_mul]
  · congr 1
    unfold Differential.logDeriv
    rw [physicalExponentialMero_deriv]
    field_simp [physicalExponentialMero_ne_zero lambda]
  · exact sauterBogoliubovGammaCarrierMero_ne_zero a b
  · exact physicalExponentialMero_ne_zero lambda

theorem differentialAlgebraicOver_sauterBogoliubovReadoutMero_iff_orbitMatching
    (a b lambda : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (sauterBogoliubovReadoutMero a b lambda) ↔
      (((∃ m : ℤ, a - 1 / 2 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 = (n : ℂ)) ∨
        ((∃ m : ℤ, a - 1 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 / 2 = (n : ℂ))) := by
  rw [sauterBogoliubovReadoutMero]
  constructor
  · intro hreadout
    have hdiv := HTGeometry.differentialAlgebraicOver_div hreadout
      (differentialAlgebraicOver_physicalExponentialMero lambda)
    have heq :
        (sauterBogoliubovGammaCarrierMero a b * physicalExponentialMero lambda) /
            physicalExponentialMero lambda =
          sauterBogoliubovGammaCarrierMero a b := by
      field_simp [physicalExponentialMero_ne_zero lambda]
    rw [heq] at hdiv
    exact (differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_iff_orbitMatching
      a b).1 hdiv
  · intro hmatching
    exact HTGeometry.differentialAlgebraicOver_mul
      ((differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_iff_orbitMatching
        a b).2 hmatching)
      (differentialAlgebraicOver_physicalExponentialMero lambda)

/-- The elementary phase/readout gauge preserves the complementary HT sector as well. -/
theorem hypertranscendentalOver_sauterBogoliubovReadoutMero_iff_orbitMismatch
    (a b lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (sauterBogoliubovReadoutMero a b lambda) ↔
      ¬ ((((∃ m : ℤ, a - 1 / 2 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 = (n : ℂ)) ∨
        ((∃ m : ℤ, a - 1 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 / 2 = (n : ℂ)))) := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_sauterBogoliubovReadoutMero_iff_orbitMatching]

/-- The standard logarithmic delay reports exactly the same HT/DA orbit boundary as the complete
Sauter connection coefficient, including its elementary phase calibration. -/
theorem hypertranscendentalOver_sauterBogoliubovReadoutWignerSmithLogClockMero_iff_orbitMismatch
    (a b lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (sauterBogoliubovReadoutWignerSmithLogClockMero a b lambda) ↔
      ¬ ((((∃ m : ℤ, a - 1 / 2 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 = (n : ℂ)) ∨
        ((∃ m : ℤ, a - 1 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 / 2 = (n : ℂ)))) := by
  rw [sauterBogoliubovReadoutWignerSmithLogClockMero,
    HTGeometry.hypertranscendentalOver_wignerSmithLogClock_iff,
    hypertranscendentalOver_sauterBogoliubovReadoutMero_iff_orbitMismatch]

/-- **Positive source extraction for strong-field readout circuits.**  Off the two exceptional
orbit matchings, any finite differential circuit with rational-function scalars that exactly
realizes the Sauter readout must already contain an HT non-scalar atom. -/
theorem exists_hypertranscendental_atom_of_sauterBogoliubovReadoutCircuit
    (a b lambda : ℂ)
    (hmismatch : ¬ ((((∃ m : ℤ, a - 1 / 2 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 = (n : ℂ)) ∨
        ((∃ m : ℤ, a - 1 = (m : ℂ)) ∧
          ∃ n : ℤ, b - 1 / 2 = (n : ℂ)))))
    {Atom : meroField Set.univ → Prop}
    (hcircuit : HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ) Atom)
      (sauterBogoliubovReadoutMero a b lambda)) :
    ∃ x : meroField Set.univ,
      Atom x ∧ HypertranscendentalOver (RatFunc ℂ) x :=
  HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
    ((hypertranscendentalOver_sauterBogoliubovReadoutMero_iff_orbitMismatch
      a b lambda).2 hmismatch) hcircuit

end

end GaloisForLFunctions
