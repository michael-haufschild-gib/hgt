import GaloisForLFunctions.HTGeometry.GeneralizedSpinTowerDifferentialBoundary
import GaloisForLFunctions.HTGeometry.VirasoroShapiroDifferentialBoundary
import GaloisForLFunctions.HTGeometry.GammaOppositeShiftBoundary
import GaloisForLFunctions.HTGeometry.KerrNewmanChargedScalarGammaBoundary
import GaloisForLFunctions.HTGeometry.SauterBogoliubovGammaBoundary
import GaloisForLFunctions.HTGeometry.ThermalCFTWignerSmithObservability

/-!
# Integer-orbit multiphysics phase-atlas universality

Terminal exact boundary theorems for generalized spin, open and closed strings, opposite-shift
scattering, Kerr--Newman response, Sauter connection coefficients, and thermal-CFT response expose
the same integer-translation selector after literal affine changes of coordinates.  This module
assembles their DA and HT phases into one twelve-observable certificate and proves that mixed
phases are impossible.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance gammaIntegerOrbitAtlasDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance gammaIntegerOrbitAtlasDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance gammaIntegerOrbitAtlasRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance gammaIntegerOrbitAtlasRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance gammaIntegerOrbitAtlasDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance gammaIntegerOrbitAtlasCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- The Kerr--Newman logarithmic clock has the same exact DA boundary as its Gamma response. -/
theorem differentialAlgebraicOver_kerrNewmanChargedScalarLogResponseClockMero_iff_integerGap
    (gap : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (kerrNewmanChargedScalarLogResponseClockMero gap) ↔
      ∃ k : ℤ, gap = (k : ℂ) := by
  constructor
  · intro hclock
    by_contra hgap
    have hnoninteger : ∀ k : ℤ, gap ≠ (k : ℂ) := by
      simpa only [not_exists] using hgap
    exact
      ((hypertranscendentalOver_kerrNewmanChargedScalarLogResponseClockMero_iff_nonintegerGap
        gap).2 hnoninteger) hclock
  · intro hgap
    unfold kerrNewmanChargedScalarLogResponseClockMero HTGeometry.wignerSmithLogClock
    unfold Differential.logDeriv
    exact differentialAlgebraicOver_deriv_div_self
      ((differentialAlgebraicOver_kerrNewmanChargedScalarGammaResponseMero_iff_integerGap
        gap).2 hgap)

private theorem sauterBogoliubov_affineSlice_orbitMatching_iff_integer
    (delta : ℂ) :
    (((∃ m : ℤ, (delta + 1 / 2) - 1 / 2 = (m : ℂ)) ∧
        ∃ n : ℤ, (1 : ℂ) - 1 = (n : ℂ)) ∨
      ((∃ m : ℤ, (delta + 1 / 2) - 1 = (m : ℂ)) ∧
        ∃ n : ℤ, (1 : ℂ) - 1 / 2 = (n : ℂ))) ↔
      ∃ k : ℤ, delta = (k : ℂ) := by
  have hdirect : (delta + 1 / 2) - 1 / 2 = delta := by ring
  have hone : ∃ n : ℤ, (1 : ℂ) - 1 = (n : ℂ) := ⟨0, by norm_num⟩
  have hcross : ¬ ∃ n : ℤ, (1 : ℂ) - 1 / 2 = (n : ℂ) := by
    intro hhalf
    exact not_halfShift_and_oneShift_integerSeparated (1 : ℂ) ⟨hhalf, hone⟩
  constructor
  · rintro (⟨hdelta, _⟩ | ⟨_, hhalf⟩)
    · simpa only [hdirect] using hdelta
    · exact (hcross hhalf).elim
  · intro hdelta
    exact Or.inl ⟨by simpa only [hdirect] using hdelta, hone⟩

/-- On the affine Sauter slice `(a,b) = (delta+1/2,1)`, the generic two-orbit matching boundary
pulls back to the single integer selector `delta`. -/
theorem differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_affineSlice_iff_integer
    (delta : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (sauterBogoliubovGammaCarrierMero (delta + 1 / 2) 1) ↔
      ∃ k : ℤ, delta = (k : ℂ) := by
  rw [differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_iff_orbitMatching,
    sauterBogoliubov_affineSlice_orbitMatching_iff_integer]

/-- The exponential Sauter readout preserves the exact affine-slice integer boundary. -/
theorem differentialAlgebraicOver_sauterBogoliubovReadoutMero_affineSlice_iff_integer
    (delta lambda : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (sauterBogoliubovReadoutMero (delta + 1 / 2) 1 lambda) ↔
      ∃ k : ℤ, delta = (k : ℂ) := by
  rw [differentialAlgebraicOver_sauterBogoliubovReadoutMero_iff_orbitMatching,
    sauterBogoliubov_affineSlice_orbitMatching_iff_integer]

/-- The Sauter logarithmic clock also has the exact affine-slice integer boundary. -/
theorem differentialAlgebraicOver_sauterBogoliubovReadoutWignerSmithLogClockMero_affineSlice_iff_integer
    (delta lambda : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (sauterBogoliubovReadoutWignerSmithLogClockMero (delta + 1 / 2) 1 lambda) ↔
      ∃ k : ℤ, delta = (k : ℂ) := by
  constructor
  · intro hclock
    by_contra hdelta
    have hnoninteger : ∀ k : ℤ, delta ≠ (k : ℂ) := by
      simpa only [not_exists] using hdelta
    have hmismatch :
        ¬ ((((∃ m : ℤ, (delta + 1 / 2) - 1 / 2 = (m : ℂ)) ∧
            ∃ n : ℤ, (1 : ℂ) - 1 = (n : ℂ)) ∨
          ((∃ m : ℤ, (delta + 1 / 2) - 1 = (m : ℂ)) ∧
            ∃ n : ℤ, (1 : ℂ) - 1 / 2 = (n : ℂ)))) := by
      rw [sauterBogoliubov_affineSlice_orbitMatching_iff_integer]
      simpa only [not_exists] using hnoninteger
    exact
      ((hypertranscendentalOver_sauterBogoliubovReadoutWignerSmithLogClockMero_iff_orbitMismatch
        (delta + 1 / 2) 1 lambda).2 hmismatch) hclock
  · intro hdelta
    unfold sauterBogoliubovReadoutWignerSmithLogClockMero HTGeometry.wignerSmithLogClock
    unfold Differential.logDeriv
    exact differentialAlgebraicOver_deriv_div_self
      ((differentialAlgebraicOver_sauterBogoliubovReadoutMero_affineSlice_iff_integer
        delta lambda).2 hdelta)

/-- Off the affine integer slice, the Sauter carrier is exactly HT. -/
theorem hypertranscendentalOver_sauterBogoliubovGammaCarrierMero_affineSlice_iff_noninteger
    (delta : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (sauterBogoliubovGammaCarrierMero (delta + 1 / 2) 1) ↔
      ∀ k : ℤ, delta ≠ (k : ℂ) := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_affineSlice_iff_integer]
  push Not
  rfl

/-- Off the affine integer slice, the Sauter readout is exactly HT. -/
theorem hypertranscendentalOver_sauterBogoliubovReadoutMero_affineSlice_iff_noninteger
    (delta lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (sauterBogoliubovReadoutMero (delta + 1 / 2) 1 lambda) ↔
      ∀ k : ℤ, delta ≠ (k : ℂ) := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_sauterBogoliubovReadoutMero_affineSlice_iff_integer]
  push Not
  rfl

/-- Off the affine integer slice, the Sauter logarithmic clock is exactly HT. -/
theorem hypertranscendentalOver_sauterBogoliubovReadoutWignerSmithLogClockMero_affineSlice_iff_noninteger
    (delta lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (sauterBogoliubovReadoutWignerSmithLogClockMero (delta + 1 / 2) 1 lambda) ↔
      ∀ k : ℤ, delta ≠ (k : ℂ) := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_sauterBogoliubovReadoutWignerSmithLogClockMero_affineSlice_iff_integer]
  push Not
  rfl

/-- Simultaneous DA phase for twelve Gamma observables selected by one affine integer orbit. -/
structure GammaIntegerOrbitMultiphysicsCollapseCertificate
    (a delta lambda : ℂ) : Prop where
  spin : DifferentialAlgebraicOver (RatFunc ℂ) (generalizedSpinTowerChannelMero delta)
  openString : DifferentialAlgebraicOver (RatFunc ℂ)
    (reducedVenezianoAmplitudeMero a delta)
  closedString : DifferentialAlgebraicOver (RatFunc ℂ)
    (reducedVirasoroShapiroAmplitudeMero a delta)
  oppositeShift : DifferentialAlgebraicOver (RatFunc ℂ)
    (gammaOppositeShiftProductMero a (delta - a))
  kerrResponse : DifferentialAlgebraicOver (RatFunc ℂ)
    (kerrNewmanChargedScalarGammaResponseMero delta)
  kerrClock : DifferentialAlgebraicOver (RatFunc ℂ)
    (kerrNewmanChargedScalarLogResponseClockMero delta)
  thermalCore : DifferentialAlgebraicOver (RatFunc ℂ)
    (gammaReflectionProductMero ((1 - delta) / 2))
  thermalResponse : DifferentialAlgebraicOver (RatFunc ℂ)
    (thermalCFTFrequencyResponseMero ((1 - delta) / 2) lambda)
  thermalClock : DifferentialAlgebraicOver (RatFunc ℂ)
    (thermalCFTResponseWignerSmithLogClockMero ((1 - delta) / 2) lambda)
  sauterCarrier : DifferentialAlgebraicOver (RatFunc ℂ)
    (sauterBogoliubovGammaCarrierMero (delta + 1 / 2) 1)
  sauterReadout : DifferentialAlgebraicOver (RatFunc ℂ)
    (sauterBogoliubovReadoutMero (delta + 1 / 2) 1 lambda)
  sauterClock : DifferentialAlgebraicOver (RatFunc ℂ)
    (sauterBogoliubovReadoutWignerSmithLogClockMero (delta + 1 / 2) 1 lambda)

/-- Simultaneous HT phase for the same twelve observables off the affine integer orbit. -/
structure GammaIntegerOrbitMultiphysicsNoncollapseCertificate
    (a delta lambda : ℂ) : Prop where
  spin : HypertranscendentalOver (RatFunc ℂ) (generalizedSpinTowerChannelMero delta)
  openString : HypertranscendentalOver (RatFunc ℂ)
    (reducedVenezianoAmplitudeMero a delta)
  closedString : HypertranscendentalOver (RatFunc ℂ)
    (reducedVirasoroShapiroAmplitudeMero a delta)
  oppositeShift : HypertranscendentalOver (RatFunc ℂ)
    (gammaOppositeShiftProductMero a (delta - a))
  kerrResponse : HypertranscendentalOver (RatFunc ℂ)
    (kerrNewmanChargedScalarGammaResponseMero delta)
  kerrClock : HypertranscendentalOver (RatFunc ℂ)
    (kerrNewmanChargedScalarLogResponseClockMero delta)
  thermalCore : HypertranscendentalOver (RatFunc ℂ)
    (gammaReflectionProductMero ((1 - delta) / 2))
  thermalResponse : HypertranscendentalOver (RatFunc ℂ)
    (thermalCFTFrequencyResponseMero ((1 - delta) / 2) lambda)
  thermalClock : HypertranscendentalOver (RatFunc ℂ)
    (thermalCFTResponseWignerSmithLogClockMero ((1 - delta) / 2) lambda)
  sauterCarrier : HypertranscendentalOver (RatFunc ℂ)
    (sauterBogoliubovGammaCarrierMero (delta + 1 / 2) 1)
  sauterReadout : HypertranscendentalOver (RatFunc ℂ)
    (sauterBogoliubovReadoutMero (delta + 1 / 2) 1 lambda)
  sauterClock : HypertranscendentalOver (RatFunc ℂ)
    (sauterBogoliubovReadoutWignerSmithLogClockMero (delta + 1 / 2) 1 lambda)

/-- **Twelve-observable collapse law.**  The multiphysics DA certificate is exactly integer-orbit
membership of the shared affine selector. -/
theorem gammaIntegerOrbit_multiphysics_simultaneousCollapse
    (a delta lambda : ℂ) :
    (∃ k : ℤ, delta = (k : ℂ)) ↔
      GammaIntegerOrbitMultiphysicsCollapseCertificate a delta lambda := by
  have hsum : a + (delta - a) = delta := by ring
  have hweight : 1 - 2 * ((1 - delta) / 2) = delta := by ring
  constructor
  · intro hdelta
    constructor
    · exact
        (differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_iff_integer delta).2 hdelta
    · exact
        (differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
          a delta).2 hdelta
    · exact
        (differentiallyAlgebraicOver_reducedVirasoroShapiroAmplitudeMero_iff_integerShift
          a delta).2 hdelta
    · apply
        (differentialAlgebraicOver_gammaOppositeShiftProductMero_iff_integerSum
          a (delta - a)).2
      simpa only [hsum] using hdelta
    · exact
        (differentialAlgebraicOver_kerrNewmanChargedScalarGammaResponseMero_iff_integerGap
          delta).2 hdelta
    · exact
        (differentialAlgebraicOver_kerrNewmanChargedScalarLogResponseClockMero_iff_integerGap
          delta).2 hdelta
    · apply
        (differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight
          ((1 - delta) / 2)).2
      simpa only [hweight] using hdelta
    · apply
        (differentialAlgebraicOver_thermalCFTFrequencyResponseMero_iff_integerWeight
          ((1 - delta) / 2) lambda).2
      simpa only [hweight] using hdelta
    · apply
        (differentialAlgebraicOver_thermalCFTResponseWignerSmithLogClockMero_iff_integerWeight
          ((1 - delta) / 2) lambda).2
      simpa only [hweight] using hdelta
    · exact
        (differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_affineSlice_iff_integer
          delta).2 hdelta
    · exact
        (differentialAlgebraicOver_sauterBogoliubovReadoutMero_affineSlice_iff_integer
          delta lambda).2 hdelta
    · exact
        (differentialAlgebraicOver_sauterBogoliubovReadoutWignerSmithLogClockMero_affineSlice_iff_integer
          delta lambda).2 hdelta
  · intro h
    exact
      (differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_iff_integer delta).1 h.spin

/-- **Twelve-observable noncollapse law.**  The multiphysics HT certificate is exactly failure of
integer-orbit membership of the shared affine selector. -/
theorem gammaIntegerOrbit_multiphysics_simultaneousHypertranscendence
    (a delta lambda : ℂ) :
    (∀ k : ℤ, delta ≠ (k : ℂ)) ↔
      GammaIntegerOrbitMultiphysicsNoncollapseCertificate a delta lambda := by
  have hsum : a + (delta - a) = delta := by ring
  have hweight : 1 - 2 * ((1 - delta) / 2) = delta := by ring
  constructor
  · intro hdelta
    constructor
    · exact
        (hypertranscendentalOver_generalizedSpinTowerChannelMero_iff_noninteger delta).2 hdelta
    · exact
        (hypertranscendentalOver_reducedVenezianoAmplitudeMero_iff_nonintegerShift
          a delta).2 hdelta
    · exact
        (hypertranscendentalOver_reducedVirasoroShapiroAmplitudeMero_iff_nonintegerShift
          a delta).2 hdelta
    · apply
        (hypertranscendentalOver_gammaOppositeShiftProductMero_iff_nonintegerSum
          a (delta - a)).2
      simpa only [hsum] using hdelta
    · exact
        (hypertranscendentalOver_kerrNewmanChargedScalarGammaResponseMero_iff_nonintegerGap
          delta).2 hdelta
    · exact
        (hypertranscendentalOver_kerrNewmanChargedScalarLogResponseClockMero_iff_nonintegerGap
          delta).2 hdelta
    · apply
        (hypertranscendentalOver_gammaReflectionProductMero_iff_nonintegerWeight
          ((1 - delta) / 2)).2
      simpa only [hweight] using hdelta
    · apply
        (hypertranscendentalOver_thermalCFTFrequencyResponseMero_iff_nonintegerWeight
          ((1 - delta) / 2) lambda).2
      simpa only [hweight] using hdelta
    · apply
        (hypertranscendentalOver_thermalCFTResponseWignerSmithLogClockMero_iff_nonintegerWeight
          ((1 - delta) / 2) lambda).2
      simpa only [hweight] using hdelta
    · exact
        (hypertranscendentalOver_sauterBogoliubovGammaCarrierMero_affineSlice_iff_noninteger
          delta).2 hdelta
    · exact
        (hypertranscendentalOver_sauterBogoliubovReadoutMero_affineSlice_iff_noninteger
          delta lambda).2 hdelta
    · exact
        (hypertranscendentalOver_sauterBogoliubovReadoutWignerSmithLogClockMero_affineSlice_iff_noninteger
          delta lambda).2 hdelta
  · intro h
    exact
      (hypertranscendentalOver_generalizedSpinTowerChannelMero_iff_noninteger delta).1 h.spin

/-- The two universal phases are exact complements; no mixed differential phase exists anywhere
in the affine multiphysics atlas. -/
theorem gammaIntegerOrbit_multiphysics_phaseComplement
    (a delta lambda : ℂ) :
    (¬ GammaIntegerOrbitMultiphysicsCollapseCertificate a delta lambda) ↔
      GammaIntegerOrbitMultiphysicsNoncollapseCertificate a delta lambda := by
  constructor
  · intro hnotCollapse
    apply (gammaIntegerOrbit_multiphysics_simultaneousHypertranscendence
      a delta lambda).1
    intro k hk
    apply hnotCollapse
    exact (gammaIntegerOrbit_multiphysics_simultaneousCollapse
      a delta lambda).1 ⟨k, hk⟩
  · intro hnoncollapse hcollapse
    have hdelta := (gammaIntegerOrbit_multiphysics_simultaneousCollapse
      a delta lambda).2 hcollapse
    have hnotInteger := (gammaIntegerOrbit_multiphysics_simultaneousHypertranscendence
      a delta lambda).2 hnoncollapse
    obtain ⟨k, hk⟩ := hdelta
    exact hnotInteger k hk

end

end GaloisForLFunctions
