import GaloisForLFunctions.HTGeometry.AtomicIncrementPrimitive
import GaloisForLFunctions.HTGeometry.AffineBaseJetGauge
import GaloisForLFunctions.HTGeometry.CoordinatewiseDifferentialFamilyMatroid
import GaloisForLFunctions.HTGeometry.JetHorizonTorsorTower
import GaloisForLFunctions.HTGeometry.NevanlinnaTranslationCharacteristic
import GaloisForLFunctions.HTGeometry.SmallGrowthRationalCoordinate
import GaloisForLFunctions.RHTower.PrimePowerDirichletFullComplexJetIndependence
import GaloisForLFunctions.RHTower.XiUpperEndHypertranscendence

/-!
# Completed-Xi atomic increment over Nagoshi's field

The rational correction in the completed-Xi `+2` defect, and every translated derivative jet of
that correction, comes from the exact small-growth coefficient field.  Consequently the filtered
von Mangoldt jet family is literally the affine consecutive-increment family of the rotated
completed logarithmic derivative over `F_s`.
-/

namespace RHTower

open Complex Filter Function Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiAtomicUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiAtomicUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiAtomicUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiAtomicUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiAtomicRationalBaseDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiAtomicRationalBaseDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField :=
  ⟨fun x => derivationClosedDifferential_apply
    upperEndRationalCoordinateField
    upperEndRationalCoordinateField_derivationClosed x⟩

local instance xiAtomicSmallGrowthDifferential :
    Differential SmallGrowthMeromorphicField where
  deriv := 0

/-- Upper-end translation is semilinear over the exact small-growth coefficient field. -/
noncomputable def smallGrowthUpperEndTranslationDifferentialSemilinearEquiv (h : ℂ) :
    DifferentialSemilinearEquiv SmallGrowthMeromorphicField upperEndMeroField where
  baseEquiv := smallGrowthTranslateEquiv h
  ambientEquiv := upperEndTranslationMeroEquiv h
  map_algebraMap' x := (smallGrowthTranslateEquiv_algebraMap h x).symm
  map_base_deriv' x := by
    change smallGrowthTranslateEquiv h 0 = 0
    exact map_zero (smallGrowthTranslateEquiv h)
  map_ambient_deriv' x := upperEndTranslationMeroEquiv_deriv h x

/-- Each shifted reciprocal in the completed-Xi correction belongs to genuine `ℂ(s)`. -/
private theorem xiShiftReciprocalUpperEndCarrier_mem_rationalCoordinateField (c : ℝ) :
    algebraMap upperEndAnalyticSubring upperEndMeroField
        (xiShiftReciprocalUpperEndAnalytic c) ∈
      upperEndRationalCoordinateField := by
  rw [xiShiftReciprocalUpperEndMero]
  have hz : upperEndCoordinateMero ∈ upperEndRationalCoordinateField :=
    IntermediateField.subset_adjoin ℂ _ (Set.mem_singleton _)
  have hI : -algebraMap ℂ upperEndMeroField I ∈
      upperEndRationalCoordinateField :=
    upperEndRationalCoordinateField.neg_mem
      (upperEndRationalCoordinateField.algebraMap_mem I)
  exact upperEndRationalCoordinateField.inv_mem
    (upperEndRationalCoordinateField.add_mem
      (upperEndRationalCoordinateField.mul_mem hI hz)
      (upperEndRationalCoordinateField.algebraMap_mem (c : ℂ)))

/-- The explicit completed-Xi `+2` correction belongs to the genuine `ℂ(s)` subfield. -/
theorem xiShiftTwoRationalCorrectionUpperEndCarrier_mem_rationalCoordinateField :
    xiShiftTwoRationalCorrectionUpperEndCarrier ∈ upperEndRationalCoordinateField := by
  change algebraMap upperEndAnalyticSubring upperEndMeroField
      (xiShiftReciprocalUpperEndAnalytic 2 +
        xiShiftReciprocalUpperEndAnalytic 1 -
        xiShiftReciprocalUpperEndAnalytic (-1)) ∈
    upperEndRationalCoordinateField
  rw [map_sub, map_add]
  exact upperEndRationalCoordinateField.sub_mem
    (upperEndRationalCoordinateField.add_mem
      (xiShiftReciprocalUpperEndCarrier_mem_rationalCoordinateField 2)
      (xiShiftReciprocalUpperEndCarrier_mem_rationalCoordinateField 1))
    (xiShiftReciprocalUpperEndCarrier_mem_rationalCoordinateField (-1))

/-- Every translated derivative jet of the correction remains in the genuine `ℂ(s)` subfield. -/
theorem xiShiftTwoRationalCorrection_translatedJet_mem_rationalCoordinateField
    (h : ℂ) (k : ℕ) :
    differentialJet k
        (upperEndTranslationMeroEquiv (I * h)
          xiShiftTwoRationalCorrectionUpperEndCarrier) ∈
      upperEndRationalCoordinateField := by
  have htranslated :
      upperEndTranslationMeroEquiv (I * h)
          xiShiftTwoRationalCorrectionUpperEndCarrier ∈
        upperEndRationalCoordinateField := by
    have hmem :=
      (upperEndRationalCoordinateTranslationAlgEquiv (I * h)
        (⟨xiShiftTwoRationalCorrectionUpperEndCarrier,
          xiShiftTwoRationalCorrectionUpperEndCarrier_mem_rationalCoordinateField⟩ :
            upperEndRationalCoordinateField)).property
    simpa only [upperEndRationalCoordinateTranslationAlgEquiv_apply] using hmem
  exact differentialJet_mem_of_derivationClosed
    upperEndRationalCoordinateField_derivationClosed k htranslated

/-- Chosen exact `F_s` coefficient representing each translated correction jet. -/
noncomputable def xiShiftTwoRationalCorrectionSmallGrowthJet (hk : ℂ × ℕ) :
    SmallGrowthMeromorphicField :=
  Classical.choose
    (exists_smallGrowth_preimage_of_mem_upperEndRationalCoordinateField
      (xiShiftTwoRationalCorrection_translatedJet_mem_rationalCoordinateField hk.1 hk.2))

@[simp]
theorem xiShiftTwoRationalCorrectionSmallGrowthJet_algebraMap (hk : ℂ × ℕ) :
    algebraMap SmallGrowthMeromorphicField upperEndMeroField
        (xiShiftTwoRationalCorrectionSmallGrowthJet hk) =
      differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiShiftTwoRationalCorrectionUpperEndCarrier) :=
  Classical.choose_spec
    (exists_smallGrowth_preimage_of_mem_upperEndRationalCoordinateField
      (xiShiftTwoRationalCorrection_translatedJet_mem_rationalCoordinateField hk.1 hk.2))

/-- The same correction jet as an element of the genuine rational-coordinate field. -/
noncomputable def xiShiftTwoRationalCorrectionCoordinateJet (hk : ℂ × ℕ) :
    upperEndRationalCoordinateField :=
  ⟨differentialJet hk.2
      (upperEndTranslationMeroEquiv (I * hk.1)
        xiShiftTwoRationalCorrectionUpperEndCarrier),
    xiShiftTwoRationalCorrection_translatedJet_mem_rationalCoordinateField hk.1 hk.2⟩

@[simp]
theorem xiShiftTwoRationalCorrectionCoordinateJet_algebraMap (hk : ℂ × ℕ) :
    algebraMap upperEndRationalCoordinateField upperEndMeroField
        (xiShiftTwoRationalCorrectionCoordinateJet hk) =
      differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiShiftTwoRationalCorrectionUpperEndCarrier) :=
  rfl

/-- Full primitive jet family of the rotated completed logarithmic derivative. -/
noncomputable def xiLogDerivRotatedFullComplexShiftJets (hk : ℂ × ℕ) :
    upperEndMeroField :=
  differentialJet hk.2
    (upperEndTranslationMeroEquiv (I * hk.1)
      xiLogDerivRotatedUpperEndCarrier)

/-- The filtered von Mangoldt jets are exact affine `+2` increments of completed-Xi jets over
`F_s`. -/
theorem filteredVonMangoldt_fullComplexShiftJets_eq_xi_affineIncrement (hk : ℂ × ℕ) :
    differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          filteredVonMangoldtUpperEndCarrier) =
      xiLogDerivRotatedFullComplexShiftJets
          (GaloisForLFunctions.MatroidGluing.complexJetEvenShift hk) -
        xiLogDerivRotatedFullComplexShiftJets hk -
        algebraMap SmallGrowthMeromorphicField upperEndMeroField
          (xiShiftTwoRationalCorrectionSmallGrowthJet hk) := by
  rw [xiShiftTwoRationalCorrectionSmallGrowthJet_algebraMap]
  change differentialJet hk.2
      (upperEndTranslationMeroEquiv (I * hk.1)
        filteredVonMangoldtUpperEndCarrier) =
    differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * (hk.1 + 2))
          xiLogDerivRotatedUpperEndCarrier) -
      differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiLogDerivRotatedUpperEndCarrier) -
      differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiShiftTwoRationalCorrectionUpperEndCarrier)
  rw [← differentialJet_sub, ← differentialJet_sub]
  congr 1
  have htranslated := congrArg (upperEndTranslationMeroEquiv (I * hk.1))
    xiLogDerivRotatedUpperEnd_translation_defect
  simpa only [map_sub, upperEndTranslationMeroEquiv_add,
    show I * hk.1 + 2 * I = I * (hk.1 + 2) by ring] using htranslated.symm

/-- Rational-coordinate form of the same exact affine increment law. -/
theorem filteredVonMangoldt_fullComplexShiftJets_eq_xi_affineIncrement_rational
    (hk : ℂ × ℕ) :
    differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          filteredVonMangoldtUpperEndCarrier) =
      xiLogDerivRotatedFullComplexShiftJets
          (GaloisForLFunctions.MatroidGluing.complexJetEvenShift hk) -
        xiLogDerivRotatedFullComplexShiftJets hk -
        algebraMap upperEndRationalCoordinateField upperEndMeroField
          (xiShiftTwoRationalCorrectionCoordinateJet hk) := by
  rw [xiShiftTwoRationalCorrectionCoordinateJet_algebraMap]
  change differentialJet hk.2
      (upperEndTranslationMeroEquiv (I * hk.1)
        filteredVonMangoldtUpperEndCarrier) =
    differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * (hk.1 + 2))
          xiLogDerivRotatedUpperEndCarrier) -
      differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiLogDerivRotatedUpperEndCarrier) -
      differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiShiftTwoRationalCorrectionUpperEndCarrier)
  rw [← differentialJet_sub, ← differentialJet_sub]
  congr 1
  have htranslated := congrArg (upperEndTranslationMeroEquiv (I * hk.1))
    xiLogDerivRotatedUpperEnd_translation_defect
  simpa only [map_sub, upperEndTranslationMeroEquiv_add,
    show I * hk.1 + 2 * I = I * (hk.1 + 2) by ring] using htranslated.symm

/-- Common translation by `+2` preserves algebraic rank of the completed-Xi full jet family over
the normalized rational-coordinate base. -/
theorem complexJetEvenShift_mem_xiLogDerivRotatedFullComplexShiftJets_rankAut :
    GaloisForLFunctions.MatroidGluing.complexJetEvenShift ∈
      (GaloisForLFunctions.MatroidGluing.matroidRank
        (algebraicFamilyMatroid upperEndRationalCoordinateField
          xiLogDerivRotatedFullComplexShiftJets)).rankAutSubgroup := by
  apply GaloisForLFunctions.MatroidGluing.algebraicFamilyRank_mem_rankAutSubgroup_of_semilinear
    (upperEndRationalCoordinateTranslationDifferentialSemilinearEquiv (2 * I))
  intro hk
  change upperEndTranslationMeroEquiv (2 * I)
      (differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiLogDerivRotatedUpperEndCarrier)) =
    differentialJet hk.2
      (upperEndTranslationMeroEquiv (I * (hk.1 + 2))
        xiLogDerivRotatedUpperEndCarrier)
  have hjet := (upperEndRationalCoordinateTranslationDifferentialSemilinearEquiv
    (2 * I)).map_differentialJet hk.2
      (upperEndTranslationMeroEquiv (I * hk.1)
        xiLogDerivRotatedUpperEndCarrier)
  change upperEndTranslationMeroEquiv (2 * I)
      (differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiLogDerivRotatedUpperEndCarrier)) =
    differentialJet hk.2
      (upperEndTranslationMeroEquiv (2 * I)
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiLogDerivRotatedUpperEndCarrier)) at hjet
  rw [hjet]
  congr 1
  rw [upperEndTranslationMeroEquiv_add]
  congr 1
  ring_nf

/-- Common translation by `+2` preserves algebraic rank over Nagoshi's exact small-growth
coefficient field. -/
theorem complexJetEvenShift_mem_xiLogDerivRotatedFullComplexShiftJets_rankAut_smallGrowth :
    GaloisForLFunctions.MatroidGluing.complexJetEvenShift ∈
      (GaloisForLFunctions.MatroidGluing.matroidRank
        (algebraicFamilyMatroid SmallGrowthMeromorphicField
          xiLogDerivRotatedFullComplexShiftJets)).rankAutSubgroup := by
  apply GaloisForLFunctions.MatroidGluing.algebraicFamilyRank_mem_rankAutSubgroup_of_semilinear
    (smallGrowthUpperEndTranslationDifferentialSemilinearEquiv (2 * I))
  intro hk
  change upperEndTranslationMeroEquiv (2 * I)
      (differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiLogDerivRotatedUpperEndCarrier)) =
    differentialJet hk.2
      (upperEndTranslationMeroEquiv (I * (hk.1 + 2))
        xiLogDerivRotatedUpperEndCarrier)
  have hjet := (smallGrowthUpperEndTranslationDifferentialSemilinearEquiv
    (2 * I)).map_differentialJet hk.2
      (upperEndTranslationMeroEquiv (I * hk.1)
        xiLogDerivRotatedUpperEndCarrier)
  change upperEndTranslationMeroEquiv (2 * I)
      (differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiLogDerivRotatedUpperEndCarrier)) =
    differentialJet hk.2
      (upperEndTranslationMeroEquiv (2 * I)
        (upperEndTranslationMeroEquiv (I * hk.1)
          xiLogDerivRotatedUpperEndCarrier)) at hjet
  rw [hjet]
  congr 1
  rw [upperEndTranslationMeroEquiv_add]
  congr 1
  ring_nf

/-- The complete rotated `xi'/xi` translation-jet family is algebraically independent over the
genuine rational-coordinate field. -/
theorem xiLogDerivRotated_fullComplexShiftJets_algebraicIndependent :
    AlgebraicIndependent upperEndRationalCoordinateField
      xiLogDerivRotatedFullComplexShiftJets := by
  exact GaloisForLFunctions.MatroidGluing.algebraicIndependent_primitive_of_evenShift_increments
      xiLogDerivRotatedFullComplexShiftJets
      (fun hk : ℂ × ℕ => differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          filteredVonMangoldtUpperEndCarrier))
      xiShiftTwoRationalCorrectionCoordinateJet
      filteredVonMangoldt_fullComplexShiftJets_algebraicIndependent
      filteredVonMangoldt_fullComplexShiftJets_eq_xi_affineIncrement_rational
      complexJetEvenShift_mem_xiLogDerivRotatedFullComplexShiftJets_rankAut

/-- The complete rotated `xi'/xi` translation-jet family is algebraically independent over
Nagoshi's exact small-growth meromorphic field. -/
theorem xiLogDerivRotated_fullComplexShiftJets_algebraicIndependent_over_smallGrowth :
    AlgebraicIndependent SmallGrowthMeromorphicField
      xiLogDerivRotatedFullComplexShiftJets := by
  exact GaloisForLFunctions.MatroidGluing.algebraicIndependent_primitive_of_evenShift_increments
      xiLogDerivRotatedFullComplexShiftJets
      (fun hk : ℂ × ℕ => differentialJet hk.2
        (upperEndTranslationMeroEquiv (I * hk.1)
          filteredVonMangoldtUpperEndCarrier))
      xiShiftTwoRationalCorrectionSmallGrowthJet
      filteredVonMangoldt_fullComplexShiftJets_algebraicIndependent_over_smallGrowth
      filteredVonMangoldt_fullComplexShiftJets_eq_xi_affineIncrement
      complexJetEvenShift_mem_xiLogDerivRotatedFullComplexShiftJets_rankAut_smallGrowth

/-- Differential-independence form of the completed logarithmic-derivative orbit over `F_s`. -/
theorem xiLogDerivRotated_fullComplexShiftOrbit_differentialIndependent_over_smallGrowth :
    DifferentialIndependent SmallGrowthMeromorphicField
      (fun h : ℂ => upperEndTranslationMeroEquiv (I * h)
        xiLogDerivRotatedUpperEndCarrier) := by
  unfold DifferentialIndependent
  exact xiLogDerivRotated_fullComplexShiftJets_algebraicIndependent_over_smallGrowth

/-- Differential-independence form of the full completed logarithmic-derivative orbit over
`ℂ(s)`. -/
theorem xiLogDerivRotated_fullComplexShiftOrbit_differentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun h : ℂ => upperEndTranslationMeroEquiv (I * h)
        xiLogDerivRotatedUpperEndCarrier) := by
  unfold DifferentialIndependent
  exact xiLogDerivRotated_fullComplexShiftJets_algebraicIndependent

/-- The full complex translation orbit of the actual rotated completed-Xi carrier is
differentially independent over `ℂ(s)`. -/
theorem xiRotated_fullComplexShiftOrbit_differentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun h : ℂ => upperEndTranslationMeroEquiv (I * h)
        xiRotatedUpperEndCarrier) := by
  let a : upperEndRationalCoordinateField :=
    ⟨-algebraMap ℂ upperEndMeroField I,
      upperEndRationalCoordinateField.neg_mem
        (upperEndRationalCoordinateField.algebraMap_mem I)⟩
  have ha : a ≠ 0 := by
    intro hazero
    have hvalue := congrArg Subtype.val hazero
    change -algebraMap ℂ upperEndMeroField I = 0 at hvalue
    apply Complex.I_ne_zero
    apply FaithfulSMul.algebraMap_injective ℂ upperEndMeroField
    simpa using neg_eq_zero.mp hvalue
  have hscaled :=
    xiLogDerivRotated_fullComplexShiftOrbit_differentialIndependent.mulBase
      (fun _ : ℂ => a) (fun _ => ha)
  let u : ℂ → upperEndMeroField := fun h =>
    upperEndTranslationMeroEquiv (I * h) xiRotatedUpperEndCarrier
  have hlog : (fun h : ℂ => (u h)′ / u h) =
      fun h : ℂ => algebraMap upperEndRationalCoordinateField upperEndMeroField a *
        upperEndTranslationMeroEquiv (I * h)
          xiLogDerivRotatedUpperEndCarrier := by
    funext h
    change (upperEndTranslationMeroEquiv (I * h) xiRotatedUpperEndCarrier)′ /
        upperEndTranslationMeroEquiv (I * h) xiRotatedUpperEndCarrier = _
    calc
      (upperEndTranslationMeroEquiv (I * h) xiRotatedUpperEndCarrier)′ /
          upperEndTranslationMeroEquiv (I * h) xiRotatedUpperEndCarrier =
        upperEndTranslationMeroEquiv (I * h)
          (xiRotatedUpperEndCarrier′ / xiRotatedUpperEndCarrier) := by
            rw [← upperEndTranslationMeroEquiv_deriv, map_div₀]
      _ = upperEndTranslationMeroEquiv (I * h)
          (-algebraMap ℂ upperEndMeroField I *
            xiLogDerivRotatedUpperEndCarrier) := by
            rw [xiRotatedUpperEndCarrier_logDeriv]
      _ = algebraMap upperEndRationalCoordinateField upperEndMeroField a *
          upperEndTranslationMeroEquiv (I * h)
            xiLogDerivRotatedUpperEndCarrier := by
            rw [map_mul, map_neg]
            have hconst := (upperEndTranslationMeroDifferentialAlgEquiv
              (I * h)).toAlgEquiv.commutes I
            change upperEndTranslationMeroEquiv (I * h)
                (algebraMap ℂ upperEndMeroField I) =
              algebraMap ℂ upperEndMeroField I at hconst
            rw [hconst]
            rfl
  apply (differentialIndependent_deriv_div_self_iff u).mpr
  rw [hlog]
  exact hscaled

end

end RHTower
