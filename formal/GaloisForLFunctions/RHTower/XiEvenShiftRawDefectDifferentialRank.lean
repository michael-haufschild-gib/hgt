import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroidBaseGauge
import GaloisForLFunctions.HTGeometry.DifferentialConstantLinearFamilyMatroid
import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionIncidenceMatroid
import GaloisForLFunctions.HTGeometry.DifferentialPairwiseCommonMode
import GaloisForLFunctions.RHTower.XiEvenShiftPrimeDefectTelescope
import GaloisForLFunctions.RHTower.XiShiftAllValuationLayerBarrier
import GaloisForLFunctions.RHTower.XiTransverseShiftAllValuationLayerRank

/-!
# Exact differential rank of raw even completed-Xi shift defects

The corrected shift-`2m` completed-Xi defects already represent the pointed collision matroid of
their grades. Their accumulated archimedean corrections are explicit rational-coordinate
gauges. The general affine base-gauge matroid law therefore removes the correction completely:
the raw logarithmic-derivative differences of the actual completed Xi function represent the
same exact matroid.

The result holds both over the genuine rational coordinate field and after adjoining every scalar
prime-valuation layer. Zero shifts are loops, repeated shifts are parallel, and the rank of every
arbitrarily indexed packet is the number of distinct nonzero even-shift grades.
-/

namespace RHTower

open Complex Filter Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiEvenRawUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiEvenRawUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiEvenRawUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiEvenRawUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiEvenRawCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiEvenRawCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiEvenRawAllValuationFieldDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiEvenRawAllValuationFieldDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-! ## Rational correction and actual value reflection -/

/-- Upper-end analytic realization of the accumulated rational correction for the shift `2m`. -/
def xiEvenShiftPrimeCorrectionAnalytic (m : ℕ) : upperEndAnalyticSubring :=
  ∑ j ∈ Finset.range m,
    (xiShiftLinearFactorInvAnalytic (((2 * j : ℕ) : ℝ) + 2) (by
        have hj : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith) +
      xiShiftLinearFactorInvAnalytic (((2 * j : ℕ) : ℝ) + 1) (by
        have hj : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith) -
      xiShiftLinearFactorInvAnalytic (((2 * j : ℕ) : ℝ) - 1) (by
        have hj : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith))

/-- The analytic correction has exactly the value prescribed by the completed-Xi telescope. -/
theorem xiEvenShiftPrimeCorrectionAnalytic_coe (m : ℕ) :
    ((xiEvenShiftPrimeCorrectionAnalytic m : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) =
      ((fun z : ℂ ↦ xiEvenShiftPrimeCorrection m (-Complex.I * z)) :
        Germ upperEndFilter ℂ) := by
  rw [xiEvenShiftPrimeCorrectionAnalytic]
  change upperEndAnalyticSubring.subtype
      (∑ j ∈ Finset.range m,
        (xiShiftLinearFactorInvAnalytic (((2 * j : ℕ) : ℝ) + 2) _ +
          xiShiftLinearFactorInvAnalytic (((2 * j : ℕ) : ℝ) + 1) _ -
          xiShiftLinearFactorInvAnalytic (((2 * j : ℕ) : ℝ) - 1) _)) = _
  rw [map_sum]
  simp only [map_sub, map_add]
  change (∑ j ∈ Finset.range m,
      ((fun z : ℂ ↦
        (xiShiftLinearFactor (((2 * j : ℕ) : ℝ) + 2) z)⁻¹ +
        (xiShiftLinearFactor (((2 * j : ℕ) : ℝ) + 1) z)⁻¹ -
        (xiShiftLinearFactor (((2 * j : ℕ) : ℝ) - 1) z)⁻¹) :
          Germ upperEndFilter ℂ)) = _
  rw [← Germ.coe_sum]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    simp only [xiEvenShiftPrimeCorrection, Finset.sum_apply,
      xiShiftLinearFactor, one_div]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring

/-- Meromorphic rational-coordinate realization of the accumulated correction. -/
def xiEvenShiftPrimeCorrectionMero (m : ℕ) : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField
    (xiEvenShiftPrimeCorrectionAnalytic m)

/-- Every accumulated even-shift correction lies in the genuine rational coordinate field. -/
theorem xiEvenShiftPrimeCorrectionMero_mem_rationalCoordinate (m : ℕ) :
    xiEvenShiftPrimeCorrectionMero m ∈ upperEndRationalCoordinateField := by
  rw [xiEvenShiftPrimeCorrectionMero, xiEvenShiftPrimeCorrectionAnalytic, map_sum]
  apply IntermediateField.sum_mem
  intro j _
  rw [map_sub, map_add]
  exact upperEndRationalCoordinateField.sub_mem
    (upperEndRationalCoordinateField.add_mem
      (xiShiftLinearFactorInvMero_mem_rationalCoordinate
        (((2 * j : ℕ) : ℝ) + 2) (by
          have hj : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith))
      (xiShiftLinearFactorInvMero_mem_rationalCoordinate
        (((2 * j : ℕ) : ℝ) + 1) (by
          have hj : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith)))
    (xiShiftLinearFactorInvMero_mem_rationalCoordinate
      (((2 * j : ℕ) : ℝ) - 1) (by
        have hj : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith))

/-- Raw, uncorrected shift-`2m` completed-Xi logarithmic-derivative carrier. -/
def xiEvenShiftRawLogDerivDefectUpperEndCarrier (m : ℕ) : upperEndMeroField :=
  xiEvenShiftPrimeDefectUpperEndCarrier m + xiEvenShiftPrimeCorrectionMero m

/-- Upper-end germ of the actual raw shift-`2m` completed-Xi logarithmic-derivative defect. -/
def xiEvenShiftRawLogDerivDefectUpperEndGerm (m : ℕ) : Germ upperEndFilter ℂ :=
  ((fun z : ℂ ↦
    logDeriv xi (-Complex.I * z + (2 * m : ℕ)) -
      logDeriv xi (-Complex.I * z)) : Germ upperEndFilter ℂ)

/-- Analytic representative of the raw even-shift completed-Xi carrier. -/
def xiEvenShiftRawLogDerivDefectUpperEndAnalytic (m : ℕ) : upperEndAnalyticSubring :=
  finiteAbscissaLSeriesToUpperEndAnalytic
      (xiTransverseShiftFiniteAbscissaSource (2 * m)) +
    xiEvenShiftPrimeCorrectionAnalytic m

/-- The raw carrier is represented by the source analytic germ plus the rational correction. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_eq_algebraMap (m : ℕ) :
    xiEvenShiftRawLogDerivDefectUpperEndCarrier m =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (xiEvenShiftRawLogDerivDefectUpperEndAnalytic m) := by
  simp only [xiEvenShiftRawLogDerivDefectUpperEndCarrier,
    xiEvenShiftRawLogDerivDefectUpperEndAnalytic,
    xiEvenShiftPrimeDefectUpperEndCarrier, xiTransverseShiftUpperEndCarrier,
    xiEvenShiftPrimeCorrectionMero,
    finiteAbscissaLSeriesToUpperEndMero_eq_algebraMap, map_add]

/-- **Raw completed-Xi value reflection.** The carrier above has exactly the uncorrected actual
shift-`2m` logarithmic-derivative difference as its upper-end germ. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_germ_eq (m : ℕ) :
    ((xiEvenShiftRawLogDerivDefectUpperEndAnalytic m : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) =
      xiEvenShiftRawLogDerivDefectUpperEndGerm m := by
  rw [xiEvenShiftRawLogDerivDefectUpperEndAnalytic]
  change finiteAbscissaLSeriesToUpperEndGerm
      (xiTransverseShiftFiniteAbscissaSource (2 * m)) +
    ((xiEvenShiftPrimeCorrectionAnalytic m : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) = _
  rw [xiTransverseEvenShiftUpperEndGerm_eq_xiEvenShiftPrimeDefect,
    xiEvenShiftPrimeCorrectionAnalytic_coe]
  change ((fun z : ℂ ↦ xiEvenShiftPrimeDefect m (-Complex.I * z)) :
      Germ upperEndFilter ℂ) +
    ((fun z : ℂ ↦ xiEvenShiftPrimeCorrection m (-Complex.I * z)) :
      Germ upperEndFilter ℂ) = _
  rw [← Germ.coe_add]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    simp only [Pi.add_apply, xiEvenShiftPrimeDefect]
    ring

@[simp]
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_zero :
    xiEvenShiftRawLogDerivDefectUpperEndCarrier 0 = 0 := by
  simp [xiEvenShiftRawLogDerivDefectUpperEndCarrier,
    xiEvenShiftPrimeDefectUpperEndCarrier, xiEvenShiftPrimeCorrectionMero,
    xiEvenShiftPrimeCorrectionAnalytic]

/-! ## Pairwise raw completed-Xi value relations -/

/-- Carrier of the raw completed-Xi difference between two labelled even translates. -/
def xiEvenShiftRawPairDifferenceUpperEndCarrier
    {V E : Type*} (grade : V → ℕ) (tail head : E → V) (e : E) :
    upperEndMeroField :=
  xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade (head e)) -
    xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade (tail e))

/-- Analytic representative of the pairwise raw even-translate difference. -/
def xiEvenShiftRawPairDifferenceUpperEndAnalytic
    {V E : Type*} (grade : V → ℕ) (tail head : E → V) (e : E) :
    upperEndAnalyticSubring :=
  xiEvenShiftRawLogDerivDefectUpperEndAnalytic (grade (head e)) -
    xiEvenShiftRawLogDerivDefectUpperEndAnalytic (grade (tail e))

/-- Actual upper-end germ of the pairwise completed-Xi logarithmic-derivative difference. -/
def xiEvenShiftRawPairDifferenceUpperEndGerm
    {V E : Type*} (grade : V → ℕ) (tail head : E → V) (e : E) :
    Germ upperEndFilter ℂ :=
  ((fun z : ℂ ↦
    logDeriv xi (-Complex.I * z + (2 * grade (head e) : ℕ)) -
      logDeriv xi (-Complex.I * z + (2 * grade (tail e) : ℕ))) :
    Germ upperEndFilter ℂ)

/-- Pairwise raw carriers are represented by the difference of their analytic representatives. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_eq_algebraMap
    {V E : Type*} (grade : V → ℕ) (tail head : E → V) (e : E) :
    xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head e =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (xiEvenShiftRawPairDifferenceUpperEndAnalytic grade tail head e) := by
  rw [xiEvenShiftRawPairDifferenceUpperEndCarrier,
    xiEvenShiftRawPairDifferenceUpperEndAnalytic,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_eq_algebraMap,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_eq_algebraMap, map_sub]

/-- **Pairwise raw completed-Xi value reflection.** Subtracting two basepoint defects cancels the
basepoint and leaves the literal logarithmic-derivative difference between the two even
translates. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_germ_eq
    {V E : Type*} (grade : V → ℕ) (tail head : E → V) (e : E) :
    ((xiEvenShiftRawPairDifferenceUpperEndAnalytic grade tail head e :
        upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
      xiEvenShiftRawPairDifferenceUpperEndGerm grade tail head e := by
  rw [xiEvenShiftRawPairDifferenceUpperEndAnalytic]
  change ((xiEvenShiftRawLogDerivDefectUpperEndAnalytic (grade (head e)) :
      upperEndAnalyticSubring) : Germ upperEndFilter ℂ) -
    ((xiEvenShiftRawLogDerivDefectUpperEndAnalytic (grade (tail e)) :
      upperEndAnalyticSubring) : Germ upperEndFilter ℂ) = _
  rw [xiEvenShiftRawLogDerivDefectUpperEndCarrier_germ_eq,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_germ_eq]
  change ((fun z : ℂ ↦
      (logDeriv xi (-Complex.I * z + (2 * grade (head e) : ℕ)) -
        logDeriv xi (-Complex.I * z)) -
      (logDeriv xi (-Complex.I * z + (2 * grade (tail e) : ℕ)) -
        logDeriv xi (-Complex.I * z))) : Germ upperEndFilter ℂ) = _
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun _ ↦ by ring

/-- **Complete pairwise Xi generated-field law.** For any graded vertex family containing a
zero-grade root, all ordered raw even completed-Xi translate differences generate exactly the
same differential field as the vertex defects over the rational coordinate base. No finiteness,
distinctness, or positivity hypothesis is needed. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_vertices
    {V : Type} (root : V) (grade : V → ℕ) (hroot : grade root = 0) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade Prod.snd Prod.fst)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) := by
  let x := fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)
  have hx0 : x root = 0 := by
    simp [x, hroot]
  have h := differentialAdjoin_range_pairwiseDifferences_eq_of_root_zero
    (F := upperEndRationalCoordinateField) (K := upperEndMeroField) root x hx0
  simpa only [x, xiEvenShiftRawPairDifferenceUpperEndCarrier] using h

/-- The complete pairwise Xi generated-field law remains exact after every scalar valuation layer
has been adjoined to the base. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_vertices
    {V : Type} (root : V) (grade : V → ℕ) (hroot : grade root = 0) :
    differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade Prod.snd Prod.fst)) =
      differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) := by
  let x := fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)
  have hx0 : x root = 0 := by
    simp [x, hroot]
  have h := differentialAdjoin_range_pairwiseDifferences_eq_of_root_zero
    (F := analyticScalarValuationLayerDifferentialField) (K := upperEndMeroField) root x hx0
  simpa only [x, xiEvenShiftRawPairDifferenceUpperEndCarrier] using h

/-! ## Exact matroid over the rational coordinate field -/

/-- The correction as an element of the rational differential base. -/
def xiEvenShiftPrimeCorrectionCoordinate (m : ℕ) :
    upperEndRationalCoordinateField :=
  ⟨xiEvenShiftPrimeCorrectionMero m,
    xiEvenShiftPrimeCorrectionMero_mem_rationalCoordinate m⟩

/-- Every arbitrary raw even-shift family generates exactly the same embedded differential field
as its corrected prime-source family over the rational coordinate base. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialAdjoin_eq_corrected
    {A : Type*} (grade : A → ℕ) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun a ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade a)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun a ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade a)) := by
  change differentialAdjoin upperEndRationalCoordinateField
      (Set.range fun a ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade a) +
        algebraMap upperEndRationalCoordinateField upperEndMeroField
          (xiEvenShiftPrimeCorrectionCoordinate (grade a))) = _
  simpa using differentialAdjoin_range_affineBase_eq
    (fun a ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade a))
    (fun _ ↦ 1) (fun a ↦ xiEvenShiftPrimeCorrectionCoordinate (grade a))
    (fun _ ↦ one_ne_zero)

/-- Rational correction does not change the represented matroid of an arbitrary even-shift
family. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialMatroid_eq_corrected
    {A : Type*} (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade a)) =
      differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade a)) := by
  change differentialFamilyMatroid
      (F := upperEndRationalCoordinateField)
      (fun a ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade a) +
        algebraMap upperEndRationalCoordinateField upperEndMeroField
          (xiEvenShiftPrimeCorrectionCoordinate (grade a))) = _
  exact differentialFamilyMatroid_addBase_eq _ _

/-- **Raw even completed-Xi collision law.** Zero shifts are loops, repeated shifts are parallel,
and distinct positive grades are exactly the differential directions of the uncorrected actual
completed-Xi family. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision
    {A : Type*} (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade a)) =
      affinePointedCollisionMatroid grade 0 := by
  rw [xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialMatroid_eq_corrected,
    xiEvenShiftPrimeDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision]

/-- Prop interface for every packet of raw even completed-Xi defects. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialIndependent_iff
    {A : Type*} (grade : A → ℕ) (I : Set A) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun i : I ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) ↔
      Set.InjOn grade I ∧ ∀ i ∈ I, grade i ≠ 0 := by
  let x := fun a ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade a)
  rw [← differentialFamilyMatroid_indep_iff x I,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_indep_iff]

/-- Exact differential rank of every raw even completed-Xi packet. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialMatroid_eRk
    {A : Type*} (grade : A → ℕ) (I : Set A) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade a))).eRk I =
      ((grade '' I) ∩ {m | m ≠ 0}).encard := by
  rw [xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_eRk]

/-! ## Exact matroid after adjoining every scalar valuation layer -/

/-- The same rational correction, embedded in the complete scalar valuation-layer field. -/
def xiEvenShiftPrimeCorrectionAllValuation (m : ℕ) :
    analyticScalarValuationLayerDifferentialField :=
  ⟨xiEvenShiftPrimeCorrectionMero m,
    IntermediateField.algebraMap_mem
      analyticScalarValuationLayerDifferentialField
      (xiEvenShiftPrimeCorrectionCoordinate m)⟩

/-- The raw and corrected even-shift families also generate the same embedded differential field
over the complete scalar valuation-layer base. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialAdjoin_eq_corrected
    {A : Type*} (grade : A → ℕ) :
    differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun a ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade a)) =
      differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun a ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade a)) := by
  change differentialAdjoin analyticScalarValuationLayerDifferentialField
      (Set.range fun a ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade a) +
        algebraMap analyticScalarValuationLayerDifferentialField upperEndMeroField
          (xiEvenShiftPrimeCorrectionAllValuation (grade a))) = _
  simpa using differentialAdjoin_range_affineBase_eq
    (fun a ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade a))
    (fun _ ↦ 1) (fun a ↦ xiEvenShiftPrimeCorrectionAllValuation (grade a))
    (fun _ ↦ one_ne_zero)

/-- **Complete pairwise source-recovery law.** When the raw even Xi family contains its zero
shift, the complete pairwise reporter generates the full corrected prime-source differential
field over the rational coordinate base. Thus pairwise completed-Xi translate observations lose
neither the common mode nor any arithmetic source direction. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_corrected
    {V : Type} (root : V) (grade : V → ℕ) (hroot : grade root = 0) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade Prod.snd Prod.fst)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun v ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade v)) := by
  calc
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade Prod.snd Prod.fst)) =
        differentialAdjoin upperEndRationalCoordinateField
          (Set.range fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) :=
      xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_vertices
        root grade hroot
    _ = differentialAdjoin upperEndRationalCoordinateField
          (Set.range fun v ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade v)) :=
      xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialAdjoin_eq_corrected grade

/-- The complete pairwise raw Xi reporter also recovers the corrected prime-source field after
all scalar valuation layers have been adjoined. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_corrected
    {V : Type} (root : V) (grade : V → ℕ) (hroot : grade root = 0) :
    differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade Prod.snd Prod.fst)) =
      differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun v ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade v)) := by
  calc
    differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade Prod.snd Prod.fst)) =
        differentialAdjoin analyticScalarValuationLayerDifferentialField
          (Set.range fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) :=
      xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_vertices
        root grade hroot
    _ = differentialAdjoin analyticScalarValuationLayerDifferentialField
          (Set.range fun v ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade v)) :=
      xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialAdjoin_eq_corrected grade

/-- Rational correction does not change the represented matroid after every scalar valuation
layer has been adjoined. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialMatroid_eq_corrected
    {A : Type*} (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun a ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade a)) =
      differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun a ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade a)) := by
  change differentialFamilyMatroid
      (F := analyticScalarValuationLayerDifferentialField)
      (fun a ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade a) +
        algebraMap analyticScalarValuationLayerDifferentialField upperEndMeroField
          (xiEvenShiftPrimeCorrectionAllValuation (grade a))) = _
  exact differentialFamilyMatroid_addBase_eq _ _

private theorem affinePointedCollisionMatroid_double
    {A : Type*} (grade : A → ℕ) :
    affinePointedCollisionMatroid (fun a ↦ 2 * grade a) 0 =
      affinePointedCollisionMatroid grade 0 := by
  apply Matroid.ext_indep
  · simp
  · intro I _
    rw [affinePointedCollisionMatroid_indep_iff,
      affinePointedCollisionMatroid_indep_iff]
    constructor
    · rintro ⟨hinj, hnonzero⟩
      refine ⟨?_, ?_⟩
      · intro i hi j hj hij
        exact hinj hi hj (congrArg (fun n ↦ 2 * n) hij)
      · intro i hi hzero
        exact hnonzero i hi (by simp [hzero])
    · rintro ⟨hinj, hnonzero⟩
      refine ⟨?_, ?_⟩
      · intro i hi j hj hij
        exact hinj hi hj (Nat.eq_of_mul_eq_mul_left (by norm_num) hij)
      · intro i hi
        exact mul_ne_zero (by norm_num) (hnonzero i hi)

/-- **Raw all-valuation collision law.** The exact raw completed-Xi family matroid survives after
adjoining every scalar prime-valuation layer. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision
    {A : Type*} (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun a ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade a)) =
      affinePointedCollisionMatroid grade 0 := by
  rw [xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialMatroid_eq_corrected]
  change differentialFamilyMatroid
      (F := analyticScalarValuationLayerDifferentialField)
      (fun a ↦ xiTransverseShiftUpperEndCarrier (2 * grade a)) = _
  rw [xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_double]

/-- Exact all-valuation Prop interface for raw even completed-Xi packets. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialIndependent_iff
    {A : Type*} (grade : A → ℕ) (I : Set A) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun i : I ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) ↔
      Set.InjOn grade I ∧ ∀ i ∈ I, grade i ≠ 0 := by
  let x := fun a ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade a)
  rw [← differentialFamilyMatroid_indep_iff x I,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_indep_iff]

/-- Exact all-valuation rank of every raw even completed-Xi packet. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialMatroid_eRk
    {A : Type*} (grade : A → ℕ) (I : Set A) :
    (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun a ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade a))).eRk I =
      ((grade '' I) ∩ {m | m ≠ 0}).encard := by
  rw [xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_eRk]

/-! ## Arbitrary-label pairwise collision quotient -/

/-- Raw even completed-Xi values at every occupied nonzero grade of an arbitrary family are
jointly differentially independent over the rational coordinate field. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_pointedOccupiedLabelSupport_differentialIndependent
    {V : Type} (grade : V → ℕ) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun q : pointedOccupiedLabelSupport grade 0 ↦
        xiEvenShiftRawLogDerivDefectUpperEndCarrier q) := by
  let support := pointedOccupiedLabelSupport grade 0
  have hfull : DifferentialIndependent upperEndRationalCoordinateField
      (fun i : ↑(Set.univ : Set support) ↦
        xiEvenShiftRawLogDerivDefectUpperEndCarrier (i : support)) := by
    apply (xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialIndependent_iff
      (fun q : support ↦ (q : ℕ)) Set.univ).2
    constructor
    · intro i _ j _ hij
      exact Subtype.ext hij
    · intro q _
      exact q.property.2
  let embed : support → ↑(Set.univ : Set support) := fun q ↦ ⟨q, Set.mem_univ q⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    exact congrArg Subtype.val hij
  simpa only [support, embed] using hfull.comp embed hembed

/-- The arbitrary occupied nonzero raw even-shift family remains jointly differentially
independent over the complete scalar valuation-layer field. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_pointedOccupiedLabelSupport_differentialIndependent
    {V : Type} (grade : V → ℕ) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun q : pointedOccupiedLabelSupport grade 0 ↦
        xiEvenShiftRawLogDerivDefectUpperEndCarrier q) := by
  let support := pointedOccupiedLabelSupport grade 0
  have hfull : DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun i : ↑(Set.univ : Set support) ↦
        xiEvenShiftRawLogDerivDefectUpperEndCarrier (i : support)) := by
    apply
      (xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialIndependent_iff
        (fun q : support ↦ (q : ℕ)) Set.univ).2
    constructor
    · intro i _ j _ hij
      exact Subtype.ext hij
    · intro q _
      exact q.property.2
  let embed : support → ↑(Set.univ : Set support) := fun q ↦ ⟨q, Set.mem_univ q⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    exact congrArg Subtype.val hij
  simpa only [support, embed] using hfull.comp embed hembed

/-- Raw even completed-Xi values at the occupied nonzero grades are jointly differentially
independent over the rational coordinate field. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_pointedCollisionSupport_differentialIndependent
    {V : Type} [Fintype V] (grade : V → ℕ) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun q : pointedCollisionIncidenceSupport grade 0 ↦
        xiEvenShiftRawLogDerivDefectUpperEndCarrier q) := by
  let support := pointedCollisionIncidenceSupport grade 0
  have hfull : DifferentialIndependent upperEndRationalCoordinateField
      (fun i : ↑(Set.univ : Set ↑support) ↦
        xiEvenShiftRawLogDerivDefectUpperEndCarrier (i : ↑support)) := by
    apply (xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialIndependent_iff
      (fun q : ↑support ↦ (q : ℕ)) Set.univ).2
    constructor
    · intro i _ j _ hij
      exact Subtype.ext hij
    · intro q _
      exact (Finset.mem_erase.mp q.property).1
  let embed : ↑support → ↑(Set.univ : Set ↑support) := fun q ↦ ⟨q, Set.mem_univ q⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    exact congrArg Subtype.val hij
  simpa only [support, embed] using hfull.comp embed hembed

/-- Raw even completed-Xi values at the occupied nonzero grades remain jointly differentially
independent over the complete scalar valuation-layer field. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_pointedCollisionSupport_differentialIndependent
    {V : Type} [Fintype V] (grade : V → ℕ) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun q : pointedCollisionIncidenceSupport grade 0 ↦
        xiEvenShiftRawLogDerivDefectUpperEndCarrier q) := by
  let support := pointedCollisionIncidenceSupport grade 0
  have hfull : DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun i : ↑(Set.univ : Set ↑support) ↦
        xiEvenShiftRawLogDerivDefectUpperEndCarrier (i : ↑support)) := by
    apply
      (xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialIndependent_iff
        (fun q : ↑support ↦ (q : ℕ)) Set.univ).2
    constructor
    · intro i _ j _ hij
      exact Subtype.ext hij
    · intro q _
      exact (Finset.mem_erase.mp q.property).1
  let embed : ↑support → ↑(Set.univ : Set ↑support) := fun q ↦ ⟨q, Set.mem_univ q⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    exact congrArg Subtype.val hij
  simpa only [support, embed] using hfull.comp embed hembed

/-- **Exact raw-Xi common-mode classifier.** For every finite inhabited grade family, including
repetitions, all ordered pairwise raw completed-Xi differences recover the vertex field over the
rational coordinate base exactly when grade zero occurs. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_vertices_iff_zero_mem_range
    {V : Type} (anchor : V) (grade : V → ℕ) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade Prod.snd Prod.fst)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) ↔
      0 ∈ Set.range grade := by
  have hx :=
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_pointedOccupiedLabelSupport_differentialIndependent
      grade
  change
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun p : V × V ↦
          xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade p.1) -
            xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade p.2)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) ↔
      0 ∈ Set.range grade
  exact differentialAdjoin_range_gradedPairwiseDifferences_eq_iff_loop_mem_range_arbitrary
    (F := upperEndRationalCoordinateField) (K := upperEndMeroField)
    (V := V) (L := ℕ) anchor grade 0
    xiEvenShiftRawLogDerivDefectUpperEndCarrier
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_zero hx

/-- The exact raw-Xi common-mode classifier remains true after adjoining every scalar valuation
layer to the differential base. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_vertices_iff_zero_mem_range
    {V : Type} (anchor : V) (grade : V → ℕ) :
    differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade Prod.snd Prod.fst)) =
      differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) ↔
      0 ∈ Set.range grade := by
  have hx :=
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_pointedOccupiedLabelSupport_differentialIndependent
      grade
  change
    differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun p : V × V ↦
          xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade p.1) -
            xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade p.2)) =
      differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) ↔
      0 ∈ Set.range grade
  exact differentialAdjoin_range_gradedPairwiseDifferences_eq_iff_loop_mem_range_arbitrary
    (F := analyticScalarValuationLayerDifferentialField) (K := upperEndMeroField)
    (V := V) (L := ℕ) anchor grade 0
    xiEvenShiftRawLogDerivDefectUpperEndCarrier
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_zero hx

/-- **Exact raw pairwise source-recovery threshold.** The complete raw pairwise reporter recovers
the full corrected even-shift prime-source field over the rational coordinate base exactly when
grade zero occurs. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_corrected_iff_zero_mem_range
    {V : Type} (anchor : V) (grade : V → ℕ) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade Prod.snd Prod.fst)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun v ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade v)) ↔
      0 ∈ Set.range grade := by
  rw [← xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialAdjoin_eq_corrected grade]
  exact
    xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_vertices_iff_zero_mem_range
      anchor grade

/-- The exact raw pairwise source-recovery threshold remains true over the full scalar
valuation-layer base. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_corrected_iff_zero_mem_range
    {V : Type} (anchor : V) (grade : V → ℕ) :
    differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade Prod.snd Prod.fst)) =
      differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun v ↦ xiEvenShiftPrimeDefectUpperEndCarrier (grade v)) ↔
      0 ∈ Set.range grade := by
  rw [←
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialAdjoin_eq_corrected
      grade]
  exact
    xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_vertices_iff_zero_mem_range
      anchor grade

/-- **Arbitrary-label raw-Xi incidence law.** Pairwise raw even completed-Xi differences represent
the occupied-grade collision-quotient incidence matroid over the rational coordinate field, with
no root, injectivity, or positivity hypothesis. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialMatroid_eq_pointedCollisionIncidenceMatroid
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) =
      pointedCollisionIncidenceMatroid
        (C := upperEndRationalCoordinateField) grade 0 tail head := by
  have hx :=
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_pointedCollisionSupport_differentialIndependent
      grade
  simpa [xiEvenShiftRawPairDifferenceUpperEndCarrier] using
    (differentialFamilyMatroid_gradedPairwiseDifferences_eq_pointedCollisionIncidenceMatroid
      (C := upperEndRationalCoordinateField) grade 0 tail head
      xiEvenShiftRawLogDerivDefectUpperEndCarrier
      xiEvenShiftRawLogDerivDefectUpperEndCarrier_zero hx)

/-- Abstract Prop interface for every packet of an arbitrary-label raw-Xi edge family. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_iff_pointedCollisionIncidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) (I : Set E) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun e : I ↦ xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head e) ↔
      (pointedCollisionIncidenceMatroid
        (C := upperEndRationalCoordinateField) grade 0 tail head).Indep I := by
  let y := xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head
  rw [← differentialFamilyMatroid_indep_iff y I,
    xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialMatroid_eq_pointedCollisionIncidenceMatroid]

/-- Full occupied-grade quotient Kirchhoff interface for raw Xi over the rational coordinate
field. The collapsed zero-grade equation is included and discharged by total incidence. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_finset_iff_pointedCollisionVertexConservation
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) (I : Finset E) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun e : ↑(↑I : Set E) ↦
          xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head e) ↔
      ∀ weight : ↑(↑I : Set E) → upperEndRationalCoordinateField,
        (∀ q : pointedCollisionIncidenceVertex grade 0,
          (∑ e : ↑(↑I : Set E),
              if pointedCollisionIncidenceVertexOf grade 0
                (head (e : E)) = q then weight e else 0) =
            ∑ e : ↑(↑I : Set E),
              if pointedCollisionIncidenceVertexOf grade 0
                (tail (e : E)) = q then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_iff_pointedCollisionIncidence
      grade tail head (↑I : Set E),
    pointedCollisionIncidenceMatroid_indep_iff_vertex_conservation]

/-- Exact rational-base differential rank after collapsing repeated raw even-shift grades. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_pointedCollisionIncidence_eRk
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) (I : Set E) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head)).eRk I =
      (pointedCollisionIncidenceMatroid
        (C := upperEndRationalCoordinateField) grade 0 tail head).eRk I := by
  rw [xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialMatroid_eq_pointedCollisionIncidenceMatroid]

/-- The arbitrary-label raw-Xi incidence law remains exact over the complete scalar valuation-layer
base. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollisionIncidenceMatroid
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) =
      pointedCollisionIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) grade 0 tail head := by
  have hx :=
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_pointedCollisionSupport_differentialIndependent
      grade
  simpa [xiEvenShiftRawPairDifferenceUpperEndCarrier] using
    (differentialFamilyMatroid_gradedPairwiseDifferences_eq_pointedCollisionIncidenceMatroid
      (C := analyticScalarValuationLayerDifferentialField) grade 0 tail head
      xiEvenShiftRawLogDerivDefectUpperEndCarrier
      xiEvenShiftRawLogDerivDefectUpperEndCarrier_zero hx)

/-- All-valuation abstract Prop interface for arbitrary-label raw-Xi edge packets. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff_pointedCollisionIncidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) (I : Set E) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun e : I ↦ xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head e) ↔
      (pointedCollisionIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) grade 0 tail head).Indep I := by
  let y := xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head
  rw [← differentialFamilyMatroid_indep_iff y I,
    xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollisionIncidenceMatroid]

/-- Full occupied-grade quotient Kirchhoff interface for raw Xi over the all-valuation base. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_finset_iff_pointedCollisionVertexConservation
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) (I : Finset E) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun e : ↑(↑I : Set E) ↦
          xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head e) ↔
      ∀ weight : ↑(↑I : Set E) → analyticScalarValuationLayerDifferentialField,
        (∀ q : pointedCollisionIncidenceVertex grade 0,
          (∑ e : ↑(↑I : Set E),
              if pointedCollisionIncidenceVertexOf grade 0
                (head (e : E)) = q then weight e else 0) =
            ∑ e : ↑(↑I : Set E),
              if pointedCollisionIncidenceVertexOf grade 0
                (tail (e : E)) = q then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff_pointedCollisionIncidence
      grade tail head (↑I : Set E),
    pointedCollisionIncidenceMatroid_indep_iff_vertex_conservation]

/-- Exact all-valuation differential rank after collapsing repeated raw even-shift grades. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_pointedCollisionIncidence_eRk
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) (I : Set E) :
    (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head)).eRk I =
      (pointedCollisionIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) grade 0 tail head).eRk I := by
  rw [xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollisionIncidenceMatroid]

/-! ## Incidence matroid of pairwise even translates -/

/-- **Pairwise raw completed-Xi incidence law.** Fix a zero-grade root and distinct vertex grades.
For every finite oriented edge family, the pairwise differences between raw even completed-Xi
translates represent exactly the rooted incidence matroid over the rational coordinate field. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (grade : V → ℕ) (hroot : grade root = 0)
    (hinj : Function.Injective grade) (tail head : E → V) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) =
      rootedIncidenceMatroid
        (C := upperEndRationalCoordinateField) root tail head := by
  have hx0 : xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade root) = 0 := by
    rw [hroot, xiEvenShiftRawLogDerivDefectUpperEndCarrier_zero]
  have hx : DifferentialIndependent upperEndRationalCoordinateField
      (fun v : ↑({v | v ≠ root} : Set V) ↦
        xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) := by
    have hxSet : DifferentialIndependent upperEndRationalCoordinateField
        (fun v : ↑({v | v ≠ root} : Set V) ↦
          xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) := by
      apply (xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialIndependent_iff
        grade {v | v ≠ root}).2
      refine ⟨?_, ?_⟩
      · intro i _ j _ hij
        exact hinj hij
      · intro v hv hzero
        exact hv (hinj (hzero.trans hroot.symm))
    exact hxSet
  simpa [xiEvenShiftRawPairDifferenceUpperEndCarrier] using
    (differentialFamilyMatroid_pairwiseDifferences_eq_rootedIncidenceMatroid
      (C := upperEndRationalCoordinateField) root tail head
      (fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) hx0 hx)

/-- Prop interface for every selected rational-base edge packet. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_iff
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (grade : V → ℕ) (hroot : grade root = 0)
    (hinj : Function.Injective grade) (tail head : E → V) (I : Set E) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun e : I ↦ xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head e) ↔
      (rootedIncidenceMatroid
        (C := upperEndRationalCoordinateField) root tail head).Indep I := by
  let y := xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head
  rw [← differentialFamilyMatroid_indep_iff y I,
    xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid
      root grade hroot hinj tail head]

/-- **Kirchhoff Prop interface for raw Xi translate differences.** A finite packet of pairwise raw
even completed-Xi differences is differentially independent over the rational coordinate field
exactly when every conserved coefficient circulation on that packet is zero. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_finset_iff_vertexConservation
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (grade : V → ℕ) (hroot : grade root = 0)
    (hinj : Function.Injective grade) (tail head : E → V) (I : Finset E) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun e : ↑(↑I : Set E) ↦
          xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head e) ↔
      ∀ weight : ↑(↑I : Set E) → upperEndRationalCoordinateField,
        (∀ v : V,
          (∑ e : ↑(↑I : Set E),
              if head (e : E) = v then weight e else 0) =
            ∑ e : ↑(↑I : Set E),
              if tail (e : E) = v then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_iff
      root grade hroot hinj tail head (↑I : Set E),
    rootedIncidenceMatroid_indep_iff_vertex_conservation]

/-- Exact rational-base differential rank of every pairwise edge packet. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialMatroid_eRk
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (grade : V → ℕ) (hroot : grade root = 0)
    (hinj : Function.Injective grade) (tail head : E → V) (I : Set E) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head)).eRk
          I =
      (rootedIncidenceMatroid
        (C := upperEndRationalCoordinateField) root tail head).eRk I := by
  rw [xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid
    root grade hroot hinj tail head]

/-- **All-valuation pairwise incidence law.** The same exact incidence matroid survives after
adjoining every scalar prime-valuation layer. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (grade : V → ℕ) (hroot : grade root = 0)
    (hinj : Function.Injective grade) (tail head : E → V) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) =
      rootedIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) root tail head := by
  have hx0 : xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade root) = 0 := by
    rw [hroot, xiEvenShiftRawLogDerivDefectUpperEndCarrier_zero]
  have hx : DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun v : ↑({v | v ≠ root} : Set V) ↦
        xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) := by
    have hxSet : DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun v : ↑({v | v ≠ root} : Set V) ↦
          xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) := by
      apply
        (xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialIndependent_iff
          grade {v | v ≠ root}).2
      refine ⟨?_, ?_⟩
      · intro i _ j _ hij
        exact hinj hij
      · intro v hv hzero
        exact hv (hinj (hzero.trans hroot.symm))
    exact hxSet
  simpa [xiEvenShiftRawPairDifferenceUpperEndCarrier] using
    (differentialFamilyMatroid_pairwiseDifferences_eq_rootedIncidenceMatroid
      (C := analyticScalarValuationLayerDifferentialField) root tail head
      (fun v ↦ xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade v)) hx0 hx)

/-- Prop interface for every selected all-valuation edge packet. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (grade : V → ℕ) (hroot : grade root = 0)
    (hinj : Function.Injective grade) (tail head : E → V) (I : Set E) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun e : I ↦ xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head e) ↔
      (rootedIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) root tail head).Indep I := by
  let y := xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head
  rw [← differentialFamilyMatroid_indep_iff y I,
    xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid
      root grade hroot hinj tail head]

/-- All-valuation Kirchhoff interface for every finite packet of raw Xi translate differences. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_finset_iff_vertexConservation
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (grade : V → ℕ) (hroot : grade root = 0)
    (hinj : Function.Injective grade) (tail head : E → V) (I : Finset E) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun e : ↑(↑I : Set E) ↦
          xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head e) ↔
      ∀ weight : ↑(↑I : Set E) → analyticScalarValuationLayerDifferentialField,
        (∀ v : V,
          (∑ e : ↑(↑I : Set E),
              if head (e : E) = v then weight e else 0) =
            ∑ e : ↑(↑I : Set E),
              if tail (e : E) = v then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff
      root grade hroot hinj tail head (↑I : Set E),
    rootedIncidenceMatroid_indep_iff_vertex_conservation]

/-- Exact all-valuation differential rank of every pairwise edge packet. -/
theorem xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eRk
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (grade : V → ℕ) (hroot : grade root = 0)
    (hinj : Function.Injective grade) (tail head : E → V) (I : Set E) :
    (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head)).eRk
          I =
      (rootedIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) root tail head).eRk I := by
  rw [xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid
    root grade hroot hinj tail head]

end

end RHTower
