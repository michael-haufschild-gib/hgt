import GaloisForLFunctions.HTGeometry.HerglotzFiniteAtomicUpperEnd
import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroidBaseGauge
import GaloisForLFunctions.HTGeometry.DifferentialObservableGaugeInvariance

/-!
# Full-translation invariance of finite-atomic Herglotz chambers

Finite signed atom surgery changes every translated regularized Herglotz carrier by an element of
the translated rational-coordinate field.  Consequently the complete translation family has the
same generated differential field, represented differential matroid, independence predicate, and
generator class modulo the rational coordinate field in every chamber.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Filter Topology MeasureTheory
open scoped Differential

noncomputable section

local instance herglotzOrbitDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance herglotzOrbitComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance herglotzOrbitCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance herglotzOrbitDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance herglotzOrbitCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance herglotzOrbitCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField :=
  ⟨fun x => derivationClosedDifferential_apply
    upperEndRationalCoordinateField
    upperEndRationalCoordinateField_derivationClosed x⟩

/-- Finite atom correction as an element of the concrete rational-coordinate intermediate field. -/
def finiteAtomGaugeCoordinateField {d : ℕ} (a c : Fin d → ℝ) :
    upperEndRationalCoordinateField :=
  upperEndRatfuncToRationalCoordinateField (finiteAtomGaugeRatFunc a c)

/-- Full complex translation orbit of the regularized Herglotz carrier. -/
def regularizedH0TranslateFamily (nu : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight nu) (h : ℂ) : upperEndMeroField :=
  upperEndTranslationMeroEquiv h (regularizedH0UpperEndMero nu hH0)

/-- Full complex translation orbit of a finite-atomic chamber member. -/
def chamberHerglotzTranslateFamily {d : ℕ} (nu : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight nu) (a c : Fin d → ℝ)
    (h : ℂ) : upperEndMeroField :=
  upperEndTranslationMeroEquiv h
    (chamberHerglotzUpperEndMero nu hH0 a c)

/-- Translation of the rational atom correction inside the normalized rational-coordinate
field. -/
def finiteAtomGaugeTranslateFamily {d : ℕ} (a c : Fin d → ℝ)
    (h : ℂ) : upperEndRationalCoordinateField :=
  upperEndRationalCoordinateTranslationAlgEquiv h
    (finiteAtomGaugeCoordinateField a c)

/-- Every translated chamber member is the corresponding translated base carrier plus a translated
rational-coordinate-field element. -/
theorem chamberHerglotzTranslateFamily_eq_add_rational
    {d : ℕ} (nu : Measure ℝ) (hH0 : Integrable nevanlinnaWeight nu)
    (a c : Fin d → ℝ) (h : ℂ) :
    chamberHerglotzTranslateFamily nu hH0 a c h =
      regularizedH0TranslateFamily nu hH0 h +
        algebraMap upperEndRationalCoordinateField upperEndMeroField
          (finiteAtomGaugeTranslateFamily a c h) := by
  rw [chamberHerglotzTranslateFamily, regularizedH0TranslateFamily,
    chamberHerglotzUpperEndMero_eq_add_finiteAtomGauge, map_add]
  congr 1

/-- Finite atom surgery preserves differential independence of every finite or infinite subfamily
of the full complex translation orbit. -/
theorem chamberHerglotzTranslateFamily_differentialIndependent_iff
    {d : ℕ} (nu : Measure ℝ) (hH0 : Integrable nevanlinnaWeight nu)
    (a c : Fin d → ℝ) :
    DifferentialIndependent upperEndRationalCoordinateField
        (chamberHerglotzTranslateFamily nu hH0 a c) ↔
      DifferentialIndependent upperEndRationalCoordinateField
        (regularizedH0TranslateFamily nu hH0) := by
  rw [show chamberHerglotzTranslateFamily nu hH0 a c =
      fun h => regularizedH0TranslateFamily nu hH0 h +
        algebraMap upperEndRationalCoordinateField upperEndMeroField
          (finiteAtomGaugeTranslateFamily a c h) by
    funext h
    exact chamberHerglotzTranslateFamily_eq_add_rational nu hH0 a c h]
  exact differentialIndependent_addBase_iff
    (regularizedH0TranslateFamily nu hH0) (finiteAtomGaugeTranslateFamily a c)

/-- Finite atom surgery preserves the entire represented differential matroid of the full complex
translation family. -/
theorem chamberHerglotzTranslateFamily_differentialFamilyMatroid_eq
    {d : ℕ} (nu : Measure ℝ) (hH0 : Integrable nevanlinnaWeight nu)
    (a c : Fin d → ℝ) :
    differentialFamilyMatroid (F := upperEndRationalCoordinateField)
        (chamberHerglotzTranslateFamily nu hH0 a c) =
      differentialFamilyMatroid (F := upperEndRationalCoordinateField)
        (regularizedH0TranslateFamily nu hH0) := by
  rw [show chamberHerglotzTranslateFamily nu hH0 a c =
      fun h => regularizedH0TranslateFamily nu hH0 h +
        algebraMap upperEndRationalCoordinateField upperEndMeroField
          (finiteAtomGaugeTranslateFamily a c h) by
    funext h
    exact chamberHerglotzTranslateFamily_eq_add_rational nu hH0 a c h]
  exact differentialFamilyMatroid_addBase_eq
    (regularizedH0TranslateFamily nu hH0) (finiteAtomGaugeTranslateFamily a c)

/-- Every finite-atomic chamber member generates exactly the same embedded full-translation
differential field as its regularized Herglotz base carrier. -/
theorem chamberHerglotzTranslateFamily_differentialAdjoin_eq
    {d : ℕ} (nu : Measure ℝ) (hH0 : Integrable nevanlinnaWeight nu)
    (a c : Fin d → ℝ) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range (chamberHerglotzTranslateFamily nu hH0 a c)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range (regularizedH0TranslateFamily nu hH0)) := by
  rw [show chamberHerglotzTranslateFamily nu hH0 a c =
      fun h => regularizedH0TranslateFamily nu hH0 h +
        algebraMap upperEndRationalCoordinateField upperEndMeroField
          (finiteAtomGaugeTranslateFamily a c h) by
    funext h
    exact chamberHerglotzTranslateFamily_eq_add_rational nu hH0 a c h]
  simpa using differentialAdjoin_range_affineBase_eq
    (regularizedH0TranslateFamily nu hH0) (fun _ : ℂ => 1)
      (finiteAtomGaugeTranslateFamily a c) (fun _ => one_ne_zero)

/-- Additive quotient by the embedded rational coordinate field. -/
abbrev upperEndMeroModuloRationalCoordinate :=
  upperEndMeroField ⧸ upperEndRationalCoordinateField.toSubring.toAddSubgroup

/-- A carrier's generator class modulo the embedded rational coordinate field. -/
def upperEndRationalGaugeClass (x : upperEndMeroField) :
    upperEndMeroModuloRationalCoordinate :=
  QuotientAddGroup.mk x

/-- Every corresponding translated generator has the same additive class modulo `ℂ(z)`. -/
theorem chamberHerglotzTranslateFamily_rationalGaugeClass_eq
    {d : ℕ} (nu : Measure ℝ) (hH0 : Integrable nevanlinnaWeight nu)
    (a c : Fin d → ℝ) (h : ℂ) :
    upperEndRationalGaugeClass (chamberHerglotzTranslateFamily nu hH0 a c h) =
      upperEndRationalGaugeClass (regularizedH0TranslateFamily nu hH0 h) := by
  change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  rw [QuotientAddGroup.eq_iff_sub_mem,
    chamberHerglotzTranslateFamily_eq_add_rational, add_sub_cancel_left]
  exact (finiteAtomGaugeTranslateFamily a c h).property

/-- **Complete measure-level finite-atomic chamber law.**  One theorem packages the exact claims:
same embedded full-translation differential field, same represented differential matroid, same
generator class modulo the rational coordinate field at every shift, and exact Hamming/Krein index
at the literal Pick kernel. -/
theorem finiteAtomicHerglotzChamber_complete
    {d : ℕ} (nu : Measure ℝ) (hH0 : Integrable nevanlinnaWeight nu)
    (a c : Fin d → ℝ) (ha : Function.Injective a)
    (hatom : ∀ j, nu {a j} = 0) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range (chamberHerglotzTranslateFamily nu hH0 a c)) =
        differentialAdjoin upperEndRationalCoordinateField
          (Set.range (regularizedH0TranslateFamily nu hH0)) ∧
      differentialFamilyMatroid (F := upperEndRationalCoordinateField)
          (chamberHerglotzTranslateFamily nu hH0 a c) =
        differentialFamilyMatroid (F := upperEndRationalCoordinateField)
          (regularizedH0TranslateFamily nu hH0) ∧
      (∀ h : ℂ,
        upperEndRationalGaugeClass (chamberHerglotzTranslateFamily nu hH0 a c h) =
          upperEndRationalGaugeClass (regularizedH0TranslateFamily nu hH0 h)) ∧
      ∀ᶠ y : ℝ in 𝓝[≠] 0,
        (∀ W : Submodule ℂ (Fin d → ℂ),
            (∀ x ∈ W, x ≠ 0 →
              (star x ⬝ᵥ (chamberPickKernel nu a c y).mulVec x).re < 0) →
            Module.finrank ℂ W ≤ hammingDist (signPattern c) (positiveChamber d)) ∧
          Module.finrank ℂ (negSupported c) =
            hammingDist (signPattern c) (positiveChamber d) := by
  exact ⟨chamberHerglotzTranslateFamily_differentialAdjoin_eq nu hH0 a c,
    chamberHerglotzTranslateFamily_differentialFamilyMatroid_eq nu hH0 a c,
    chamberHerglotzTranslateFamily_rationalGaugeClass_eq nu hH0 a c,
    chamberLaw_herglotzMeasure nu hH0 a c ha hatom⟩

/-- No function of the unpointed generator class modulo `ℂ(z)` can recover the exact chamber
grading, already in a one-atom fiber. -/
theorem no_negCount_selector_of_rationalGaugeClass
    (nu : Measure ℝ) (hH0 : Integrable nevanlinnaWeight nu) (a : Fin 1 → ℝ) :
    ¬ ∃ S : upperEndMeroModuloRationalCoordinate → ℕ,
      ∀ c : Fin 1 → ℝ,
        S (upperEndRationalGaugeClass
          (chamberHerglotzTranslateFamily nu hH0 a c 0)) = negCount c := by
  rintro ⟨S, hS⟩
  let c0 : Fin 1 → ℝ := fun _ => 0
  let cneg : Fin 1 → ℝ := fun _ => -1
  have hclass :
      upperEndRationalGaugeClass
          (chamberHerglotzTranslateFamily nu hH0 a c0 0) =
        upperEndRationalGaugeClass
          (chamberHerglotzTranslateFamily nu hH0 a cneg 0) :=
    (chamberHerglotzTranslateFamily_rationalGaugeClass_eq nu hH0 a c0 0).trans
      (chamberHerglotzTranslateFamily_rationalGaugeClass_eq nu hH0 a cneg 0).symm
  have hcount : negCount c0 = negCount cneg := by
    rw [← hS c0, ← hS cneg, hclass]
  simp [negCount, c0, cneg] at hcount

end

end GaloisForLFunctions.HTGeometry
