import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary
import GaloisForLFunctions.HTGeometry.PhysicalCharacteristicIncidence

/-!
# Meromorphic realization of physical characteristic incidence

The exponential mode is constructed inside the genuine global meromorphic field.  Translation
defects on that element have exactly the scalar characters used by the DA logarithmic
characteristic arrangement.  Hence the DA physical boundary and the meromorphic source boundary
are two literal realizations of the same coface symbol, not merely analogous formulas.
-/

open Filter Set
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance meromorphicPhysicalIncidenceDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicPhysicalIncidenceComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance meromorphicPhysicalIncidenceComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance meromorphicPhysicalIncidenceDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- The physical exponential mode as a genuine global analytic germ. -/
def physicalExponentialAnalytic (lambda : ℂ) :
    analyticSubring (Set.univ : Set ℂ) :=
  ⟨(fun z : ℂ ↦ Complex.exp (lambda * z) : Germ (Filter.principal Set.univ) ℂ),
    ⟨fun z : ℂ ↦ Complex.exp (lambda * z),
      (analyticOnNhd_const.mul analyticOnNhd_id).cexp, rfl⟩⟩

@[simp] theorem univGermEval_physicalExponentialAnalytic
    (lambda z : ℂ) :
    univGermEval z
        (physicalExponentialAnalytic lambda :
          Germ (Filter.principal Set.univ) ℂ) =
      Complex.exp (lambda * z) := by
  rfl

/-- Translation of the analytic exponential mode is multiplication by its source character. -/
theorem addTranslationAnalyticEquiv_physicalExponentialAnalytic
    (tau lambda : ℂ) :
    addTranslationAnalyticEquiv tau (physicalExponentialAnalytic lambda) =
      constToAnalytic Set.univ (Complex.exp (lambda * tau)) *
        physicalExponentialAnalytic lambda := by
  apply Subtype.ext
  apply univGerm_ext
  intro z
  rw [univGermEval_addTranslationAnalyticEquiv,
    univGermEval_analyticSubring_mul]
  simp only [univGermEval_physicalExponentialAnalytic]
  change Complex.exp (lambda * (z + tau)) =
    Complex.exp (lambda * tau) * Complex.exp (lambda * z)
  rw [show lambda * (z + tau) = lambda * tau + lambda * z by ring,
    Complex.exp_add]

/-- The physical exponential mode inside the global meromorphic fraction field. -/
def physicalExponentialMero (lambda : ℂ) :
    meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (physicalExponentialAnalytic lambda)

theorem physicalExponentialAnalytic_ne_zero (lambda : ℂ) :
    physicalExponentialAnalytic lambda ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun a : analyticSubring (Set.univ : Set ℂ) ↦
      univGermEval 0 (a : Germ (Filter.principal Set.univ) ℂ)) hzero
  norm_num at h

theorem physicalExponentialMero_ne_zero (lambda : ℂ) :
    physicalExponentialMero lambda ≠ 0 := by
  intro hzero
  apply physicalExponentialAnalytic_ne_zero lambda
  apply IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ)
  simpa [physicalExponentialMero] using hzero

/-- Translation of the genuine meromorphic exponential mode has the same source character. -/
theorem addTranslationMeroEquiv_physicalExponentialMero
    (tau lambda : ℂ) :
    addTranslationMeroEquiv tau (physicalExponentialMero lambda) =
      algebraMap ℂ (meroField Set.univ) (Complex.exp (lambda * tau)) *
        physicalExponentialMero lambda := by
  rw [physicalExponentialMero, addTranslationMeroEquiv_algebraMap,
    addTranslationAnalyticEquiv_physicalExponentialAnalytic, map_mul]
  rfl

/-- A genuine meromorphic translation defect diagonalizes with the DA source coordinate. -/
theorem meromorphicTranslationDefect_physicalExponentialMero
    (tau lambda : ℂ) :
    addTranslationMeroEquiv tau (physicalExponentialMero lambda) -
        physicalExponentialMero lambda =
      algebraMap ℂ (meroField Set.univ)
          (Complex.exp (lambda * tau) - 1) *
        physicalExponentialMero lambda := by
  rw [addTranslationMeroEquiv_physicalExponentialMero, map_sub, map_one]
  ring

/-- The already formalized rank-three meromorphic boundary fingerprint restricts to the physical
source symbol on every exponential mode. -/
theorem rankThreeGenerator_boundaryFingerprint_physicalExponentialMero
    (v : Fin 3 → ℂ) (lambda : ℂ) (i : Fin 3) :
    (rankThreeGeneratorMeromorphicDifferenceDifferentialField v).boundaryFingerprint
        (physicalExponentialMero lambda) i =
      algebraMap ℂ (meroField Set.univ)
          (Complex.exp (lambda * v i) - 1) *
        physicalExponentialMero lambda := by
  exact meromorphicTranslationDefect_physicalExponentialMero (v i) lambda

/-- An ordered product of genuine meromorphic source-translation defects. -/
def iteratedMeromorphicTranslationDefect
    {ι : Type*} (tau : ι → ℂ) :
    List ι → meroField (Set.univ : Set ℂ) → meroField Set.univ
  | [], x => x
  | i :: indices, x =>
      addTranslationMeroEquiv (tau i)
          (iteratedMeromorphicTranslationDefect tau indices x) -
        iteratedMeromorphicTranslationDefect tau indices x

/-- Iterated meromorphic defects have the complete product source character on an exponential
mode. -/
theorem iteratedMeromorphicTranslationDefect_physicalExponentialMero
    {ι : Type*} (tau : ι → ℂ) (indices : List ι) (lambda : ℂ) :
    iteratedMeromorphicTranslationDefect tau indices
        (physicalExponentialMero lambda) =
      algebraMap ℂ (meroField Set.univ)
          (indices.map (fun i ↦ Complex.exp (lambda * tau i) - 1)).prod *
        physicalExponentialMero lambda := by
  induction indices with
  | nil => simp [iteratedMeromorphicTranslationDefect]
  | cons i indices ih =>
      simp only [iteratedMeromorphicTranslationDefect, ih, map_mul,
        List.map_cons, List.prod_cons]
      rw [show addTranslationMeroEquiv (tau i)
          (algebraMap ℂ (meroField Set.univ)
            (indices.map (fun j ↦ Complex.exp (lambda * tau j) - 1)).prod) =
          algebraMap ℂ (meroField Set.univ)
            (indices.map (fun j ↦ Complex.exp (lambda * tau j) - 1)).prod by
        change addTranslationMeroEquiv (tau i)
            (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
              (constToAnalytic Set.univ
                (indices.map
                  (fun j ↦ Complex.exp (lambda * tau j) - 1)).prod)) = _
        exact addTranslationMeroEquiv_const _ _,
        addTranslationMeroEquiv_physicalExponentialMero, map_sub, map_one]
      ring

/-- The physical coface boundary realized inside the genuine global meromorphic field. -/
def meromorphicPhysicalCofaceBoundary
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ)
    (i : Fin (r + 1)) : meroField (Set.univ : Set ℂ) :=
  iteratedMeromorphicTranslationDefect tau (Finset.univ.erase i).toList
    (physicalExponentialMero lambda)

theorem meromorphicPhysicalCofaceBoundary_eq_symbol_mul
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ)
    (i : Fin (r + 1)) :
    meromorphicPhysicalCofaceBoundary r tau lambda i =
      algebraMap ℂ (meroField Set.univ)
          (HTGeometry.physicalCofaceSymbol r tau lambda i) *
        physicalExponentialMero lambda := by
  simpa [meromorphicPhysicalCofaceBoundary, HTGeometry.physicalCofaceSymbol] using
    iteratedMeromorphicTranslationDefect_physicalExponentialMero tau
      (Finset.univ.erase i).toList lambda

/-- A meromorphic physical coface vanishes exactly when its DA scalar symbol vanishes. -/
theorem meromorphicPhysicalCofaceBoundary_eq_zero_iff_symbol_eq_zero
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ)
    (i : Fin (r + 1)) :
    meromorphicPhysicalCofaceBoundary r tau lambda i = 0 ↔
      HTGeometry.physicalCofaceSymbol r tau lambda i = 0 := by
  rw [meromorphicPhysicalCofaceBoundary_eq_symbol_mul]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hscalar | hmode
    · exact (map_eq_zero_iff (algebraMap ℂ (meroField Set.univ))
        (algebraMap ℂ (meroField Set.univ)).injective).mp hscalar
    · exact False.elim (physicalExponentialMero_ne_zero lambda hmode)
  · intro h
    rw [h, map_zero, zero_mul]

/-- **DA--meromorphic physical comparison.**  The DA logarithmic characteristic boundary and the
coface boundary formed by actual translations in the global meromorphic field agree on the
physical exponential family. -/
theorem multipleGammaPhysicalLogCharacteristicBoundary_iff_meromorphicBoundary
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ) :
    HTGeometry.MultipleGammaLogCharacteristicBoundary r
        (HTGeometry.physicalLogarithmicClock tau lambda) ↔
      ∀ i : Fin (r + 1),
        meromorphicPhysicalCofaceBoundary r tau lambda i = 0 := by
  change (∀ i : Fin (r + 1),
    HTGeometry.physicalCofaceSymbol r tau lambda i = 0) ↔ _
  constructor
  · intro h i
    exact (meromorphicPhysicalCofaceBoundary_eq_zero_iff_symbol_eq_zero
      r tau lambda i).2 (h i)
  · intro h i
    exact (meromorphicPhysicalCofaceBoundary_eq_zero_iff_symbol_eq_zero
      r tau lambda i).1 (h i)

/-- For a rationally independent source frame, the common DA/meromorphic physical degeneracy
spectrum consists exactly of the central character. -/
theorem multipleGammaMeromorphicPhysicalBoundary_iff_zero
    {r : ℕ} (hr : 1 ≤ r) (tau : Fin (r + 1) → ℂ)
    (htau : LinearIndependent ℚ tau) (lambda : ℂ) :
    (∀ i : Fin (r + 1),
      meromorphicPhysicalCofaceBoundary r tau lambda i = 0) ↔
      lambda = 0 := by
  rw [← multipleGammaPhysicalLogCharacteristicBoundary_iff_meromorphicBoundary,
    HTGeometry.multipleGammaPhysicalLogCharacteristicBoundary_iff_zero hr tau htau]

end

end GaloisForLFunctions
