import GaloisForLFunctions.HTGeometry.EntireFunctionField

/-!
# Globally presented meromorphic tensors on complex affine space

Mathlib's `Meromorphic` predicate has scalar complex domain.  A multiple
standard twist instead lives on `(Fin N → ℂ)`, and Kaczorowski--Perelli's
gamma-cleared formula has stronger, global data: an explicit quotient of two
entire functions.  This file records exactly that data and its function-level
meaning.

This is deliberately a *presentation* object.  It does not assert that every
locally meromorphic function on `ℂ^N` is a quotient of global entire functions,
nor does it supply a continuation for a multiple twist.  A continuation theorem
must construct a presentation and prove its initial-region agreement.

The affine-pullback denominator condition is essential: a nonzero entire
denominator may restrict to the zero function on an affine subspace contained
in its polar divisor.
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

open GaloisForLFunctions.HTGeometry

/-- An explicit globally meromorphic scalar tensor on `ℂ^N`, presented as a
quotient of entire functions with nonzero denominator. -/
structure MeromorphicTensorPresentation (N : ℕ) where
  numerator : entireSubring (Fin N → ℂ)
  denominator : entireSubring (Fin N → ℂ)
  denominator_ne_zero : denominator ≠ 0

namespace MeromorphicTensorPresentation

variable {N : ℕ}

/-- Function-level evaluation of an explicit meromorphic tensor presentation.
At polar points Lean's total division convention gives zero; all analytic
statements below are restricted to `regularSet`. -/
noncomputable def value (T : MeromorphicTensorPresentation N) : (Fin N → ℂ) → ℂ :=
  fun s => (T.numerator : (Fin N → ℂ) → ℂ) s / (T.denominator : (Fin N → ℂ) → ℂ) s

/-- Complement of the displayed denominator-zero set of a presentation.  It is
the domain on which this particular quotient presentation is manifestly
analytic; numerator zeros may make the actual meromorphic function regular at
additional points. -/
def regularSet (T : MeromorphicTensorPresentation N) : Set (Fin N → ℂ) :=
  {s | (T.denominator : (Fin N → ℂ) → ℂ) s ≠ 0}

/-- Algebraic fraction-field carrier of a presentation.  Unlike `value`, this
does not attempt partial pointwise evaluation. -/
noncomputable def toEntireField (T : MeromorphicTensorPresentation N) :
    EntireField (Fin N → ℂ) :=
  algebraMap (entireSubring (Fin N → ℂ)) (EntireField (Fin N → ℂ)) T.numerator /
    algebraMap (entireSubring (Fin N → ℂ)) (EntireField (Fin N → ℂ)) T.denominator

theorem numerator_analyticAt (T : MeromorphicTensorPresentation N) (s : Fin N → ℂ) :
    AnalyticAt ℂ (T.numerator : (Fin N → ℂ) → ℂ) s :=
  T.numerator.property s (mem_univ s)

theorem denominator_analyticAt (T : MeromorphicTensorPresentation N) (s : Fin N → ℂ) :
    AnalyticAt ℂ (T.denominator : (Fin N → ℂ) → ℂ) s :=
  T.denominator.property s (mem_univ s)

/-- A presentation's regular locus is open. -/
theorem isOpen_regularSet (T : MeromorphicTensorPresentation N) : IsOpen T.regularSet := by
  rw [regularSet]
  change IsOpen ((T.denominator : (Fin N → ℂ) → ℂ) ⁻¹' {z : ℂ | z ≠ 0})
  exact T.denominator.property.continuous.isOpen_preimage _ isOpen_ne

/-- The quotient is analytic at every regular point. -/
theorem analyticAt_value (T : MeromorphicTensorPresentation N) {s : Fin N → ℂ}
    (hs : s ∈ T.regularSet) : AnalyticAt ℂ T.value s := by
  change (T.denominator : (Fin N → ℂ) → ℂ) s ≠ 0 at hs
  exact (T.numerator_analyticAt s).div (T.denominator_analyticAt s) hs

/-- The quotient is analytic on its full regular locus. -/
theorem analyticOnNhd_value_regularSet (T : MeromorphicTensorPresentation N) :
    AnalyticOnNhd ℂ T.value T.regularSet := by
  change AnalyticOnNhd ℂ
    (fun s : Fin N → ℂ =>
      (T.numerator : (Fin N → ℂ) → ℂ) s / (T.denominator : (Fin N → ℂ) → ℂ) s)
    T.regularSet
  have hnum : AnalyticOnNhd ℂ (T.numerator : (Fin N → ℂ) → ℂ) T.regularSet :=
    (show AnalyticOnNhd ℂ (T.numerator : (Fin N → ℂ) → ℂ) Set.univ from
      T.numerator.property).mono (subset_univ T.regularSet)
  have hden : AnalyticOnNhd ℂ (T.denominator : (Fin N → ℂ) → ℂ) T.regularSet :=
    (show AnalyticOnNhd ℂ (T.denominator : (Fin N → ℂ) → ℂ) Set.univ from
      T.denominator.property).mono (subset_univ T.regularSet)
  exact hnum.div hden (fun _ hs => by
    change (T.denominator : (Fin N → ℂ) → ℂ) _ ≠ 0 at hs
    exact hs)

/-- Clearing the displayed denominator recovers the displayed numerator away
from its polar set. -/
theorem denominator_mul_value (T : MeromorphicTensorPresentation N) {s : Fin N → ℂ}
    (hs : s ∈ T.regularSet) :
    (T.denominator : (Fin N → ℂ) → ℂ) s * T.value s =
      (T.numerator : (Fin N → ℂ) → ℂ) s := by
  change (T.denominator : (Fin N → ℂ) → ℂ) s *
    ((T.numerator : (Fin N → ℂ) → ℂ) s / (T.denominator : (Fin N → ℂ) → ℂ) s) =
    (T.numerator : (Fin N → ℂ) → ℂ) s
  change (T.denominator : (Fin N → ℂ) → ℂ) s ≠ 0 at hs
  calc
    (T.denominator : (Fin N → ℂ) → ℂ) s *
        ((T.numerator : (Fin N → ℂ) → ℂ) s / (T.denominator : (Fin N → ℂ) → ℂ) s) =
      ((T.numerator : (Fin N → ℂ) → ℂ) s / (T.denominator : (Fin N → ℂ) → ℂ) s) *
        (T.denominator : (Fin N → ℂ) → ℂ) s := mul_comm _ _
    _ = (T.numerator : (Fin N → ℂ) → ℂ) s := div_mul_cancel₀ _ hs

/-- Nonzero globally means the regular locus has at least one point.  It does
not mean the denominator is nonzero at every point. -/
theorem regularSet_nonempty (T : MeromorphicTensorPresentation N) : T.regularSet.Nonempty := by
  by_contra h
  apply T.denominator_ne_zero
  apply Subtype.ext
  funext s
  change (T.denominator : (Fin N → ℂ) → ℂ) s = 0
  by_contra hs
  apply h
  refine ⟨s, ?_⟩
  change (T.denominator : (Fin N → ℂ) → ℂ) s ≠ 0
  exact hs

/-- The denominator remains nonzero after embedding into the field of fractions
of entire functions. -/
theorem denominator_toEntireField_ne_zero (T : MeromorphicTensorPresentation N) :
    algebraMap (entireSubring (Fin N → ℂ)) (EntireField (Fin N → ℂ)) T.denominator ≠ 0 := by
  intro h
  exact T.denominator_ne_zero
    (IsFractionRing.injective (entireSubring (Fin N → ℂ)) (EntireField (Fin N → ℂ)) (by
      simpa using h))

/-- Product of two explicit meromorphic tensor presentations. -/
noncomputable def product (S T : MeromorphicTensorPresentation N) :
    MeromorphicTensorPresentation N where
  numerator := S.numerator * T.numerator
  denominator := S.denominator * T.denominator
  denominator_ne_zero := mul_ne_zero S.denominator_ne_zero T.denominator_ne_zero

theorem value_product (S T : MeromorphicTensorPresentation N) (s : Fin N → ℂ) :
    (product S T).value s = S.value s * T.value s := by
  change
    ((S.numerator : (Fin N → ℂ) → ℂ) s * (T.numerator : (Fin N → ℂ) → ℂ) s) /
      ((S.denominator : (Fin N → ℂ) → ℂ) s * (T.denominator : (Fin N → ℂ) → ℂ) s) =
    ((S.numerator : (Fin N → ℂ) → ℂ) s / (S.denominator : (Fin N → ℂ) → ℂ) s) *
      ((T.numerator : (Fin N → ℂ) → ℂ) s / (T.denominator : (Fin N → ℂ) → ℂ) s)
  exact mul_div_mul_comm _ _ _ _

theorem regularSet_product (S T : MeromorphicTensorPresentation N) :
    (product S T).regularSet = S.regularSet ∩ T.regularSet := by
  ext s
  change
    (S.denominator : (Fin N → ℂ) → ℂ) s * (T.denominator : (Fin N → ℂ) → ℂ) s ≠ 0 ↔
      (S.denominator : (Fin N → ℂ) → ℂ) s ≠ 0 ∧
        (T.denominator : (Fin N → ℂ) → ℂ) s ≠ 0
  constructor
  · intro h
    exact ⟨fun hS => h (by rw [hS, zero_mul]), fun hT => h (by rw [hT, mul_zero])⟩
  · rintro ⟨hS, hT⟩
    exact mul_ne_zero hS hT

/-- Pull a presentation back along an affine map, when the pulled-back
denominator is provably not the zero entire function.  This condition cannot be
dropped: an affine image may lie entirely inside a polar divisor. -/
noncomputable def affinePullback {M N : ℕ} (T : MeromorphicTensorPresentation N)
    (L : (Fin M → ℂ) →L[ℂ] (Fin N → ℂ)) (b : Fin N → ℂ)
    (hden : (fun s : Fin M → ℂ => (T.denominator : (Fin N → ℂ) → ℂ) (L s + b)) ≠ 0) :
    MeromorphicTensorPresentation M where
  numerator := ⟨fun s => (T.numerator : (Fin N → ℂ) → ℂ) (L s + b), by
    change AnalyticOnNhd ℂ
      ((T.numerator : (Fin N → ℂ) → ℂ) ∘ fun s : Fin M → ℂ => L s + b) Set.univ
    exact (show AnalyticOnNhd ℂ (T.numerator : (Fin N → ℂ) → ℂ) Set.univ from
      T.numerator.property).comp
        ((L.analyticOnNhd Set.univ).add analyticOnNhd_const)
        (Set.mapsTo_univ _ _)⟩
  denominator := ⟨fun s => (T.denominator : (Fin N → ℂ) → ℂ) (L s + b), by
    change AnalyticOnNhd ℂ
      ((T.denominator : (Fin N → ℂ) → ℂ) ∘ fun s : Fin M → ℂ => L s + b) Set.univ
    exact (show AnalyticOnNhd ℂ (T.denominator : (Fin N → ℂ) → ℂ) Set.univ from
      T.denominator.property).comp
        ((L.analyticOnNhd Set.univ).add analyticOnNhd_const)
        (Set.mapsTo_univ _ _)⟩
  denominator_ne_zero := by
    intro h
    apply hden
    exact congrArg Subtype.val h

theorem value_affinePullback {M N : ℕ} (T : MeromorphicTensorPresentation N)
    (L : (Fin M → ℂ) →L[ℂ] (Fin N → ℂ)) (b : Fin N → ℂ)
    (hden : (fun s : Fin M → ℂ => (T.denominator : (Fin N → ℂ) → ℂ) (L s + b)) ≠ 0)
    (s : Fin M → ℂ) :
    (T.affinePullback L b hden).value s = T.value (L s + b) := rfl

end MeromorphicTensorPresentation

end GaloisForLFunctions.SelbergClass
