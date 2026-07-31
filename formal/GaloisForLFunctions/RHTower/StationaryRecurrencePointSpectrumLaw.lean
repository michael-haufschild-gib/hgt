import GaloisForLFunctions.RHTower.StationaryRecurrenceCompletionLaw
import GaloisForLFunctions.HTGeometry.ConvolutionAtomBounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Point-spectrum universality of stationary recurrence

The completed-time survival-fidelity distribution of an arbitrary
probability energy law depends only on its point spectrum: atom locations
and atom masses.  Continuous and singular-continuous spectral sectors can
be changed arbitrarily without changing this recurrence law, provided the
point masses remain fixed.

The proof is all-order.  Singleton masses of a convolution depend only on
singleton masses of its factors.  This property propagates through every
convolution power of the energy-difference law.  The stationary recurrence
moments are precisely those zero-sum collision masses, and compact moment
determinacy on `[0,1]` identifies the complete probability law.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Two real measures have the same point spectrum when every singleton
has the same mass. -/
def SamePointMasses (mu nu : Measure ℝ) : Prop :=
  ∀ x : ℝ, mu {x} = nu {x}

theorem samePointMasses_refl (mu : Measure ℝ) :
    SamePointMasses mu mu :=
  fun _ => rfl

theorem samePointMasses_symm
    {mu nu : Measure ℝ} (h : SamePointMasses mu nu) :
    SamePointMasses nu mu :=
  fun x => (h x).symm

/-- Singleton mass of a convolution depends only on singleton masses of
its two factors. -/
theorem conv_singleton_eq_of_samePointMasses
    (mu mu' nu nu' : Measure ℝ)
    [IsFiniteMeasure mu] [IsFiniteMeasure mu']
    [IsFiniteMeasure nu] [IsFiniteMeasure nu']
    (hmu : SamePointMasses mu mu')
    (hnu : SamePointMasses nu nu')
    (z : ℝ) :
    (mu ∗ nu) {z} = (mu' ∗ nu') {z} := by
  rw [conv_singleton_eq_lintegral, conv_singleton_eq_lintegral]
  let S : Set ℝ := {x | nu {z - x} ≠ 0}
  let S' : Set ℝ := {x | nu' {z - x} ≠ 0}
  have hSS' : S = S' := by
    ext x
    simp only [S, S', Set.mem_setOf_eq]
    rw [hnu (z - x)]
  have hScount : S.Countable := by
    let A : Set ℝ := {y | nu {y} ≠ 0}
    have hA : A.Countable := countable_atoms nu
    have hsub : S ⊆ (fun y => z - y) '' A := by
      intro x hx
      exact ⟨z - x, hx, by ring⟩
    exact (hA.image (fun y => z - y)).mono hsub
  have hsupp :
      Function.support (fun x => nu {z - x}) ⊆ S := by
    intro x hx
    exact hx
  have hsupp' :
      Function.support (fun x => nu' {z - x}) ⊆ S := by
    rw [hSS']
    intro x hx
    exact hx
  rw [← setLIntegral_eq_of_support_subset (μ := mu) hsupp,
    ← setLIntegral_eq_of_support_subset (μ := mu') hsupp',
    lintegral_countable _ hScount,
    lintegral_countable _ hScount]
  apply tsum_congr
  intro x
  rw [hnu (z - x), hmu x]

/-- Convolution powers inherit equality of all point masses. -/
theorem convPow_samePointMasses
    (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : SamePointMasses mu nu)
    (n : ℕ) :
    SamePointMasses (convPow mu n) (convPow nu n) := by
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      rw [convPow, convPow]
      intro x
      letI : IsProbabilityMeasure (convPow mu n) :=
        isProbabilityMeasure_convPow mu n
      letI : IsProbabilityMeasure (convPow nu n) :=
        isProbabilityMeasure_convPow nu n
      exact conv_singleton_eq_of_samePointMasses
        mu nu (convPow mu n) (convPow nu n) h ih x

/-- The energy-difference laws of two spectra with the same atoms have
the same atoms. -/
theorem spectralDifferenceMeasure_samePointMasses
    (mu nu : Measure ℝ)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : SamePointMasses mu nu) :
    SamePointMasses
      (spectralDifferenceMeasure mu)
      (spectralDifferenceMeasure nu) := by
  intro z
  rw [spectralDifferenceMeasure,
    spectralDifferenceMeasure,
    Measure.map_apply (by fun_prop) (measurableSet_singleton z),
    Measure.map_apply (by fun_prop) (measurableSet_singleton z),
    Measure.prod_apply (by measurability),
    Measure.prod_apply (by measurability)]
  let S : Set ℝ := {x | mu {x - z} ≠ 0}
  have hScount : S.Countable := by
    let A : Set ℝ := {y | mu {y} ≠ 0}
    have hA : A.Countable := countable_atoms mu
    have hsub : S ⊆ (fun y => y + z) '' A := by
      intro x hx
      exact ⟨x - z, hx, by ring⟩
    exact (hA.image (fun y => y + z)).mono hsub
  have hfiber (x : ℝ) :
      Prod.mk x ⁻¹' (fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' {z} =
        {x - z} := by
    ext y
    simp
    constructor <;> intro hy <;> linarith
  simp_rw [hfiber]
  have hsupp :
      Function.support (fun x => mu {x - z}) ⊆ S := by
    intro x hx
    exact hx
  have hsupp' :
      Function.support (fun x => nu {x - z}) ⊆ S := by
    intro x hx
    have : mu {x - z} ≠ 0 := by
      rw [h (x - z)]
      exact hx
    exact this
  rw [← setLIntegral_eq_of_support_subset (μ := mu) hsupp,
    ← setLIntegral_eq_of_support_subset (μ := nu) hsupp',
    lintegral_countable _ hScount,
    lintegral_countable _ hScount]
  apply tsum_congr
  intro x
  rw [h x, h (x.1 - z)]

/-- **Point-spectrum universality of stationary recurrence.**  For every
pair of probability energy laws, equality of all point masses forces
equality of their complete centered-time limiting survival-fidelity laws.
Thus arbitrary changes to the continuous and singular-continuous spectral
sectors are invisible to completed recurrence. -/
theorem stationarySpectralReturnProbabilityMeasure_eq_of_samePointMasses
    (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : SamePointMasses mu nu) :
    stationarySpectralReturnProbabilityMeasure mu =
      stationarySpectralReturnProbabilityMeasure nu := by
  apply spectralReturnFidelityInterval_probabilityMeasure_ext_moments
  intro n
  rw [stationarySpectralReturnProbabilityMeasure_moment,
    stationarySpectralReturnProbabilityMeasure_moment]
  exact congrArg ENNReal.toReal
    (convPow_samePointMasses
      (spectralDifferenceMeasure mu)
      (spectralDifferenceMeasure nu)
      (spectralDifferenceMeasure_samePointMasses mu nu h)
      n 0)

end RHTower
