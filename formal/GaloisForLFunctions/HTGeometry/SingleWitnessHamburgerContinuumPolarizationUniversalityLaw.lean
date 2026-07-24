import GaloisForLFunctions.HTGeometry.ClopenKernelFirstSecondKindPolarizationLaw
import GaloisForLFunctions.HTGeometry.IndeterminacyCriterion
import GaloisForLFunctions.HTGeometry.MomentIndeterminacyMaximalTotalVariationUniversalityLaw
import GaloisForLFunctions.HTGeometry.NevanlinnaEntire

/-!
# Single-witness Hamburger continuum-polarization universality

One bounded complex kernel witness for a normalized positive Hamburger moment form propagates to
the origin and to every real observation point.  At the origin it produces an injective
Nevanlinna family of representing measures, hence indeterminacy.  On every real slice it
simultaneously produces first-kind summability and decay together with recurrence-weighted
second-kind escape.

This closes three previously terminal surfaces: global bounded-kernel transfer, clopen
first/second-kind polarization, and Nevanlinna-leaf nonuniqueness.
-/

open Polynomial Filter MeasureTheory OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Single-witness Hamburger continuum-polarization universality law.**  An arbitrary bounded
complex kernel witness for a normalized positive moment form forces an injective continuum
parameter family of representing measures, failure of uniqueness, and the complete global
first/second-kind polarization profile. -/
theorem singleWitness_hamburgerContinuumPolarizationUniversality
    (h : PositiveMomentForm s) {z₀ : ℂ} (hz₀ : BoundedKernel s z₀)
    (hzero : s 0 = 1) :
    (∃ F : OnePoint ℝ → Measure ℝ, Function.Injective F ∧
      ∀ t, GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (F t)) ∧
    (¬ ∀ μ ν : Measure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ →
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s ν → μ = ν) ∧
    ∀ x : ℝ,
      BoundedKernel s (x : ℂ) ∧
      FirstKindBounded s (x : ℂ) ∧
      0 < christoffelLimit s x ∧
      Summable (fun k => ((monicOrtho s k).eval x) ^ 2 /
        momentInner s (monicOrtho s k) (monicOrtho s k)) ∧
      Tendsto (fun k => (orthonormalPoly s k).eval x) atTop (nhds 0) ∧
      ∀ C : ℝ, ∃ n : ℕ,
        C < |recurOffSqrt s n * (secondKindNorm s n).eval x| ∨
        C < |recurOffSqrt s n * (secondKindNorm s (n + 1)).eval x| := by
  have hzeroKernel : BoundedKernel s 0 := boundedKernel_global h hz₀ 0
  refine ⟨injective_leaf_into_representing h hzeroKernel hzero,
    not_subsingleton_representing h hzeroKernel hzero, ?_⟩
  exact clopenKernel_firstSecondKind_complete_polarization
    h (isClosed_boundedKernel h) hz₀

/-- **Single-witness Hamburger maximal-TV continuum-polarization universality law.**  An
arbitrary bounded complex kernel witness forces both the complete global first/second-kind
polarization profile and a real continuum of moment-identical probability measures whose every
distinct pair is mutually singular at maximal total-variation distance. -/
theorem singleWitness_hamburgerMaximalTVContinuumPolarizationUniversality
    (h : PositiveMomentForm s) {z₀ : ℂ} (hz₀ : BoundedKernel s z₀)
    (hzero : s 0 = 1) :
    (∃ leaf : ℝ → ProbabilityMeasure ℝ,
      (∀ t : ℝ,
        GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
          (leaf t : Measure ℝ)) ∧
      ∀ t u : ℝ, t ≠ u →
        (leaf t : Measure ℝ) ⟂ₘ (leaf u : Measure ℝ) ∧
        (((leaf t : Measure ℝ).toSignedMeasure -
              (leaf u : Measure ℝ).toSignedMeasure).totalVariation Set.univ = 2)) ∧
    (¬ ∀ μ ν : Measure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ →
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s ν → μ = ν) ∧
    ∀ x : ℝ,
      BoundedKernel s (x : ℂ) ∧
      FirstKindBounded s (x : ℂ) ∧
      0 < christoffelLimit s x ∧
      Summable (fun k => ((monicOrtho s k).eval x) ^ 2 /
        momentInner s (monicOrtho s k) (monicOrtho s k)) ∧
      Tendsto (fun k => (orthonormalPoly s k).eval x) atTop (nhds 0) ∧
      ∀ C : ℝ, ∃ n : ℕ,
        C < |recurOffSqrt s n * (secondKindNorm s n).eval x| ∨
        C < |recurOffSqrt s n * (secondKindNorm s (n + 1)).eval x| := by
  have hzeroKernel : BoundedKernel s 0 := boundedKernel_global h hz₀ 0
  have hmaximal :=
    exists_momentIdentical_pairwiseMaximalTotalVariation_family h hzeroKernel hzero
  have hpolarization :=
    singleWitness_hamburgerContinuumPolarizationUniversality h hz₀ hzero
  exact ⟨hmaximal, hpolarization.2⟩

end HTGeometry
