import GaloisForLFunctions.HTGeometry.HerglotzFullTranslationFreeness
import GaloisForLFunctions.HTGeometry.TranslatedFamilyGauge

/-!
# Full-translation freeness of regularized Herglotz transforms

The arbitrary-measure genericity theorem is naturally expressed for the finite measure
`exp u * (1 + t²)⁻¹ dμ`.  This file identifies that measure with the Nevanlinna-weighted
measure in the regularized-transform presentation and transports finite-family relation-freeness
through the translated polynomial gauge.  The resulting capstone is stated for the literal
regularized integral from the measure-cone theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ENNReal

noncomputable section

/-- Exponential reweighting by the Nevanlinna density is exactly the finite measure used in the
regularized Herglotz presentation. -/
theorem expWeightedMeasure_nevanlinnaWeight
    (μ : Measure ℝ) (u : Lp ℝ ⊤ μ) :
    expWeightedMeasure μ nevanlinnaWeight u =
      nevanlinnaWeightedMeasure μ (fun t => u t) := by
  rw [expWeightedMeasure, nevanlinnaWeightedMeasure]
  congr 1
  funext t
  rw [mul_comm]

/-- The common upper domain of a finite translated family is open. -/
theorem isOpen_commonUpperTranslationDomain {m : ℕ}
    (shift : InjectiveShiftConfiguration (Fin m)) :
    IsOpen (commonUpperTranslationDomain shift) := by
  rw [show commonUpperTranslationDomain shift =
      ⋂ i : Fin m, {z : ℂ | 0 < (z + shift.1 i).im} by
    ext z
    simp [commonUpperTranslationDomain]]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const
    (Complex.continuous_im.comp (continuous_id.add continuous_const))

/-- On an open domain, pointwise equality of two families identifies all their finite jet
relations. -/
theorem familyDifferentiallyAlgebraicOn_congr_of_isOpen
    {m : ℕ} {f g : Fin m → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hfg : ∀ i z, z ∈ U → f i z = g i z)
    (hf : FamilyDifferentiallyAlgebraicOn f U) :
    FamilyDifferentiallyAlgebraicOn g U := by
  obtain ⟨n, P, hP, hrel⟩ := hf
  refine ⟨n, P, hP, fun z hz => ?_⟩
  have hvec : familyJetVec (n := n) g z = familyJetVec (n := n) f z := by
    funext q
    cases q with
    | inl a => cases a; rfl
    | inr q =>
        obtain ⟨i, j⟩ := q
        change iteratedDeriv (j : ℕ) (g i) z = iteratedDeriv (j : ℕ) (f i) z
        apply Filter.EventuallyEq.iteratedDeriv_eq
        filter_upwards [hU.mem_nhds hz] with y hy
        exact (hfg i y hy).symm
  rw [hvec]
  exact hrel z hz

/-- **Translated regularized Herglotz relation descent.**  If the finite Cauchy transform of the
Nevanlinna-weighted exponential measure has no mixed differential relation among a finite tuple of
distinct translates, neither does the literal regularized Herglotz integral. -/
theorem not_familyDifferentiallyAlgebraicOn_regularizedHerglotz_of_cauchy
    {m : ℕ} (μ : Measure ℝ) (u : Lp ℝ ⊤ μ)
    (shift : InjectiveShiftConfiguration (Fin m))
    [IsFiniteMeasure (expWeightedMeasure μ nevanlinnaWeight u)]
    (hC : ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => cauchyTransform
        (expWeightedMeasure μ nevanlinnaWeight u) (z + shift.1 i))
      (commonUpperTranslationDomain shift)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => ∫ t, regularizedHerglotzKernel t (z + shift.1 i) *
        (Real.exp (u t) : ℂ) ∂μ)
      (commonUpperTranslationDomain shift) := by
  let ν : Measure ℝ := expWeightedMeasure μ nevanlinnaWeight u
  let M : ℂ := (((ν.real Set.univ : ℝ)) : ℂ)
  have hu : Measurable (fun t => u t) := (Lp.stronglyMeasurable u).measurable
  have hν : nevanlinnaWeightedMeasure μ (fun t => u t) = ν := by
    exact (expWeightedMeasure_nevanlinnaWeight μ u).symm
  letI : IsFiniteMeasure ν := by
    dsimp only [ν]
    infer_instance
  letI : IsFiniteMeasure (nevanlinnaWeightedMeasure μ (fun t => u t)) := by
    rw [hν]
    infer_instance
  intro hregularized
  have hpresentation : FamilyDifferentiallyAlgebraicOn
      (fun i z => (z + shift.1 i) * M + (1 + (z + shift.1 i) ^ 2) *
        cauchyTransform ν (z + shift.1 i))
      (commonUpperTranslationDomain shift) := by
    apply familyDifferentiallyAlgebraicOn_congr_of_isOpen
      (isOpen_commonUpperTranslationDomain shift) _ hregularized
    intro i z hz
    have hzg : (z + shift.1 i).im ≠ 0 := ne_of_gt (hz i)
    have hreg := regularizedHerglotzTransform_eq μ (fun t => u t) hu hzg
    simpa only [hν, ν, M, cauchyTransform] using hreg
  apply hC
  exact familyDifferentiallyAlgebraicOn_translatedCauchy_of_presentation
    ν M shift.1 (fun z hz i => ne_of_gt (hz i)) hpresentation

/-- **Measure-universal full-translation Herglotz theorem.**  For every positive Borel measure
with infinite support satisfying the Nevanlinna growth condition, a dense residual set of bounded
real exponential reweightings makes the literal regularized Herglotz transform differentially
algebraically independent across every finite tuple of distinct complex translates on their common
upper half-plane. -/
theorem herglotz_fullTranslationRegularizedFreeness_denseResidual
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (hH0 : Integrable nevanlinnaWeight μ) :
    let universalPhase : Set (Lp ℝ ⊤ μ) := {u | ∀
      (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      herglotzExpandedPatternRelationHolds
        (row := CarrierPatternRow p) μ nevanlinnaWeight p.coefficientDegree p.orders
          (carrierPatternExponent p) u shift coeff →
        ∀ col, coeff col = 0}
    Dense universalPhase ∧ universalPhase ∈ residual (Lp ℝ ⊤ μ) ∧
      ∀ u ∈ universalPhase, ∀ (m : ℕ)
        (shift : InjectiveShiftConfiguration (Fin m)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z => ∫ t, regularizedHerglotzKernel t (z + shift.1 i) *
            (Real.exp (u t) : ℂ) ∂μ)
          (commonUpperTranslationDomain shift) := by
  dsimp only
  let universalPhase : Set (Lp ℝ ⊤ μ) := {u | ∀
    (p : FiniteDifferentialPattern ℕ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    herglotzExpandedPatternRelationHolds
      (row := CarrierPatternRow p) μ nevanlinnaWeight p.coefficientDegree p.orders
        (carrierPatternExponent p) u shift coeff →
      ∀ col, coeff col = 0}
  have hbase := herglotz_fullTranslationCauchyFamilyFreeness_denseResidual
    μ hμ nevanlinnaWeight hH0 nevanlinnaWeight_pos
  refine ⟨hbase.1, hbase.2.1, ?_⟩
  intro u hu m shift
  letI : IsFiniteMeasure (expWeightedMeasure μ nevanlinnaWeight u) :=
    isFiniteMeasure_expWeightedMeasure μ nevanlinnaWeight hH0
      (fun t => (nevanlinnaWeight_pos t).le) u
  apply not_familyDifferentiallyAlgebraicOn_regularizedHerglotz_of_cauchy μ u shift
  exact hbase.2.2 u hu m shift

end

end GaloisForLFunctions.HTGeometry
