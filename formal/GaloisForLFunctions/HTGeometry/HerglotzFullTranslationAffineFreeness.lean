import GaloisForLFunctions.HTGeometry.HerglotzFullTranslationRegularizedFreeness

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ENNReal

noncomputable section

theorem contDiffAt_regularizedHerglotzTransform_translate
    (μ : Measure ℝ) (u : Lp ℝ ⊤ μ)
    [IsFiniteMeasure
      (expWeightedMeasure μ nevanlinnaWeight u)]
    (c : ℂ) {z : ℂ} (hz : (z + c).im ≠ 0) :
    ContDiffAt ℂ (⊤ : ℕ∞)
      (fun w => ∫ t,
        regularizedHerglotzKernel t (w + c) *
          (Real.exp (u t) : ℂ) ∂μ) z := by
  let ν : Measure ℝ :=
    expWeightedMeasure μ nevanlinnaWeight u
  let M : ℂ := (((ν.real Set.univ : ℝ)) : ℂ)
  have hu : Measurable (fun t => u t) :=
    (Lp.stronglyMeasurable u).measurable
  have hν :
      nevanlinnaWeightedMeasure μ (fun t => u t) = ν :=
    (expWeightedMeasure_nevanlinnaWeight μ u).symm
  letI : IsFiniteMeasure ν := by
    dsimp only [ν]
    infer_instance
  letI : IsFiniteMeasure
      (nevanlinnaWeightedMeasure μ (fun t => u t)) := by
    rw [hν]
    infer_instance
  have hcauchy :
      ContDiffAt ℂ (⊤ : ℕ∞)
        (fun w => cauchyTransform ν (w + c)) z :=
    contDiffAt_cauchyTransform_translate ν c hz
  have hshift :
      ContDiffAt ℂ (⊤ : ℕ∞) (fun w : ℂ => w + c) z :=
    contDiffAt_id.add contDiffAt_const
  have hpresentation :
      ContDiffAt ℂ (⊤ : ℕ∞)
        (fun w =>
          (w + c) * M +
            (1 + (w + c) ^ 2) *
              cauchyTransform ν (w + c)) z :=
    (hshift.mul contDiffAt_const).add
      ((contDiffAt_const.add (hshift.pow 2)).mul hcauchy)
  have him :
      ContinuousAt (fun w : ℂ => (w + c).im) z :=
    Complex.continuous_im.continuousAt.comp
      (continuousAt_id.add continuousAt_const)
  have hne : ∀ᶠ w in 𝓝 z, (w + c).im ≠ 0 :=
    him.eventually_ne hz
  apply hpresentation.congr_of_eventuallyEq
  filter_upwards [hne] with w hw
  have hreg :=
    regularizedHerglotzTransform_eq
      μ (fun t => u t) hu hw
  simpa only [hν, ν, M, cauchyTransform] using hreg

theorem
    herglotz_fullTranslationFreeness_affine_denseResidual
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (hH0 : Integrable nevanlinnaWeight μ) :
    let universalPhase : Set (Lp ℝ ⊤ μ) := {u | ∀
      (p : FiniteDifferentialPattern ℕ)
      (shift :
        InjectiveShiftConfiguration
          (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p ×
          Fin (p.coefficientDegree + 1) → ℂ),
      herglotzExpandedPatternRelationHolds
        (row := CarrierPatternRow p) μ nevanlinnaWeight
          p.coefficientDegree p.orders
          (carrierPatternExponent p) u shift coeff →
        ∀ col, coeff col = 0}
    Dense universalPhase ∧
      universalPhase ∈ residual (Lp ℝ ⊤ μ) ∧
      ∀ u ∈ universalPhase, ∀ (α β : ℂ) (m : ℕ)
        (shift : InjectiveShiftConfiguration (Fin m)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z =>
            α + β * (z + shift.1 i) +
              ∫ t,
                regularizedHerglotzKernel
                    t (z + shift.1 i) *
                  (Real.exp (u t) : ℂ) ∂μ)
          (commonUpperTranslationDomain shift) := by
  dsimp only
  have hbase :=
    herglotz_fullTranslationRegularizedFreeness_denseResidual
      μ hμ hH0
  dsimp only at hbase
  refine ⟨hbase.1, hbase.2.1, ?_⟩
  intro u hu α β m shift hfull
  letI : IsFiniteMeasure
      (expWeightedMeasure μ nevanlinnaWeight u) :=
    isFiniteMeasure_expWeightedMeasure μ nevanlinnaWeight hH0
      (fun t => (nevanlinnaWeight_pos t).le) u
  let g : Fin m → ℂ → ℂ := fun i z =>
    ∫ t, regularizedHerglotzKernel
        t (z + shift.1 i) *
      (Real.exp (u t) : ℂ) ∂μ
  apply hbase.2.2 u hu m shift
  apply familyDifferentiallyAlgebraicOn_of_add_polynomial
    g
    (fun i =>
      Polynomial.C α +
        Polynomial.C β *
          (Polynomial.X + Polynomial.C (shift.1 i)))
  · intro z hz i
    exact contDiffAt_regularizedHerglotzTransform_translate
      μ u (shift.1 i) (ne_of_gt (hz i))
  · apply familyDifferentiallyAlgebraicOn_congr_of_isOpen
      (isOpen_commonUpperTranslationDomain shift) _ hfull
    intro i z hz
    simp only [g, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    ring

end

end GaloisForLFunctions.HTGeometry
