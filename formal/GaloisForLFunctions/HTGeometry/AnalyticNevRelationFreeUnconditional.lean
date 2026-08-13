import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaMaximalTranslationInputs
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierRelationFree
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaBoundaryRealAnalytic

/-!
# The finite-jet residual hypertranscendence law of the constructed carrier family

Freezing an arbitrary finite Cauchy jet of the boundary carrier leaves an infinite-dimensional
positive chart, and inside that chart the actual weighted-carrier Cauchy transforms are
hypertranscendental on a dense residual set.  The constructed analytic Nevanlinna family of an
indeterminate normalised moment sequence supplies every analytic hypothesis of that law: minimal
exponential type, a lower row with no common zero, a zero and a regular point of the denominator
entry, the Weyl half-plane map, and the label null-preimage property of the real-analytic lower
row.  Only the frozen-jet data and the parameter law remain as arguments.
-/

open MeasureTheory OnePoint Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped OnePoint

namespace HTGeometry

noncomputable section

variable {s : ℕ → ℝ}

/-- **Finite-jet residual hypertranscendence, unconditionally.**  Freeze any finite packet of
upper-half-plane Cauchy jets of the constructed carrier family against an infinite-support
parameter law: the positive mass-one chart of the frozen level contains a dense residual family
whose actual weighted-carrier Cauchy transforms are hypertranscendental, and every point of the
chart is a strictly positive normalised density. -/
theorem analyticNevCarrier_positiveActualCarrier_hypertranscendental_dense_residual
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective
      (fun i => (analyticNevCarrierFamily h h0b h0).quotient (zf i)))
    (hupperf : ∀ i, 0 < ((analyticNevCarrierFamily h h0b h0).quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta] (heta : eta.support.Infinite) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => (analyticNevCarrierFamily h h0b h0).quotient (zf i)) nf eta hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let hypertranscendentalCarrier : Set positiveChart := {w |
      Hypertranscendental
        (fun z => ∫ x, ((x : ℂ) - z)⁻¹
          ∂weightedBoundaryCarrier (analyticNevCarrierFamily h h0b h0).base.toBoundaryFamily eta
            (linftyOne eta + w.1.1))}
    Dense hypertranscendentalCarrier ∧
      hypertranscendentalCarrier ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive eta (linftyOne eta + w.1.1) ∧
          ∫ t, (linftyOne eta + w.1.1) t ∂eta = 1 :=
  (analyticNevCarrierFamily h h0b h0).positiveActualCarrier_hypertranscendental_dense_residual
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0).minimalExponentialType
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0).noCommonZero
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0).zeroPoint_spec
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0).regularPoint_spec
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0).upperMap
    zf hqf_inj hupperf nf eta heta

/-- **Singular-continuous finite-jet capstone, unconditionally.**  For a singular-continuous
projective parameter law, every point of the frozen positive chart is an atomless
Lebesgue-singular probability solution of the same Hamburger moment problem, and a dense residual
subfamily has hypertranscendental Cauchy transform. -/
theorem analyticNevCarrier_positiveSingularContinuousCarrier_hypertranscendental_dense_residual
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective
      (fun i => (analyticNevCarrierFamily h h0b h0).quotient (zf i)))
    (hupperf : ∀ i, 0 < ((analyticNevCarrierFamily h h0b h0).quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (hetaSC : eta ∈ projectiveSingularContinuousProbabilityLaws) :
    let mu : Measure (OnePoint ℝ) := eta
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => (analyticNevCarrierFamily h h0b h0).quotient (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let hypertranscendentalCarrier : Set positiveChart := {w |
      Hypertranscendental
        (fun z => ∫ x, ((x : ℂ) - z)⁻¹
          ∂weightedBoundaryCarrier (analyticNevCarrierFamily h h0b h0).base.toBoundaryFamily mu
            (linftyOne mu + w.1.1))}
    Dense hypertranscendentalCarrier ∧
      hypertranscendentalCarrier ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        let density := linftyOne mu + w.1.1
        let carrier := weightedBoundaryCarrier
          (analyticNevCarrierFamily h h0b h0).base.toBoundaryFamily mu density
        LinftyStrictlyPositive mu density ∧
          ∫ t, density t ∂mu = 1 ∧
          IsProbabilityMeasure carrier ∧ NullSingletonClass carrier ∧
          carrier ⟂ₘ (volume : Measure ℝ) ∧ HasHamburgerMoments s carrier :=
  (analyticNevCarrierFamily h h0b
      h0).positiveSingularContinuousCarrier_hypertranscendental_dense_residual
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0).minimalExponentialType
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0).noCommonZero
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0).zeroPoint_spec
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0).regularPoint_spec
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0).upperMap
    zf hqf_inj hupperf nf eta hetaSC
    (fun _ hE hnull =>
      (analyticNevCarrierFamily h h0b h0).projectiveLabel_preimage_volume_eq_zero_of_classical
        hE hnull)

end

end HTGeometry
