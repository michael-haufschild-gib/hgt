import GaloisForLFunctions.HTGeometry.BoundaryCarrierTranslationFreeness
import GaloisForLFunctions.HTGeometry.AtomlessProjectiveFrameFiber

/-!
# Maximal translation rank on every infinite Nevanlinna boundary face

The compact-patch transversality theorem supplies dense relation-free points in each positive
`L∞` chart.  Infinite-support probability laws are dense on every infinite closed projective
carrier.  Weak continuity of density reweighting and of the Nevanlinna barycenter joins these two
facts, giving the global weak-topology density theorem on every infinite closed boundary face.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter MeasureTheory OnePoint Set Topology
open scoped ENNReal OnePoint Topology

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- The classical analytic inputs used by the compact-patch Nevanlinna transversality theorem. -/
structure MaximalTranslationInputs where
  minimalExponentialType : HasMinimalExponentialType F.c
  noCommonZero : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0)
  zeroPoint : ℂ
  zeroPoint_spec : F.c zeroPoint = 0
  regularPoint : ℂ
  regularPoint_spec : F.c regularPoint ≠ 0
  upperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im
  phase_isGδ : IsGδ {nu : ProbabilityMeasure ℝ |
    MaximalTranslationDifferentialFree nu}

/-- An infinite-support parameter barycenter lies in the weak closure of carriers with simultaneous
full-rank packet certificates inside every projective face carrying it. -/
theorem barycenter_mem_closure_maximalTranslationFullRankWitness_inter_face
    (inputs : F.MaximalTranslationInputs)
    (K : Set (OnePoint ℝ))
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (hetaK : eta ∈ probabilityLawsCarriedBy K)
    (hetaInfinite : (eta : Measure (OnePoint ℝ)).support.Infinite) :
    F.base.toBoundaryFamily.barycenter eta ∈
      closure ({nu : ProbabilityMeasure ℝ |
        MaximalTranslationFullRankWitness nu} ∩
        F.base.toBoundaryFamily.boundaryCarrierFace K) := by
  let BF := F.base.toBoundaryFamily
  let mu : Measure (OnePoint ℝ) := eta
  let zf : Fin 0 → ℂ := Fin.elim0
  let nf : Fin 0 → ℕ := Fin.elim0
  have hqf : Function.Injective (fun i : Fin 0 => F.quotient (zf i)) :=
    fun i => Fin.elim0 i
  have hupperf : ∀ i : Fin 0, 0 < (F.quotient (zf i)).im :=
    fun i => Fin.elim0 i
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let positiveChart : Set S := Metric.ball 0 1
  let good : Set positiveChart := {w | ∀
    (p : FiniteDifferentialPattern Unit)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
    actualNevanlinnaExpandedFullRankWitness
      (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
      (ι := CarrierPatternShift p)
      F.background F.amplitude F.quotient p.coefficientDegree p.orders
        (carrierPatternExponent p) mu (linftyOne mu) S w.1 shift}
  have hlocal : Dense good ∧ good ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive mu (linftyOne mu + w.1.1) ∧
          ∫ t, (linftyOne mu + w.1.1) t ∂mu = 1 := by
    simpa [good, positiveChart, S, frozen, mu, zf, nf] using
      (F.allFinitePatterns_positiveAbstractCarrier_fullRankWitness_dense_residual
        inputs.minimalExponentialType inputs.noCommonZero
        inputs.zeroPoint_spec inputs.regularPoint_spec inputs.upperMap
        zf hqf hupperf nf mu hetaInfinite)
  let density : positiveChart → Lp ℝ (⊤ : ENNReal) mu :=
    fun w => linftyOne mu + w.1.1
  let carrier : positiveChart → ProbabilityMeasure ℝ := fun w =>
    weightedBoundaryProbabilityCarrier BF mu (density w)
      (hlocal.2.2 w).1 (hlocal.2.2 w).2
  have hdensity : Continuous density := by
    dsimp only [density]
    fun_prop
  have hcarrier : Continuous carrier := by
    dsimp only [carrier]
    exact BF.barycenter_isClosedEmbedding.continuous.comp
      (continuous_linftyDensityProbabilityMeasure mu density hdensity
        (fun w => (hlocal.2.2 w).1) (fun w => (hlocal.2.2 w).2))
  have hgoodImage : carrier '' good ⊆
      {nu : ProbabilityMeasure ℝ | MaximalTranslationFullRankWitness nu} ∩
        BF.boundaryCarrierFace K := by
    rintro nu ⟨w, hw, rfl⟩
    constructor
    · intro p shift
      exact F.probabilityCarrierExpandedFullRankWitness_weightedBoundaryProbabilityCarrier
        mu (linftyOne mu) S w.1 (hlocal.2.2 w).1 (hlocal.2.2 w).2
        p.coefficientDegree p.orders (carrierPatternExponent p) shift
        inputs.upperMap (hw p shift)
    · refine ⟨linftyDensityProbabilityMeasure mu (density w)
          (hlocal.2.2 w).1 (hlocal.2.2 w).2, ?_, rfl⟩
      change linftyDensityMeasure mu (density w) Kᶜ = 0
      exact (withDensity_absolutelyContinuous mu _)
        (show mu Kᶜ = 0 from hetaK)
  let zeroChart : positiveChart := ⟨0, by simp [positiveChart]⟩
  have hcarrierZero : carrier zeroChart = BF.barycenter eta := by
    change BF.barycenter
        (linftyDensityProbabilityMeasure mu (density zeroChart)
          (hlocal.2.2 zeroChart).1 (hlocal.2.2 zeroChart).2) =
      BF.barycenter eta
    apply congrArg BF.barycenter
    apply ProbabilityMeasure.toMeasure_injective
    simpa [carrier, density, zeroChart, mu] using!
      (linftyDensityMeasure_linftyOne (eta : Measure (OnePoint ℝ)))
  have hzero : carrier zeroChart ∈ closure (carrier '' good) :=
    hcarrier.range_subset_closure_image_dense hlocal.1 ⟨zeroChart, rfl⟩
  rw [hcarrierZero] at hzero
  exact closure_mono hgoodImage hzero

/-- The full-rank closure theorem implies the corresponding intrinsic relation-free closure
theorem. -/
theorem barycenter_mem_closure_maximalTranslationDifferentialFree_inter_face
    (inputs : F.MaximalTranslationInputs)
    (K : Set (OnePoint ℝ))
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (hetaK : eta ∈ probabilityLawsCarriedBy K)
    (hetaInfinite : (eta : Measure (OnePoint ℝ)).support.Infinite) :
    F.base.toBoundaryFamily.barycenter eta ∈
      closure ({nu : ProbabilityMeasure ℝ |
        MaximalTranslationDifferentialFree nu} ∩
        F.base.toBoundaryFamily.boundaryCarrierFace K) := by
  apply closure_mono (s := {nu : ProbabilityMeasure ℝ |
    MaximalTranslationFullRankWitness nu} ∩
      F.base.toBoundaryFamily.boundaryCarrierFace K)
  · rintro nu ⟨hfull, hface⟩
    exact ⟨maximalTranslationDifferentialFree_of_fullRankWitness hfull, hface⟩
  · exact F.barycenter_mem_closure_maximalTranslationFullRankWitness_inter_face
      inputs K eta hetaK hetaInfinite

/-- On every infinite closed projective face, simultaneous full-rank packet witnesses are weakly
dense.  The conclusion is stated intrinsically in the ambient probability space. -/
theorem boundaryCarrierFace_subset_closure_maximalTranslationFullRankWitness
    (inputs : F.MaximalTranslationInputs)
    (K : Set (OnePoint ℝ)) (hKclosed : IsClosed K) (hK : K.Infinite) :
    F.base.toBoundaryFamily.boundaryCarrierFace K ⊆
      closure ({nu : ProbabilityMeasure ℝ |
        MaximalTranslationFullRankWitness nu} ∩
        F.base.toBoundaryFamily.boundaryCarrierFace K) := by
  let BF := F.base.toBoundaryFamily
  let C := CarriedProbabilityLaw K
  let infiniteLaws : Set C := {eta |
    ((eta.1 : ProbabilityMeasure (OnePoint ℝ)) :
      Measure (OnePoint ℝ)).support.Infinite}
  let bary : C → ProbabilityMeasure ℝ := fun eta => BF.barycenter eta.1
  have hinfiniteDense : Dense infiniteLaws := by
    simpa [infiniteLaws, C] using
      (infiniteSupport_carriedProbabilityLaws_dense K hKclosed hK)
  have hbaryContinuous : Continuous bary :=
    BF.barycenter_isClosedEmbedding.continuous.comp continuous_subtype_val
  have hinfiniteImage : bary '' infiniteLaws ⊆
      closure ({nu : ProbabilityMeasure ℝ |
        MaximalTranslationFullRankWitness nu} ∩ BF.boundaryCarrierFace K) := by
    rintro _ ⟨eta, hetaInfinite, rfl⟩
    exact F.barycenter_mem_closure_maximalTranslationFullRankWitness_inter_face
      inputs K eta.1 eta.2 hetaInfinite
  have hclosure : closure (bary '' infiniteLaws) ⊆
      closure ({nu : ProbabilityMeasure ℝ |
        MaximalTranslationFullRankWitness nu} ∩ BF.boundaryCarrierFace K) :=
    closure_minimal hinfiniteImage isClosed_closure
  rintro nu ⟨eta, hetaK, rfl⟩
  apply hclosure
  exact hbaryContinuous.range_subset_closure_image_dense hinfiniteDense
    ⟨⟨eta, hetaK⟩, rfl⟩

/-- Full-rank density implies maximal translation-differential-freeness density on every infinite
closed boundary face. -/
theorem boundaryCarrierFace_subset_closure_maximalTranslationDifferentialFree
    (inputs : F.MaximalTranslationInputs)
    (K : Set (OnePoint ℝ)) (hKclosed : IsClosed K) (hK : K.Infinite) :
    F.base.toBoundaryFamily.boundaryCarrierFace K ⊆
      closure ({nu : ProbabilityMeasure ℝ |
        MaximalTranslationDifferentialFree nu} ∩
        F.base.toBoundaryFamily.boundaryCarrierFace K) := by
  apply (F.boundaryCarrierFace_subset_closure_maximalTranslationFullRankWitness
    inputs K hKclosed hK).trans
  exact closure_mono (by
    rintro nu ⟨hfull, hface⟩
    exact ⟨maximalTranslationDifferentialFree_of_fullRankWitness hfull, hface⟩)

/-- Maximally translation-free points of one boundary face, with the relative weak topology. -/
def boundaryCarrierFaceMaximalTranslationPhase
    (K : Set (OnePoint ℝ)) :
    Set {nu : ProbabilityMeasure ℝ //
      nu ∈ F.base.toBoundaryFamily.boundaryCarrierFace K} :=
  {nu | MaximalTranslationDifferentialFree nu.1}

/-- Every infinite closed boundary face carries a dense residual maximal-translation phase. -/
theorem boundaryCarrierFace_maximalTranslationPhase_dense_residual
    (inputs : F.MaximalTranslationInputs)
    (K : Set (OnePoint ℝ)) (hKclosed : IsClosed K) (hK : K.Infinite) :
    Dense (F.boundaryCarrierFaceMaximalTranslationPhase K) ∧
      F.boundaryCarrierFaceMaximalTranslationPhase K ∈
        residual {nu : ProbabilityMeasure ℝ //
          nu ∈ F.base.toBoundaryFamily.boundaryCarrierFace K} := by
  have hdense : Dense (F.boundaryCarrierFaceMaximalTranslationPhase K) := by
    rw [Subtype.dense_iff]
    have himage :
        ((↑) : {nu : ProbabilityMeasure ℝ //
          nu ∈ F.base.toBoundaryFamily.boundaryCarrierFace K} → ProbabilityMeasure ℝ) ''
            F.boundaryCarrierFaceMaximalTranslationPhase K =
          {nu : ProbabilityMeasure ℝ | MaximalTranslationDifferentialFree nu} ∩
            F.base.toBoundaryFamily.boundaryCarrierFace K := by
      ext nu
      simp [boundaryCarrierFaceMaximalTranslationPhase]
    rw [himage]
    exact F.boundaryCarrierFace_subset_closure_maximalTranslationDifferentialFree
      inputs K hKclosed hK
  refine ⟨hdense, residual_of_dense_Gδ ?_ hdense⟩
  exact IsGδ.preimage continuous_subtype_val inputs.phase_isGδ

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
