import GaloisForLFunctions.HTGeometry.MovingCanonicalFullTranslationRankGenericity
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalFullTranslationFreeness
import GaloisForLFunctions.HTGeometry.HerglotzFullTranslationRankGenericity
import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryFaceMaximalTranslation

/-!
# Inhabitation of expanded full-rank interfaces

Several full-rank interfaces are produced inside dense or residual set statements.  Their
inhabitation is therefore mathematically unconditional once the corresponding genericity theorem
applies, but a declaration-level premise audit cannot see through the set comprehension.  This file
extracts the witnesses explicitly and records the connectors from actual Nevanlinna witnesses to
intrinsic probability-carrier witnesses.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-- One phase simultaneously realizes every canonical moving-carrier full-rank pattern. -/
theorem exists_allFinitePatterns_movingCanonicalExpandedFullRankWitness
    {Γ : Type} [Countable Γ] :
    ∃ θ : BoundedRealSequence, ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      movingCanonicalExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        p.coefficientDegree p.orders (carrierPatternExponent p) θ shift := by
  exact (allFinitePatterns_movingCanonicalExpandedFullRankWitness_dense_residual
    (Γ := Γ)).1.nonempty

/-- One phase simultaneously realizes every canonical even moving-carrier full-rank pattern. -/
theorem exists_allFinitePatterns_movingEvenCanonicalExpandedFullRankWitness
    {Γ : Type} [Countable Γ] :
    ∃ θ : BoundedRealSequence, ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      movingEvenCanonicalExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        p.coefficientDegree p.orders (carrierPatternExponent p) θ shift := by
  exact (allFinitePatterns_movingEvenCanonicalExpandedFullRankWitness_dense_residual
    (Γ := Γ)).1.nonempty

/-- Infinite support and a positive integrable weight produce one Herglotz parameter realizing all
canonical finite full-rank patterns and all injective shift packets. -/
theorem exists_allFinitePatterns_herglotzExpandedFullRankWitness
    {Γ : Type} [Countable Γ]
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t) :
    ∃ u : Lp ℝ ⊤ μ, ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      herglotzExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        μ w p.coefficientDegree p.orders (carrierPatternExponent p) u shift := by
  exact (allFinitePatterns_herglotzExpandedFullRankWitness_dense_residual
    (Γ := Γ) μ hμ w hw hwpos).1.nonempty

/-- A dense actual-Nevanlinna witness locus contains an actual full-rank witness.  This is the
logical connector hidden by the dense-set formulation of the analytic genericity theorem. -/
theorem exists_actualNevanlinnaExpandedFullRankWitness_of_dense
    {row κ ι : Type} [Fintype row] [Fintype κ] [Fintype ι]
    (m0 a q : ℂ → ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (baseDensity : Lp ℝ ⊤ mu)
    (S : Submodule ℝ (Lp ℝ ⊤ mu))
    (shift : InjectiveShiftConfiguration ι)
    (h : Dense {w : S | actualNevanlinnaExpandedFullRankWitness
      (row := row) (κ := κ) (ι := ι)
      m0 a q degree orders exponent mu baseDensity S w shift}) :
    ∃ w : S, actualNevanlinnaExpandedFullRankWitness
      (row := row) (κ := κ) (ι := ι)
      m0 a q degree orders exponent mu baseDensity S w shift := by
  exact h.nonempty

/-- A maximal translation witness supplies every constituent probability-carrier certificate. -/
theorem probabilityCarrierExpandedFullRankWitness_of_maximalTranslation
    {nu : ProbabilityMeasure ℝ} (hnu : MaximalTranslationFullRankWitness nu)
    (p : FiniteDifferentialPattern Unit)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p)) :
    probabilityCarrierExpandedFullRankWitness
      (row := CarrierPatternRow p) (nu := nu)
      p.coefficientDegree p.orders (carrierPatternExponent p) shift :=
  hnu p shift

/-- Membership in the closure of the maximal full-rank phase already forces that phase to be
inhabited. -/
theorem exists_maximalTranslationFullRankWitness_of_mem_closure
    {nu₀ : ProbabilityMeasure ℝ}
    (hnu₀ : nu₀ ∈ closure {nu : ProbabilityMeasure ℝ |
      MaximalTranslationFullRankWitness nu}) :
    ∃ nu : ProbabilityMeasure ℝ, MaximalTranslationFullRankWitness nu := by
  apply closure_nonempty_iff.mp
  exact ⟨nu₀, hnu₀⟩

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- Every infinite projective boundary carrier satisfying the classical analytic inputs yields an
intrinsic probability carrier with maximal translation full-rank witnesses. -/
theorem exists_maximalTranslationFullRankWitness
    (inputs : F.MaximalTranslationInputs)
    (K : Set (OnePoint ℝ))
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (hetaK : eta ∈ probabilityLawsCarriedBy K)
    (hetaInfinite : (eta : Measure (OnePoint ℝ)).support.Infinite) :
    ∃ nu : ProbabilityMeasure ℝ, MaximalTranslationFullRankWitness nu := by
  apply exists_maximalTranslationFullRankWitness_of_mem_closure
  apply closure_mono Set.inter_subset_left
  exact F.barycenter_mem_closure_maximalTranslationFullRankWitness_inter_face
    inputs K eta hetaK hetaInfinite

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
