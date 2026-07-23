import GaloisForLFunctions.RHTower.XiFiniteEvaluationReporter
import GaloisForLFunctions.RHTower.XiLogDerivReporterConditionalInformation

/-!
# Xi evaluation-reporter source discrimination universality

At every finite resolution, completed-Xi jet freeness supplies an unisolvent point-evaluation
reporter with positive-definite Xi Gram geometry.  The same unchanged finite-dimensional reporter
cannot remain faithful to the logarithmic derivative tower: by its output dimension, it assigns
zero conditional information to a genuinely new `logDeriv xi` derivative.  Thus reporter
faithfulness is source-sensitive even between these canonically linked Xi observables.
-/

open scoped ComplexOrder InnerProductSpace

namespace RHTower

open GaloisForLFunctions
open HTGeometry
open Module

noncomputable section

/-- **Xi/log-Xi finite-reporter discrimination law.**  For every `N`, one injective `N`-point
evaluation packet is faithful to the first `N` completed-Xi derivatives, yet the identical
reporter loses a genuinely new logarithmic-derivative direction at some order at most `N`. -/
theorem exists_injective_xiEvaluationReporter_faithfulXi_blindLogDeriv (N : ℕ) :
    ∃ points : Fin N → ℂ,
      Function.Injective points ∧
      (finiteDerivativeReporterGram N xi
        (finiteEvaluationReporter points)).PosDef ∧
      ∃ k : ℕ, k ≤ N ∧
        finiteDerivativeReporterConditionalInformation k (logDeriv xi)
            (finiteEvaluationReporter points) = 0 ∧
        finiteEvaluationReporter points (iteratedDeriv k (logDeriv xi)) ∈
          finiteDerivativeReporterPreviousSpace k (logDeriv xi)
            (finiteEvaluationReporter points) ∧
        iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
          (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) (logDeriv xi)) := by
  obtain ⟨points, _dual, hinjective, _hdelta, _hrecovery, hXi, _hdet,
      _hinjectiveMap, _hker, _hrank, _hinformation⟩ :=
    exists_injective_xiFiniteEvaluationReporterHilbertReconstruction N
  obtain ⟨k, hk, hzero, hreported, hsource⟩ :=
    exists_xiLogDeriv_finiteReporterConditionalInformation_collapse
      (finiteEvaluationReporter points)
  refine ⟨points, hinjective, hXi, k, ?_, hzero, hreported, hsource⟩
  simpa using hk

end

end RHTower
