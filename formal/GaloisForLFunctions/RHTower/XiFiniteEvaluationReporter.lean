import GaloisForLFunctions.HTGeometry.FiniteEvaluationReporter
import GaloisForLFunctions.RHTower.XiArbitraryJetHilbertReconstruction

/-!
# Dimension-optimal finite evaluation reporters for completed Xi

Completed-Xi jet freeness and the finite evaluation/reporter connector together give a concrete
faithful reporter at every finite resolution.  Exactly `N` point samples recover all coefficients
of the first `N` Xi derivatives, carry a positive-definite Fisher Gram, have no blind coefficient
direction, and contribute positive sequential information at every admitted order.

The construction is dimension-optimal among arbitrary finite-dimensional Hilbert reporters:
nonsingularity of any `N`-jet reporter Gram forces output finrank at least `N`.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HTGeometry
open Module

noncomputable section

/-- **Unconditional finite-sample Xi reporter reconstruction.**  At every resolution, one packet
of exactly as many distinct samples as Xi derivatives supports exact coefficient recovery, strict
reporter information, faithful readout, zero blindness, full visible rank, and positive sequential
information throughout the block. -/
theorem exists_injective_xiFiniteEvaluationReporterHilbertReconstruction (N : ℕ) :
    ∃ (points : Fin N → ℂ) (dual : Fin N → Fin N → ℂ),
      Function.Injective points ∧
      (∀ (q r : Fin N), ∑ i, dual q i * iteratedDeriv (r : ℕ) xi (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin N → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * iteratedDeriv (r : ℕ) xi (points i)) = a q) ∧
      (finiteDerivativeReporterGram N xi
        (finiteEvaluationReporter points)).PosDef ∧
      0 < (finiteDerivativeReporterGram N xi
        (finiteEvaluationReporter points)).det ∧
      Function.Injective
        (finiteDerivativeReporterMap N xi (finiteEvaluationReporter points)) ∧
      LinearMap.ker
        (finiteDerivativeReporterMap N xi (finiteEvaluationReporter points)) = ⊥ ∧
      finrank ℂ (LinearMap.range
        (finiteDerivativeReporterMap N xi (finiteEvaluationReporter points))) = N ∧
      ∀ k : ℕ, k < N →
        0 < finiteDerivativeReporterConditionalInformation k xi
          (finiteEvaluationReporter points) := by
  apply exists_injective_finiteEvaluationReporterHilbertReconstruction_of_linearIndependent
  exact (algebraicIndependent_xi_iteratedDeriv.comp
    (fun j : Fin N => (j : ℕ)) Fin.val_injective).linearIndependent

universe u

/-- **Dimension-optimal Xi reporter law.**  An `N`-dimensional point-evaluation reporter realizes
faithful `N`-jet information, while every faithful Hilbert-valued `N`-jet reporter—regardless of
its construction—has output finrank at least `N`. -/
theorem xiFiniteEvaluationReporter_dimensionOptimal (N : ℕ) :
    (∃ points : Fin N → ℂ,
      Function.Injective points ∧
      (finiteDerivativeReporterGram N xi
        (finiteEvaluationReporter points)).PosDef ∧
      Function.Injective
        (finiteDerivativeReporterMap N xi (finiteEvaluationReporter points)) ∧
      LinearMap.ker
        (finiteDerivativeReporterMap N xi (finiteEvaluationReporter points)) = ⊥ ∧
      finrank ℂ (LinearMap.range
        (finiteDerivativeReporterMap N xi (finiteEvaluationReporter points))) = N ∧
      (∀ k : ℕ, k < N →
        0 < finiteDerivativeReporterConditionalInformation k xi
          (finiteEvaluationReporter points))) ∧
    (∀ (Y : Type u) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
        [FiniteDimensional ℂ Y] (report : (ℂ → ℂ) →ₗ[ℂ] Y),
      (finiteDerivativeReporterGram N xi report).det ≠ 0 →
        N ≤ finrank ℂ Y) := by
  constructor
  · obtain ⟨points, _dual, hinj, _hdelta, _hrecovery, hgram, _hdet,
      hreport, hker, hrank, hinfo⟩ :=
      exists_injective_xiFiniteEvaluationReporterHilbertReconstruction N
    exact ⟨points, hinj, hgram, hreport, hker, hrank, hinfo⟩
  · intro Y _ _ _ report hdet
    exact finrank_ge_of_finiteDerivativeReporterGram_det_ne_zero
      N xi report hdet

end

end RHTower
