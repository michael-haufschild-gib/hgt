import GaloisForLFunctions.RHTower.PrimeLogThetaRealAxisAmbientHilbertObstruction
import GaloisForLFunctions.HilbertMetric.DenseClosedComplexScalarRigidity

/-!
# No dense closable real-axis reader on the critical-Laplace graph

Route P cannot evade its real-axis obstruction by replacing a continuous
closed-graph functional with an unbounded partial reader on a dense domain.
For complex scalar output, dense closability already forces a continuous
extension.  The literal prime-coordinate identity then contradicts the
ambient-Hilbert obstruction.

This leaves a sharp positive design constraint: any coefficient-faithful
real-axis scalar reader on the existing completed graph must have a
non-dense domain, fail closability, or change the source topology before
completion.  A four-level boundary construction must therefore not be
modelled as four dense closable scalar readers in this Hilbert graph.
-/

open Complex Set Topology
open scoped LinearPMap

namespace RHTower

noncomputable section

/-- **Dense-closability obstruction at the literal theta boundary.** A partial
complex-linear reader which agrees with the literal real-axis theta value on
every one-prime graph point cannot be both closable and densely defined on
the existing closed critical-Laplace graph. -/
theorem not_dense_domain_of_closable_primeLogTheta_realAxis_reader
    (x : ℝ)
    (F : primeLogCriticalLaplaceSynthesis.closure.graph →ₗ.[ℂ] ℂ)
    (hclosable : F.IsClosable)
    (hcore : ∀ p : Nat.Primes,
      primeLogCriticalLaplacePrimeGraphPoint p ∈ F.domain)
    (hreader : ∀ p : Nat.Primes,
      F ⟨primeLogCriticalLaplacePrimeGraphPoint p, hcore p⟩ =
        primeLogThetaStripRealAxisReporter x p) :
    ¬ Dense (F.domain : Set primeLogCriticalLaplaceSynthesis.closure.graph) := by
  intro hdense
  haveI : IsClosed (primeLogCriticalLaplaceSynthesis.closure.graph :
      Set (primeLogCriticalSourceL2 × primeLogCriticalHalfLineL2)) :=
    primeLogCriticalLaplaceSynthesis_closure_isClosed
  haveI : CompleteSpace (primeLogCriticalLaplaceSynthesis.closure.graph :
      Set (primeLogCriticalSourceL2 × primeLogCriticalHalfLineL2)) :=
    IsClosed.completeSpace_coe
  haveI : CompleteSpace primeLogCriticalLaplaceSynthesis.closure.graph := this
  obtain ⟨G, hG⟩ := GaloisForLFunctions.HilbertMetric.dense_closable_complexScalarLinearPMap_exists_continuous_extension
    F hclosable hdense
  apply no_continuousClosedGraphReader_primeLogTheta_realAxis x G
  intro p
  exact (hG ⟨primeLogCriticalLaplacePrimeGraphPoint p, hcore p⟩).trans (hreader p)

/-- **Four-level consequence.** A candidate Route-P four-level real-axis
boundary map cannot have all of its coordinate readers dense and closable
when even one coordinate retains the literal degree-zero theta values. -/
theorem not_dense_closable_fourLevel_primeLogTheta_realAxis_reader
    (x : ℝ)
    (F : Fin 4 →
      (primeLogCriticalLaplaceSynthesis.closure.graph →ₗ.[ℂ] ℂ))
    (i : Fin 4)
    (hcore : ∀ p : Nat.Primes,
      primeLogCriticalLaplacePrimeGraphPoint p ∈ (F i).domain)
    (hreader : ∀ p : Nat.Primes,
      F i ⟨primeLogCriticalLaplacePrimeGraphPoint p, hcore p⟩ =
        primeLogThetaStripRealAxisReporter x p)
    (hclosable : (F i).IsClosable) :
    ¬ Dense ((F i).domain :
      Set primeLogCriticalLaplaceSynthesis.closure.graph) := by
  exact not_dense_domain_of_closable_primeLogTheta_realAxis_reader x
    (F i) hclosable hcore hreader

end

end RHTower
