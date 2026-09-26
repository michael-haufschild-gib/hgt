import GaloisForLFunctions.HTGeometry.ChebyshevMomentTrace
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import GaloisForLFunctions.RHTower.XiThetaArithmeticTraceZeroHankelApproximants

open Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Chebyshev trace coordinates of the actual xi central reciprocal moments. -/
def xiCentralChebyshevMomentTrace (n : ℕ) : ℝ :=
  HTGeometry.chebyshevMomentTrace (fun k => (xiCentralReciprocalMoment k).re) n

/-- The same trace coordinates read from the prime--Gamma source germ. -/
def primeArchChebyshevMomentTrace (n : ℕ) : ℝ :=
  HTGeometry.chebyshevMomentTrace
    (fun k => analyticTraceMoments
      (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) k) n

theorem primeArchChebyshevMomentTrace_eq_xi (n : ℕ) :
    primeArchChebyshevMomentTrace n = xiCentralChebyshevMomentTrace n := by
  unfold primeArchChebyshevMomentTrace xiCentralChebyshevMomentTrace
  apply HTGeometry.momentFunctional_congr
  exact analyticTraceMoments_normalizedPrimeArchSource

/-- Chebyshev coordinates of the finite arithmetic stage's power traces. -/
def thetaArithmeticChebyshevMomentTrace (k n : ℕ) : ℝ :=
  HTGeometry.chebyshevMomentTrace
    (fun m => ((thetaArithmeticTraceZeroStage k ^ m).trace).re) n

theorem thetaArithmeticChebyshevMomentTrace_eq_nodes (k n : ℕ) :
    thetaArithmeticChebyshevMomentTrace k n =
      ∑ x ∈ thetaArithmeticCenteredNodes k,
        x * (Chebyshev.T ℝ (n : ℤ)).eval (1 - 2 * x) := by
  classical
  have hseq :
      (fun m => ((thetaArithmeticTraceZeroStage k ^ m).trace).re) =
        (fun m => ∑ x ∈ thetaArithmeticCenteredNodes k, x ^ m) := by
    funext m
    exact re_trace_pow_thetaArithmeticTraceZeroStage k m
  rw [thetaArithmeticChebyshevMomentTrace, hseq]
  simpa only [one_mul] using
    (HTGeometry.chebyshevMomentTrace_finset_atoms
      (thetaArithmeticCenteredNodes k) (fun _ : ℝ => 1) (fun x => x) n)

end

end RHTower
