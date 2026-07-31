import GaloisForLFunctions.RHTower.XiDivisorTraceMomentIdentity
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm

/-!
# The witness trace is prime–archimedean source data

The last edge of the divisor trace tower: its limit trace — already identified with the
first central reciprocal moment — equals a Taylor coefficient of the **continued
prime–archimedean source germ**, through the corpus's unconditional moment bridge.  The
operator-theoretic tower, the divisor moment layer, and the prime–Gamma source meet in one
number:

* `opTrace_xiDivisorResolventSquare_eq_primeArchSourceMoment` — the trace of the Schatten-1
  resolvent square `diag(μ_q⁻²)` is the zeroth analytic trace moment of the normalized
  prime–archimedean source germ;
* `opTrace_xiDivisorResolventSquare_im_eq_zero` — the witness trace is real.

This is the source-side identification of the tower's limit at the moment-0 observable,
fully unconditional: the trace of a concrete trace-class operator with divisor spectrum is
computable from the primes and the archimedean place.  What the tower card's open conjecture
still demands is this identification *operatorially* at every stage — the finite source
stages themselves — not merely at the level of the limit value.
-/

namespace RHTower

noncomputable section

open Complex ContinuousLinearMap

/-- **The witness trace is prime–archimedean source data**: the limit trace of the divisor
trace tower is the zeroth Taylor coefficient of the continued prime–Gamma source germ. -/
theorem opTrace_xiDivisorResolventSquare_eq_primeArchSourceMoment :
    opTrace (xiDivisorResolvent.comp xiDivisorResolvent) =
      ((analyticTraceMoments
          (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) 0 : ℝ) : ℂ) := by
  rw [opTrace_xiDivisorResolventSquare_eq_moment,
    primeArchSourceMoment_eq_xiCentralReciprocalMoment]

/-- The witness trace is real. -/
theorem opTrace_xiDivisorResolventSquare_im_eq_zero :
    (opTrace (xiDivisorResolvent.comp xiDivisorResolvent)).im = 0 := by
  rw [opTrace_xiDivisorResolventSquare_eq_moment]
  exact xiCentralReciprocalMoment_im_eq_zero 0

end

end RHTower
