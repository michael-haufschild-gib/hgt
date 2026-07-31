import GaloisForLFunctions.RHTower.XiDivisorTraceTowerWitness
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace

/-!
# The witness trace is the first central reciprocal moment

The divisor-side trace-tower witness has a computable limit: the operator trace of the
Schatten-1 resolvent square `diag(μ_q⁻²)` is the sum of the reciprocal squares of the
spectral points — which the corpus already identifies as the **first central reciprocal
moment** of the Xi divisor (`xiCentralReciprocalMoment 0`, the Li/Keiper-type constant whose
reality the corpus proves unconditionally).

* `xiDivisorResolventSquare_basis` — the resolvent square is diagonal with entries the
  reciprocal squares;
* `opTrace_xiDivisorResolventSquare` — its trace is `Σ' μ_q⁻²`, by basis-independence of the
  trace on Hilbert–Schmidt products evaluated on the divisor basis;
* `opTrace_xiDivisorResolventSquare_eq_moment` — **the trace equals
  `xiCentralReciprocalMoment 0`**: the trace-tower witness's limit trace is an actual
  arithmetic constant of the corpus, closing the loop between the operator-theoretic tower
  and the moment/log-derivative layer.

Unconditional throughout.
-/

namespace RHTower

noncomputable section

open Complex ContinuousLinearMap

/-- The resolvent square acts on the divisor basis by the reciprocal squares. -/
theorem xiDivisorResolventSquare_basis (q : XiZeroCopy) :
    (xiDivisorResolvent.comp xiDivisorResolvent) (xiDivisorHilbertBasis q) =
      xiZeroCopyReciprocalSquare q • xiDivisorHilbertBasis q := by
  rw [ContinuousLinearMap.comp_apply]
  simp only [xiDivisorResolvent]
  rw [xiDivisorDiagonal_basis, map_smul, xiDivisorDiagonal_basis, smul_smul]
  congr 1
  rw [xiZeroCopyReciprocalSquare, sq]
  rfl

/-- The trace of the resolvent square is the sum of the reciprocal squares. -/
theorem opTrace_xiDivisorResolventSquare :
    opTrace (xiDivisorResolvent.comp xiDivisorResolvent) =
      ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q := by
  rw [show xiDivisorResolvent.comp xiDivisorResolvent =
      xiDivisorResolvent ∘L xiDivisorResolvent from rfl]
  rw [opTrace_comp_eq_tsum_basis xiDivisorResolvent_isHilbertSchmidt
    xiDivisorResolvent_isHilbertSchmidt xiDivisorHilbertBasis]
  apply tsum_congr
  intro q
  rw [show (xiDivisorResolvent ∘L xiDivisorResolvent) (xiDivisorHilbertBasis q) =
      xiZeroCopyReciprocalSquare q • xiDivisorHilbertBasis q from
    xiDivisorResolventSquare_basis q]
  rw [inner_smul_right]
  have hone : (inner ℂ (xiDivisorHilbertBasis q) (xiDivisorHilbertBasis q)) =
      (1 : ℂ) := by
    have h := xiDivisorHilbertBasis.orthonormal
    rw [orthonormal_iff_ite] at h
    have := h q q
    rwa [if_pos rfl] at this
  rw [hone, mul_one]

/-- **The witness trace is the first central reciprocal moment**: the limit trace of the
divisor trace tower is `xiCentralReciprocalMoment 0` — an arithmetic constant the corpus
already proves real.  The operator-theoretic tower and the moment/log-derivative layer meet
in one number. -/
theorem opTrace_xiDivisorResolventSquare_eq_moment :
    opTrace (xiDivisorResolvent.comp xiDivisorResolvent) =
      xiCentralReciprocalMoment 0 := by
  rw [opTrace_xiDivisorResolventSquare, ← tsum_xiZeroCopyReciprocalSquare_pow 0]
  apply tsum_congr
  intro q
  rw [zero_add, pow_one]

end

end RHTower
