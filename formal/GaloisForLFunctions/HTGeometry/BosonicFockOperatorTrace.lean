import GaloisForLFunctions.HTGeometry.BosonicFockOperatorRealization
import GaloisForLFunctions.HTGeometry.LpDiagonalOperator

/-!
# Operator traces of the second quantization

When the one-particle contraction is square-summable the second quantization is Hilbert–Schmidt, so
each of its powers from the second onward is a product of two Hilbert–Schmidt operators and has a
convergent, basis-independent operator trace.  That trace is the occupation moment: the sum of the
corresponding powers of the occupation monomials.

Consequently, at every genus at least one, the trace expansion of the regularized determinant is an
identity between the determinant and genuine operator traces, not merely between the determinant and
sums of eigenvalue powers.
-/

open scoped BigOperators

noncomputable section

namespace HTGeometry

variable {ι : Type*} [DecidableEq ι]

/-- Square-summability of the one-particle contraction gives square-summability of the whole
occupation spectrum. -/
theorem summable_norm_bosonicEigenvalue_sq (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (2 : ℕ))) :
    Summable (fun ν : ι →₀ ℕ => ‖bosonicEigenvalue p ν‖ ^ (2 : ℕ)) :=
  (isHilbertSchmidt_ellTwoDiagonal_iff _ _).mp
    ((isHilbertSchmidt_bosonicSecondQuantization_iff p hp_lt).mpr hsum)

/-- In the square-summable regime the second quantization is the Hilbert–Schmidt diagonal of its
eigenvalue family. -/
theorem bosonicSecondQuantization_eq_diagOp (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (2 : ℕ))) :
    bosonicSecondQuantization p hp_lt
      = HilbertSchmidt.diagOp (bosonicEigenvalue p)
          (summable_norm_bosonicEigenvalue_sq p hp_lt hsum) := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext ν
  rw [bosonicSecondQuantization_eq, ellTwoDiagonal_apply, HilbertSchmidt.diagOp_apply]

/-- **The power traces of the second quantization are the occupation moments.**  From the second
power onward the operator trace converges and equals the sum of that power of the occupation
monomials. -/
theorem opTrace_bosonicSecondQuantization_pow (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (2 : ℕ))) (m : ℕ) :
    ContinuousLinearMap.opTrace ((bosonicSecondQuantization p hp_lt) ^ (m + 2))
      = ∑' ν : ι →₀ ℕ, bosonicEigenvalue p ν ^ (m + 2) := by
  rw [bosonicSecondQuantization_eq_diagOp p hp_lt hsum]
  exact HilbertSchmidt.opTrace_diagOp_pow _ _ (norm_bosonicEigenvalue_le_one p hp_lt) m

/-- **The trace expansion of the regularized determinant, in operator traces.**  At every genus at
least one, and for a square-summable one-particle contraction, the logarithm of the order-`g+1`
regularized determinant of `I - x Γ` is the series of operator traces of the powers of `Γ`, starting
at the determinant order. -/
theorem regularizedFredholmDet_eq_exp_neg_opTrace_series (k : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (2 : ℕ))) {x : ℂ} (hx : ‖x‖ < 1) :
    regularizedFredholmDet (k + 1) p x
      = Complex.exp (-∑' m : ℕ, x ^ (m + (k + 1 + 1)) / ((m + (k + 1 + 1) : ℕ) : ℂ) *
          ContinuousLinearMap.opTrace
            ((bosonicSecondQuantization p hp_lt) ^ (m + (k + 1 + 1)))) := by
  have hsum' : Summable (fun a => ‖p a‖ ^ (k + 1 + 1)) := by
    refine hsum.of_nonneg_of_le (fun a => by positivity) (fun a => ?_)
    exact pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (hp_lt a)) (by omega)
  rw [regularizedFredholmDet_eq_exp_neg_traceSeries (k + 1) p hp_lt hsum' hx]
  congr 2
  refine tsum_congr fun m => ?_
  congr 1
  have hidx : m + (k + 1 + 1) = (m + k) + 2 := by omega
  rw [hidx, opTrace_bosonicSecondQuantization_pow p hp_lt hsum (m + k)]

end HTGeometry

end
