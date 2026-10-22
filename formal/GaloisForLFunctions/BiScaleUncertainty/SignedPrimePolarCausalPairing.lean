import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalMoments

/-!
# The signed prime-polar pairing of the causal factorial source

The full pairing of a test `H` is `Σ_(n ≥ 2) Λ(n) n^(-1/2) H(log n) - ∫_0^∞ 2 cosh(x/2) H(x) dx`. For the
continuous, compactly supported causal factorial source `C_N`, the prime side equals that of the
factorial bi-null test and the polar side is computed from the two exponential moments. This gives an
exact closed form for the pairing and the explicit bound `O(log N / sqrt N)`.

## Main results

- `primeTerm_sourceFactorialCausal`: the prime sequence of `C_N` equals that of `factorialBiNull N`.
- `sourceFactorialCausal_admissible`: `C_N` has finite prime support, absolutely summable prime terms
  and an integrable polar term on `[0, ∞)`.
- `fullPairing_sourceFactorialCausal_eq`: `fullPairing C_N =
  (2 chebyshevBiNullProducer N - sourceFactorialCoefficient N · harmonicCorrection N) / sqrt N`.
- `abs_fullPairing_sourceFactorialCausal_le`:
  `|fullPairing C_N| ≤ (10 log(4N + 1) + 3 + 1/(4N)) / sqrt N`.

## Hypotheses

All results are unconditional; the only side condition is `1 ≤ N`. No bound on the error term of the
prime number theorem is assumed.
-/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower
noncomputable section
set_option autoImplicit false

/-- The prime-power terms of the causal source coincide with those of the factorial bi-null test,
because the two functions agree at every `log n`. -/
theorem primeTerm_sourceFactorialCausal {N : ℕ} (hN : 1 ≤ N) :
    primeTerm (sourceFactorialCausal N) = primeTerm (factorialBiNull N) := by
  funext n
  unfold primeTerm
  split_ifs with hn
  · rw [sourceFactorialCausal_at_log hN (by omega)]
  · rfl

/-- Admissibility of the causal source for the full pairing: finite prime support, absolutely summable
prime terms, and integrability of `2 cosh(x/2) · C_N(x)` on `[0, ∞)`. -/
theorem sourceFactorialCausal_admissible {N : ℕ} (hN : 1 ≤ N) :
    (Function.support (primeTerm (sourceFactorialCausal N))).Finite ∧
      Summable (fun n => |primeTerm (sourceFactorialCausal N) n|) ∧
      IntegrableOn (fun x => polarDensity x*sourceFactorialCausal N x) (Ici 0) := by
  rw [primeTerm_sourceFactorialCausal hN]
  refine ⟨(factorialBiNull_admissible N).1, (factorialBiNull_admissible N).2.1, ?_⟩
  exact ((continuous_polarDensity.mul (continuous_sourceFactorialCausal N)).integrable_of_hasCompactSupport
    ((hasCompactSupport_sourceFactorialCausal hN).mul_left (f := polarDensity))).integrableOn

/-- Exact pairing: `fullPairing C_N =
(2 chebyshevBiNullProducer N - sourceFactorialCoefficient N · harmonicCorrection N) / sqrt N`. -/
theorem fullPairing_sourceFactorialCausal_eq {N : ℕ} (hN : 1 ≤ N) :
    fullPairing (sourceFactorialCausal N) =
      (2*chebyshevBiNullProducer N-sourceFactorialCoefficient N*harmonicCorrection N)/Real.sqrt N := by
  have hip : Integrable (fun x => Real.exp (x/2)*sourceFactorialCausal N x) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
      (continuous_sourceFactorialCausal N)).integrable_of_hasCompactSupport
        ((hasCompactSupport_sourceFactorialCausal hN).mul_left)
  have him : Integrable (fun x => Real.exp (-(x/2))*sourceFactorialCausal N x) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2).neg).mul
      (continuous_sourceFactorialCausal N)).integrable_of_hasCompactSupport
        ((hasCompactSupport_sourceFactorialCausal hN).mul_left)
  have hp : (fun x => polarDensity x*sourceFactorialCausal N x) =
      fun x => Real.exp (x/2)*sourceFactorialCausal N x+Real.exp (-(x/2))*sourceFactorialCausal N x := by
    funext x
    unfold polarDensity
    rw [Real.cosh_eq]
    ring
  unfold fullPairing
  rw [primeTerm_sourceFactorialCausal hN, tsum_primeTerm_factorialBiNull,
    ← integral_weight_sourceFactorialCausal_eq_halfLine hN polarDensity, hp,
    integral_add hip him, integral_exp_half_sourceFactorialCausal hN,
    integral_exp_neg_half_sourceFactorialCausal hN]
  ring

/-- Unconditional size bound: `|fullPairing C_N| ≤ (10 log(4N + 1) + 3 + 1/(4N)) / sqrt N` for `N ≥ 1`. -/
theorem abs_fullPairing_sourceFactorialCausal_le {N : ℕ} (hN : 1 ≤ N) :
    |fullPairing (sourceFactorialCausal N)| ≤
      (10*Real.log (4*(N : ℝ)+1)+3+1/(4*(N : ℝ)))/Real.sqrt N := by
  rw [fullPairing_sourceFactorialCausal_eq hN, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hb := abs_chebyshevBiNullProducer_le hN
  obtain ⟨hc0,hc1⟩ := harmonicCorrection_bounds hN
  obtain ⟨ha0,ha1⟩ := sourceFactorialCoefficient_bounds hN
  calc
    _ ≤ |2*chebyshevBiNullProducer N|+|sourceFactorialCoefficient N*harmonicCorrection N| := abs_sub _ _
    _ = 2*|chebyshevBiNullProducer N|+sourceFactorialCoefficient N*harmonicCorrection N := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (mul_nonneg (by linarith) hc0)]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc1 (by linarith : 0 ≤ sourceFactorialCoefficient N)]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
