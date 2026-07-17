import GaloisForLFunctions.RHTower.VonMangoldtGammaAllDepthCauchy
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Diagonal prime-channel obstruction for positive-log Mellin jets

The inverse-tilted Mellin source requires positive powers of the prime logarithm.  If those
powers are restored independently in each resolved prime channel, the resulting positive norm
has infinite energy already on the prime slice.  Consequently a positive unbalancing incidence
for the completed source cannot be diagonal in the prime channels: cancellation or coupling must
occur before the Hilbert norm is formed.
-/

namespace RHTower

noncomputable section

/-- The diagonal resolved-prime energy of the `r`th positive-log Mellin jet. -/
def primeMellinJetDiagonalEnergy (r : ℕ) (p : Nat.Primes) : ℝ :=
  finiteVonMangoldtRealWeight p * Real.log (p : ℝ) ^ (2 * r)

/-- **Diagonal positive-log obstruction.** Every positive-log Mellin jet has infinite diagonal
resolved-prime energy.  The proof uses only the prime specialization `Λ(p)=log p`, the uniform
lower bound `log p ≥ log 2`, and Euler's divergence of the prime harmonic series. -/
theorem not_summable_primeMellinJetDiagonalEnergy (r : ℕ) :
    ¬ Summable (primeMellinJetDiagonalEnergy r) := by
  intro hsum
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled : Summable (fun p : Nat.Primes =>
      Real.log 2 ^ (2 * r + 1) * (1 / (p : ℝ))) := by
    apply Summable.of_nonneg_of_le
    · intro p
      positivity
    · intro p
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
      have hlog2le : Real.log 2 ≤ Real.log (p : ℝ) :=
        Real.strictMonoOn_log.monotoneOn (by norm_num) hp0 hp2
      have hpow : Real.log 2 ^ (2 * r + 1) ≤
          Real.log (p : ℝ) ^ (2 * r + 1) :=
        pow_le_pow_left₀ hlog2pos.le hlog2le _
      calc
        Real.log 2 ^ (2 * r + 1) * (1 / (p : ℝ)) =
            Real.log 2 ^ (2 * r + 1) / (p : ℝ) := by ring
        _ ≤ Real.log (p : ℝ) ^ (2 * r + 1) / (p : ℝ) :=
          div_le_div_of_nonneg_right hpow hp0.le
        _ = primeMellinJetDiagonalEnergy r p := by
          rw [primeMellinJetDiagonalEnergy, finiteVonMangoldtRealWeight,
            ArithmeticFunction.vonMangoldt_apply_prime p.prop, pow_succ]
          ring
    · exact hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff
      (pow_ne_zero (2 * r + 1) hlog2pos.ne')).mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

end

end RHTower
