import GaloisForLFunctions.RHTower.Sieve.ZetaBoxLowerBound
import GaloisForLFunctions.RHTower.Sieve.ZetaThreeFourOne
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegStrip

/-!
# The prime sum on the zero-free strip, uniformly in the frequency

The box bound of `ZetaBoxLowerBound.lean` is elementary but its constant degrades with the frequency
range.  The corpus's zero-free region removes that defect: on the strip `|σ − 1| ≤ A/log⁹|t|`,
`|t| ≥ 9`, the estimate `‖1/ζ(σ+it)‖ ≤ (20/A)·log⁷|t|` holds, so

    ∑'_p cos(t log p)/p^σ  ≥  −log((20/A)·log⁷|t|) − π²/6,

uniformly in `t`.  Only a `log log |t|` is lost, which is exactly what a Halász estimate can absorb.

This is the input `MoebiusDistance.lean` calls "the zero-free-region input the corpus does not
have"; the corpus does have it, in `RHTower/ZetaLogDerivBound.lean`.
-/

namespace RHTower.Sieve

open Complex RHTower

/-- The prime sum against `log‖ζ‖` on the strip, with the tail made numeric. -/
theorem le_tsum_re_prime_cpow_of_log_le {σ t L : ℝ} (hσ : 1 < σ)
    (hL : L ≤ Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖) :
    L - Real.pi ^ 2 / 6
      ≤ ∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re := by
  have hre : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have hcomp := abs_log_norm_riemannZeta_sub_tsum_re_le hre
  have habs := abs_le.1 hcomp
  have hsq : (∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2)
      = ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
    rw [tsum_norm_sq_eq]
    congr 1
    ext p
    congr 2
    simp
  have htail : (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ))) ≤ Real.pi ^ 2 / 6 :=
    tsum_prime_rpow_le hσ.le
  rw [hsq] at habs
  linarith [habs.1, habs.2]

/-- **The prime sum on the zero-free strip.**  Uniform in the frequency, with only a `log log`
loss. -/
theorem le_tsum_re_prime_cpow_strip {σ t : ℝ} (ht : 9 ≤ |t|) (hσ1 : 1 < σ)
    (hσl : 1 - zetaLowerA / Real.log |t| ^ 9 ≤ σ)
    (hσu : σ ≤ 1 + zetaLowerA / Real.log |t| ^ 9) :
    -Real.log (20 / zetaLowerA * Real.log |t| ^ 7) - Real.pi ^ 2 / 6
      ≤ ∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have ht0 : (0 : ℝ) < |t| := by linarith
  have hexp2 := exp_two_lt_eight
  have hlogt : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hB0 : (0 : ℝ) < 20 / zetaLowerA * Real.log |t| ^ 7 := by positivity
  have hz : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_strip ht hσl hσu
  have hzpos : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_pos_iff.2 hz
  have hinv := RHTower.norm_inv_riemannZeta_le ht hσl hσu
  rw [norm_inv] at hinv
  have hlow : (20 / zetaLowerA * Real.log |t| ^ 7)⁻¹
      ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rw [inv_le_comm₀ hB0 hzpos]
    exact hinv
  have hlog : -Real.log (20 / zetaLowerA * Real.log |t| ^ 7)
      ≤ Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have hle := Real.log_le_log (by positivity) hlow
    rwa [Real.log_inv] at hle
  exact le_tsum_re_prime_cpow_of_log_le hσ1 hlog

end RHTower.Sieve
