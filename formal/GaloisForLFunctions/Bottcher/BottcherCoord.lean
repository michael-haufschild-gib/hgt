/-
# Böttcher tower — the complex Böttcher coordinate (log-series), brick 2

`log φ_c(z) = log z + ∑ₖ 2⁻⁽ᵏ⁺¹⁾·log(1 + c/(f_c^[k]z)²)`. The series converges on the
escape set: each term is bounded by `(‖c‖/‖z‖²)·(1/2)ᵏ` (via the complex-log estimate
`norm_clog_one_add_le` and the orbit growth), hence summable. This is the ℂ-analog of
`greenApprox_converges`; `Re(log φ_c) = G_c`, and the multivaluedness of the series
(branch of `log`) on disconnected `Ω_c` is where the dyadic monodromy lives.
-/
import GaloisForLFunctions.Bottcher.ComplexLogBound
import GaloisForLFunctions.Bottcher.GreenFunction

open Complex

namespace Bottcher

/-- The `k`-th term of the complex Böttcher log-series. -/
noncomputable def bottcherLogTerm (c z : ℂ) (k : ℕ) : ℂ :=
  (2 ^ (k + 1) : ℂ)⁻¹ * Complex.log (1 + c / ((quadratic c)^[k] z) ^ 2)

/-- **Term bound** `‖term_k‖ ≤ (‖c‖/‖z‖²)·(1/2)ᵏ` on the escape set. -/
theorem norm_bottcherLogTerm_le {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (k : ℕ) :
    ‖bottcherLogTerm c z k‖ ≤ ‖c‖ / ‖z‖ ^ 2 * (1 / 2) ^ k := by
  unfold bottcherLogTerm
  obtain ⟨hreg, hne⟩ := escape_regime_stable hc hz k
  set A := (quadratic c)^[k] z with hA
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hne
  have hA2 : (0 : ℝ) < ‖A‖ ^ 2 := by positivity
  have hw : ‖c / A ^ 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, div_le_iff₀ hA2]; nlinarith [hreg]
  have hlog := norm_clog_one_add_le hw
  have hnorm2 : ‖(2 ^ (k + 1) : ℂ)⁻¹‖ = (2 ^ (k + 1) : ℝ)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_ofNat]
  have hAz : ‖z‖ ≤ ‖A‖ := norm_le_orbit hc hz k
  have hcA : ‖c / A ^ 2‖ = ‖c‖ / ‖A‖ ^ 2 := by rw [norm_div, norm_pow]
  rw [norm_mul, hnorm2]
  calc (2 ^ (k + 1) : ℝ)⁻¹ * ‖Complex.log (1 + c / A ^ 2)‖
      ≤ (2 ^ (k + 1) : ℝ)⁻¹ * (2 * ‖c / A ^ 2‖) := by gcongr
    _ = (2 ^ (k + 1) : ℝ)⁻¹ * (2 * (‖c‖ / ‖A‖ ^ 2)) := by rw [hcA]
    _ ≤ (2 ^ (k + 1) : ℝ)⁻¹ * (2 * (‖c‖ / ‖z‖ ^ 2)) := by
        have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (by linarith) 2
        gcongr
    _ = ‖c‖ / ‖z‖ ^ 2 * (1 / 2) ^ k := by rw [pow_succ, div_pow, one_pow]; field_simp

/-- **The complex Böttcher log-series is summable** on the escape set. -/
theorem bottcherLogTerm_summable {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    Summable (bottcherLogTerm c z) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => norm_bottcherLogTerm_le hc hz k) ?_
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- The complex Böttcher coordinate's logarithm, `log φ_c(z) = log z + ∑ₖ termₖ`. -/
noncomputable def bottcherLog (c z : ℂ) : ℂ :=
  Complex.log z + ∑' k, bottcherLogTerm c z k

/-- The complex Böttcher coordinate `φ_c(z) = exp(log φ_c(z))`, with `|φ_c| = exp(G_c)`. -/
noncomputable def bottcherCoord (c z : ℂ) : ℂ := Complex.exp (bottcherLog c z)

end Bottcher
