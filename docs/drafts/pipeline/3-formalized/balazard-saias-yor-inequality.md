# Balazard–Saias–Yor inequality

**Statement (proved).** For every finite set `Z` of zeros of `ζ` with `Re ρ > ½`:
`Σ_{ρ∈Z} log(|ρ|/|1−ρ|) ≤ (1/2π) ∫_ℝ log|ζ(½+it)| dt/(¼+t²)`, with integrable integrand.
Corollaries: the integral is `≥ 0`; if it is `≤ 0`, RH holds.

**Status.** Stage 3, unconditional (`RHTower.integrable_and_sum_log_le_integral_log_norm_zeta`,
`integral_log_norm_zeta_criticalLine_nonneg`,
`riemannHypothesis_of_integral_log_norm_zeta_criticalLine_le_zero`).

**Proof.**
1. `s = 1/(1−w)` maps `|w| < 1` onto `Re s > ½`; `G(w) = (s−1)ζ(s)` (`zetaEntire`), `G(0) = 1`.
2. Jensen (mathlib) on `|w| ≤ r < 1`: circle average of `log|G|` `≥ Σ log(r/|u|)`, `u = 1 − 1/ρ`.
3. `|ζ(s)| ≤ 5√(|s|+2)` on `Re s ≥ ½` ⇒ `log|G(w)| ≤ A − 2 log|1−w| ≤ A − 2 log|sin θ|`.
4. Reverse Fatou (lintegral of `F − f_r`) as `r → 1`: boundary integrability and the inequality.
5. `θ(t) = π − 2 arctan 2t`: `1/(1−e^{iθ}) = ½ + it`, `|θ'| = 1/(¼+t²)`.
6. `log|s−1| = ½ log(¼+t²)` integrates to `0` (circle average of `log|w−1|` vanishes).

**Open (equality).** `= Σ_{all Re ρ>½}` needs uniform integrability of `log⁻|G|` near `w = 1`
(local zero counting of `ζ` on Apollonius arcs at large height). The one-sided form already gives
the criterion direction `∫ ≤ 0 ⇒ RH`.

**Next use.** Combined with a mollifier `M`, Jensen's inequality gives
`Σ log|ρ/(1−ρ)| ≤ ½ log ∫|ζM|² dμ − log|M(1)|` once `∫ log|M| dμ ≥ log|M(1)|` is proved (same
reverse-Fatou argument for bounded `M`): a quantitative Nyman–Beurling bridge.

**Mollified form (MUST-760).** For `M` entire, bounded on `Re s ≥ ½`, `M(1) ≠ 0`:
`Σ log(|ρ|/|1−ρ|) ≤ ½ log((1/2π)∫|ζM|² dt/(¼+t²)) − log|M(1)|`
(`RHTower.sum_log_le_half_log_meanSquare_zeta_mul`), hence
`riemannHypothesis_of_forall_mollified_meanSquare_le`: RH if `inf_M ∫|ζM|²dμ/|M(1)|² = 1`.
Open: necessity (RH ⇒ the infimum is 1 over Dirichlet polynomials), and the exact value
`(1/2π)∫|ζ|² dt/(¼+t²) = log 2π − γ` (Mellin–Plancherel of `{x}`), which with `M = 1` would give
the unconditional bound `Σ_{Re ρ>½} log|ρ/(1−ρ)| ≤ ½ log(log 2π − γ) ≈ 0.116`.

**Explicit constant (MUST-761).** `(1/2π)∫|ζ(½+it)|² dt/(¼+t²) = log 2π − γ`
(`RHTower.integrable_and_integral_norm_sq_zeta_criticalLine`), so unconditionally
`Σ_{Re ρ>½} log(|ρ|/|1−ρ|) ≤ ½ log(log 2π − γ)`
(`sum_log_norm_div_le_half_log_log_two_pi_sub_eulerMascheroni`). Next: the Gram entries
`(1/2π)∫|ζ|²(m/n)^{it}dt/(¼+t²)` (Vasyunin) to evaluate `∫|ζM|²dμ` for Dirichlet polynomials.

**Gram form (MUST-762).** `A(m,n) = ∫_0^∞ {x/m}{x/n} dx/x²`; for real `a` on positive integers,
`(1/2π)∫|ζM|²dμ = Σ a_m a_n A(m,n)`, `(Σ a_n/n)² ≤ Σ a_m a_n A(m,n)`, and RH if the ratio can be
made `≤ 1 + ε` for every `ε` (`RHTower.riemannHypothesis_of_fractGram_form`). Open: closed forms of
`A(m,n)` (Vasyunin cotangent sums) and the converse (RH ⇒ the infimum is 1).

**Poisson–Jensen family (MUST-764).** Any centre `s₀` (`Re s₀ > ½`, `ζ(s₀) ≠ 0`, `s₀ ≠ 1`):
`Σ log(|ρ+s̄₀−1|/|ρ−s₀|) ≤ ∫ log|ζ(½+iτ)|P_{s₀}(τ)dτ − log|ζ(s₀)| + log(|s₀|/|s₀−1|)`
(`RHTower.integrable_and_sum_log_blaschke_le`); local version of BSY.

**Gap law and terminus (MUST-766).** Off RH, `E(s₀) ≥ log 3` at a chain centre
(`RHTower.exists_log_three_le_poissonJensenDefect_of_not_riemannHypothesis`). Terminus of the lane:
`E(s₀)` equals (under the equality form) `½ Σ_ρ |log|(ρ+s̄₀−1)/(ρ−s₀)||`, an absolute-value functional
of the divisor; the explicit formula reaches only analytic reflection-odd test functions (whose
divisor sums cancel in reflected pairs), so E has no prime-side evaluation. Upper bounds for E go
through local mollified mean squares at scale `β − ½` and stop at the zero-density barrier
`β − ½ ≪ 1/log γ`.

**Correction and converse (2026-10-05, CANNOT-491, MUST-780).**
- The Gram form (MUST-762) is vacuous: `Σ a_m a_n A(m,n) ≥ (49/48)(Σ a_n/n)²` for every real Dirichlet polynomial
  (`RHTower.fractGram_form_ge`, `not_forall_fractGram_form_le`). Its "converse" RH ⇒ inf = 1 is false.
- For the class of MUST-760 (entire, bounded on Re s ≥ ½) the converse holds:
  `RHTower.riemannHypothesis_iff_forall_mollified_meanSquare_le`, with witnesses `M = −sP(s)/(s−1)` from the
  Báez-Duarte approximants (`bdMollifier`). The equality direction of BSY itself remains open.

**Criterion closed (2026-10-05, MUST-781).** `RH ⟺ ∫ log|ζ(½+it)| dt/(¼+t²) = 0`
(`RHTower.riemannHypothesis_iff_integral_log_norm_zeta_criticalLine_eq_zero`), from
`I ≤ log((1+d)/(1−d))` for every real NB residual d < 1 and RH ⇒ d → 0. Also `tanh(I/2) ≤ d` unconditionally.
Still open: the unconditional equality `I = Σ_{Re ρ>½} log|ρ/(1−ρ)|`.
