# BSY equality: the critical-line log integral counts exactly the off-line zeros

**Target (unconditional).** With `G(w) = (s−1)ζ(s)`, `s = 1/(1−w)`:
`lim_{r→1⁻} (1/2π)∫ log|G(re^{iθ})| dθ = (1/2π)∫ log|G(e^{iθ})| dθ`, hence (Jensen)
`(1/2π)∫_ℝ log|ζ(½+it)| dt/(¼+t²) = Σ_{Re ρ>½} m_ρ log|ρ/(ρ−1)|` (Balazard–Saias–Yor 1999).
Corpus has only `≤` (MUST-759) and RH ⟺ I = 0 (MUST-781).

## Paper proof
Let `m(r)` be the circle average of `log|G|` at radius `r`.
1. `log⁺` part: dominated convergence, dominant `A + 2log 2 − 2log|sin θ|` (existing growth bound).
2. No concentration at `w = 1`: the horodisc `|w − ¾| ≤ ¼` is `Re s ≥ 2`, where `|G| ≥ c > 0`. Poisson–Jensen
   at `x = r − η ∈ [½,1)` on the circle `|w| = r`: `log|G(x)| ≤ ∫ P(x, re^{iθ}) log|G(re^{iθ})|`; kernel
   `≥ 1/(4η)` on `|θ| ≤ η`; Poisson average of `log(2/|1−z|)` is `log(2/|1−x|) ≤ log(2/η)`. Hence
   `(1/2π)∫_{|θ|≤η} log⁻|G(re^{iθ})| ≤ 4η(C + 2log(1/η))` for all `r ≥ ½ + η`.
3. Arc `|θ| ≥ η`: ball `B = closedBall(−1, 2 − b)`, `b ≍ η²`, contains the arc for all `r ≤ 1` and avoids `1`;
   divisor extraction `log|G| = Σ_u d_u log|·−u| + log|g|` on `B` (finite, codiscrete ⇒ a.e. on circles);
   each `∫_{arc} log|re^{iθ} − u|` converges by dominated convergence (`log|sin(θ − arg u)|` dominant for
   `|u| = 1`); `log|g|` uniformly continuous.
4. `η → 0`.

## Lean plan
Corpus inputs: `HTGeometry.PoissonJensen.poissonJensen`, `circleAverage_re_herglotzRieszKernel_mul_log_of_mem_closedBall`,
mathlib `extract_zeros_poles(_log)`, `poissonKernel_def`, `AnalyticOnNhd.circleAverage_log_norm`;
ZetaHalfPlaneDiscJensen (`zetaDisc`, growth `exists_log_norm_zetaDisc_le`), ZetaDiscBoundaryJensenInequality,
ZetaCriticalLineJensenInequality (change of variables).

## Status
- 2026-10-05: opened.
- 2026-10-05: formalized (MUST-783), module ZetaCriticalLineJensenEquality, axiom-clean. Step 2 via the corpus Poisson–Jensen
  formula (HTGeometry.PoissonJensen.poissonJensen) turned into an inequality; step 3 via mathlib `extract_zeros_poles_log`
  plus `isDiscrete_of_codiscreteWithin` (exceptional set countable) and dominated convergence with pointwise limits off the
  countable boundary zeros. Stated in Jensen form (zetaDisc divisor); the s-plane multiplicity transport u = 1 − 1/ρ is not
  formalized (cosmetic).
