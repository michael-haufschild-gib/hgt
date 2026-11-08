# Depth Density `o(T)` and Vanishing Critical-Line Logarithmic Mean (B57)

- **ID:** b57-depth-density-and-critical-line-log-mean
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0811/obstacles-summary.md` §2.5 (B57)
- **Statement:** Determine unconditionally whether $\sum_{T < \gamma \le 2T,\, \beta > 1/2} m_\rho(\beta - \tfrac{1}{2}) = o(T)$ — equivalently $T^{-1}\int_T^{2T} \log\|\zeta(\tfrac{1}{2}+it)\|\,dt \to 0$, $I(\tfrac{1}{2} + x + it) \to 0$ as $x \to +\infty$, density-zero horizon damping deficits, and $N(\tfrac{1}{2} + u/\log T, T) = o(T\log T)$ for every fixed $u > 0$ — and formalize the complete unconditional resolution and its corollaries in Lean 4.

## Goal
Resolve B57 unconditionally and formalize the theorem together with its full equivalence and implication chain (`ClusteringLogMeanAndMollifierEquivalence`, `TheLogMeanIsTheInnerMassAtInfinity`, `TheBulkReadingOfTheLogMean`, cumulative depth density, critical-scale proportion, and density-one local Weil positivity B28).

## Gates
- [x] 0 → 1  in-progress: internal corpus and external SOTA audited; invariants and fake-exclusion gates isolated
- [ ] 1 → 2  fully-proven: complete dependency-closed paper proof, `[PROVED HERE]`, zero open core
- [ ] 2 → 3  formalized: Lean theorems compiled with `lake --old env lean`, `#print axioms` clean (`propext`, `Classical.choice`, `Quot.sound`)

## Frontier & Discrimination Gates
1. **Known unconditional bounds (`ζ`):**
   - Lower floor: $T^{-1}\int_T^{2T} \log\|\zeta(\tfrac{1}{2}+it)\|\,dt \ge -O(\log T / T)$ (`exists_logIntegral_floor`), via two-sided all-heights Littlewood edge budget (`exists_zetaLine_littlewood_edge_budget_all_heights`).
   - Linear ceiling: $\sum_{T < \gamma \le 2T, \beta > 1/2} m_\rho(\beta - \tfrac{1}{2}) \le C T$ (`exists_eventually_offLineMoment_le_mul`, numerically $\le 0.067 T$).
   - Exponential tail: $\sum_{T < \gamma \le 2T, \beta \ge 1/2 + R/\log T} m_\rho(\beta - \tfrac{1}{2}) \le B_e e^{-R/28} T + K_e \log^2 T$ (`exists_dyadic_offLineTailMoment_le_exp`).
   - Second moment: $\sum_{0 < \gamma \le V} m_\rho (\beta - \tfrac{1}{2})_+^2 = o(V)$ (`tendsto_offLineSecondMoment_div`).
   - Gaussian law at $\sqrt{\tfrac{1}{2}\log\log T}$: `tendsto_log_norm_zeta_law_gaussian`.
2. **Mandatory fake-exclusion gates for any valid proof:**
   - *Impure Euler factor (`T5`):* $(1 - c p_0^{-s})\zeta(s)$ ($|c| > \sqrt{p_0}$) has critical-line log-mean $\log(|c|/\sqrt{p_0}) > 0$; mechanism must use the functional equation / symmetry across $\operatorname{Re} s = 1/2$.
   - *Abstract strip zero configurations (`NearLineDensityBesselCertificateAndSeparation`):* `clusteredModel` satisfies Riemann–von Mangoldt, $> 68\%$ simple critical zeros, reflection symmetry, and arbitrary-rate Selberg exponential tails yet violates `(L)`; mechanism must use the Dirichlet series / Euler product / explicit formula of $\zeta$, not abstract zero-census axioms alone.
   - *Mollified $L^2$ + Jensen barrier (`SubexponentialMollifierLengthAndWindowSpikes`):* Every normalized complex Dirichlet polynomial $M$ of length $N \le \exp(T^{1/60})$ satisfies $\int_T^{2T} \|\zeta M(\tfrac{1}{2}+it)\|^2 dt \ge (1 + \frac{\log T}{8\log T + 6\log N})T$; polynomial-length second-moment + Jensen cannot reach $o(T)$.
