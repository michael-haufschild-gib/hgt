# Stable bounded-generator causal horizon

- **ID:** stable-bounded-generator-causal-horizon
- **Stage:** 3-formalized
- **Type:** CANDIDATE
- **Date:** 2026-07-28
- **Parent article:** `local-horizon-quantum-return-law-main.tex`

## Exact question

What remains of the universal common-response-jet law when every observed
coefficient has a known nonzero calibration error?

## Frontier

- `[CORPUS]` exact scalar-prefix cancellation and the critical \(N/e\)
  causal boundary are formalized.
- `[LITERATURE]` robust Hamiltonian-learning methods control reconstruction
  under preparation, measurement and shot error. Calibration-aware quantum
  speed limits profile nuisance parameters through information geometry.
  Neither supplies an arbitrary-error-profile continuation bound for two
  bounded generators with a common approximate scalar jet.
- `[OPEN CORE]` expose the complete finite calibration contribution and
  retain the exact dynamical tail.

## Conjecture

`[CONJECTURE]` Let \(X\) be a complete complex normed space,
\(\|G\|,\|K\|\le\Lambda\), \(x\in X\), and
\(\ell:X\to\mathbb C\) continuous. Put
\[
 F_G(z)=\ell(e^{zG}x),\qquad u=\|z\|\Lambda.
\]
For any nonnegative error profile \(\eta_0,\ldots,\eta_{N-1}\), if
\[
 |\ell(G^m x)-\ell(K^m x)|\le\eta_m,\qquad 0\le m<N,
\]
then
\[
\begin{split}
 |F_G(z)-F_K(z)|
 &\le
 \sum_{m=0}^{N-1}\frac{\|z\|^m}{m!}\eta_m\\
 &\quad+
 2\|\ell\|\|x\|
 \left(e^u-\sum_{m=0}^{N-1}\frac{u^m}{m!}\right).
\end{split}
\tag{S}
\]
If \(N>0\) and \(u\le N/e\), then
\[
 |F_G(z)-F_K(z)|
 \le
 \sum_{m=0}^{N-1}\frac{\|z\|^m}{m!}\eta_m
 \frac{4\|\ell\|\|x\|}{\sqrt{2\pi N}}.
\tag{SC}
\]

## Hostile attack before proof

1. **Does error leak into the tail?** No. The first \(N\) terms are retained
   rather than cancelled; every later coefficient uses only the generator
   norm bound.
2. **Are the units wrong?** \(\eta_m\) bounds the observed scalar
   \(m\)-th generator coefficient itself. Multiplication by
   \(\|z\|^m/m!\) gives response units.
3. **Does the theorem hide a uniform-error assumption?** No. Every order has
   its own arbitrary nonnegative error budget.
4. **Does it claim device feasibility?** No. It gives the exact error budget
   a device must meet; whether hardware meets it is an empirical question.
5. **Can the finite head be reduced further universally?** No without
   assumptions relating the errors at different orders. Aligned scalar
   coefficient errors can saturate the triangle bound.

Verdict: `SURVIVES PRELIMINARY ATTACK`.

## Dependency-closed paper proof

Absolute convergence gives
\[
 F_G(z)-F_K(z)=
 \sum_{m=0}^{N-1}\frac{z^m}{m!}
   [\ell(G^m x)-\ell(K^m x)]
 +\sum_{j=0}^{\infty}\frac{z^{N+j}}{(N+j)!}
   [\ell(G^{N+j}x)-\ell(K^{N+j}x)].
\tag{1}
\]
The triangle inequality and the assumed coefficient budgets bound the
finite sum by
\[
 \sum_{m=0}^{N-1}\frac{\|z\|^m}{m!}\eta_m.
\tag{2}
\]
For every later order,
\[
 |\ell(G^m x)-\ell(K^m x)|
 \le2\|\ell\|\|x\|\Lambda^m.
\tag{3}
\]
Therefore the infinite tail is at most
\[
 2\|\ell\|\|x\|
 \sum_{m=N}^{\infty}\frac{u^m}{m!}
 =
 2\|\ell\|\|x\|
 \left(e^u-\sum_{m=0}^{N-1}\frac{u^m}{m!}\right).
\tag{4}
\]
Equations (1)--(4) prove `(S)`. At \(u\le N/e\), the already paper-proved
critical exponential-tail theorem bounds the parenthesis in (4) by
\[
 2/\sqrt{2\pi N}.
\]
This proves `(SC)`.

All proof obligations are closed on paper.

## Status

- `[LEAN-PROVED]` exact statements `(S)` and `(SC)`.
- Formal declarations:
  - `boundedGeneratorResponse_difference_eq_prefix_add_tail`
  - `boundedGeneratorResponse_difference_norm_le_of_approx_prefix`
  - `boundedGeneratorResponse_approx_prefix_critical_bound`
- `[NOVELTY UNVERIFIED]` search cannot establish priority.
