# Real orbifold Rees dual-conormal jet tower

- **ID:** `deninger-real-orbifold-rees-dual-conormal-jet-tower`
- **Stage:** 3-formalized
- **Type:** SOURCE LOCAL THEOREM
- **Label:** `DAC_REAL_ORBIFOLD_REES_DUAL_CONORMAL_JET_TOWER`
- **Parent:** `deninger-archimedean-conormal-dual-conormal-trace-domain`
- **Statement:** Deninger's real transverse orbifold and exponent
  \(-2\) canonically produce the complete dual-conormal Taylor-jet
  tower. Its positive-time character is exactly
  \((1-e^{-2t})^{-1}\).

## 1. Source germ

Use the real orbifold
\[
 \mathbb R_{\ge0}\cong\mathbb R/\mu_2,\qquad x=r^2.             \tag{1}
\]
For the trivial real Hodge coefficient, the Rees sheaf is locally the
smooth \(\mu_2\)-invariant coefficient. A germ is therefore a smooth
function \(f(x)\), equivalently the even germ \(f(r^2)\).

Deninger's real-place flow is
\[
 \phi^t(x)=e^{-2t}x.                                           \tag{2}
\]
This is source data from the real Rees normal coordinate, not a value
read from \(\Gamma_{\mathbb R}\).

## 2. Dual-conormal jets

For \(k\ge0\), define the normalized Taylor functional
\[
 j_k(f)=\frac{1}{k!}\frac{d^k f}{dx^k}(0).                    \tag{3}
\]
The complete jet space is the Fréchet product
\[
 K'_\infty=\prod_{k\ge0}\mathbb R\,j_k,                        \tag{4}
\]
with finite truncations
\[
 K'_{\infty,\le N}=\prod_{0\le k\le N}\mathbb R\,j_k.          \tag{5}
\]
In the double coordinate \(r\), \(j_k\) is the normalized even
\(2k\)-jet. Odd \(r\)-jets do not descend through the infinite
Frobenius involution.

## 3. Flow law

For every smooth germ \(f\),
\[
\begin{aligned}
 j_k((\phi^t)^*f)
 &=j_k(f(e^{-2t}x))\\
 &=e^{-2kt}j_k(f).                                             \tag{6}
\end{aligned}
\]
Thus the \(k\)-th dual-conormal jet is an eigenline of weight
\(e^{-2kt}\). This is the \(\kappa=-2\) specialization of the
dual-conormal flow law \(e^{k\kappa t}\).

The supported density-current partner is the LF direct sum of normal
Dirac derivatives. Its \(k\)-th line has the complementary
positive-time-expanding weight \(e^{2(k+1)t}\). The paired
conormal/dual-conormal construction assigns the attracting
positive-time character to `(4)` and the opposite time direction to
the supported density-current tower.

## 4. Character theorem

`[PAPER-PROVED] [DAC_REAL_ORBIFOLD_REES_DUAL_CONORMAL_JET_TOWER]`

For \(t>0\), the trace of `(2)` on the finite jet truncation `(5)` is
\[
 \operatorname{Tr}\!\left((\phi^t)^*
   \mid K'_{\infty,\le N}\right)
 =\sum_{k=0}^N e^{-2kt}.                                      \tag{7}
\]
Since \(0<e^{-2t}<1\), the traces converge locally uniformly on
\((0,\infty)\):
\[
 \lim_{N\to\infty}
 \operatorname{Tr}\!\left((\phi^t)^*
   \mid K'_{\infty,\le N}\right)
 =\sum_{k\ge0}e^{-2kt}
 =\frac{1}{1-e^{-2t}}.                                       \tag{8}
\]
Consequently `(8)` defines the distributional character on every
compactly supported positive-time test.

The order-zero line \(j_0\) is the fixed coefficient fiber. Higher
normal jets are forced: deleting them changes `(8)` to a polynomial
and destroys the archimedean density.

## 5. Compatibility with existing Lean

The analytic character identity is already formalized unconditionally
in
`formal/GaloisForLFunctions/RHTower/DeningerArithmeticArchimedean.lean`.
In particular:

- `summable_deningerTimeTestLaplace_neg_even` proves summability of the
  jet-weighted Laplace samples;
- `tsum_deningerTimeTestLaplace_neg_even_eq_arch` proves
  \[
    \sum_{k\ge0}\Phi(-2k)
    =
    \int\phi(t)\frac{dt}{1-e^{-2t}}
  \]
  for every repository positive-time test.

The remaining item — the representation of the character as the flow
trace of the explicit jet-product object `(4)` — is now formalized in
`formal/GaloisForLFunctions/RHTower/DeningerReesJetTower.lean`; see the
Lean status section at the end of this card.

## 6. Boundary of the theorem

This theorem does not construct:

- the global stationary leaf/component \(Y_\infty\);
- the compactified Deninger source;
- the extension of `(8)` through \(t=0\);
- the \(b\)-trace anomaly or its normalization;
- the global Hodge/Green projection;
- the finite-prime periodic-orbit trace.

Those are the remaining clauses of
`DAC_ARCHIMEDEAN_CONORMAL_DUAL_CONORMAL_TRACE_DOMAIN`.

## Hostile audit

- The exponent \(-2\) is Deninger's real Rees flow law.
- The character uses all even orbifold jets, not a declared rank-one
  gamma coefficient.
- No Gamma function, zeta zero, RH premise, CCM object, or numerical
  computation defines the jet tower.
- Equality with the archimedean density is proved both algebraically
  by the geometric series and analytically for arbitrary positive-time
  tests in existing Lean.

## References

- Christopher Deninger, *A note on arithmetic topology and dynamical
  systems*, arXiv:math/0204274.
- Jesús A. Álvarez López, Yuri A. Kordyukov, and Eric Leichtnam,
  *A trace formula for foliated flows*, arXiv:2402.06671.

## Log

- 2026-07-27 — Identified Deninger's real Rees orbifold coordinate
  with the full dual-conormal even-jet product and derived the exact
  positive-time archimedean character.

## Lean status

### The jet tower, its flow law and its character landed

`formal/GaloisForLFunctions/RHTower/DeningerReesJetTower.lean`, alongside the already formalized
analytic identity in `DeningerArithmeticArchimedean.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerReesFlow`, `deningerRealJet` — the real-place Rees flow `(2)` on the orbifold coordinate
  and the normalized dual-conormal Taylor jet `(3)`.
- `deningerJetWeight`, `deningerJetWeight_eq_pow` — the weight `e^{-2kt}` and its geometric form.
- `deningerRealJet_reesFlow` — **`(6)`, the flow law**: for every `C^k` germ,
  `j_k((φ^t)^* f) = e^{-2kt} j_k(f)`, so the `k`-th jet is an eigenline.  This is the `κ = -2`
  specialization of the dual-conormal flow law.
- `deningerJetTowerOperator`, `deningerJetTower_trace` — **`(7)`**: on the truncation `(5)` the
  flow is the diagonal operator with those weights, and its trace is `∑_{k≤N} e^{-2kt}`.
- `deningerJetTower_summable`, `deningerJetTower_tsum` — **`(8)`**: for `t > 0` the weights are
  summable and sum to `(1 - e^{-2t})^{-1}`.
- `deningerJetTower_trace_tendsto` — the truncated traces converge to that character, which is the
  precise sense of `lim_N Tr(φ^t | K'_{∞,≤N})` in `(8)`.
- `deningerDensityCurrentWeight`, `deningerDensityCurrentWeight_one_lt` — the complementary
  supported density-current tower has the expanding weights `e^{2(k+1)t} > 1` in positive time, so
  the attracting character belongs to `(4)`, as the card assigns.

### Remaining

Nothing for the local character.  The clauses listed in §6 — the global stationary leaf, the
compactified source, the extension through `t = 0`, the `b`-trace anomaly, the global Hodge/Green
projection and the finite-prime periodic-orbit trace — are explicitly outside this theorem.
