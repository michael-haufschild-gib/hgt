# Route E moving terminal-kernel antiscale resonance

- **ID:** `ROUTE-E-MOVING-TERMINAL-KERNEL-RESONANCE-001`
- **Stage:** 2-fully-proven
- **Type:** `[QUANTITATIVE MOVING PRODUCER-CLASS NO-GO]` / `[POSITIVE MASS-SPREAD CONSTRAINT]`
- **Scientific status:** `[PAPER-PROVED] [INTERNAL COLLISION-AUDITED] [EXTERNAL AUDIT OMITTED BY INSTRUCTION]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **RH used:** no
- **Computation used:** no

## Purpose

Static regular kernels are recurrent, but Route E permits kernels moving with physical aperture.
This theorem proves that motion alone does not evade antiscale coherence.  Any absolutely summable
kernel confined to a terminal logarithmic prime band is quantitatively annihilated at the explicit
physical resonance \(t_Y=\pi/\log Y\).  Escape requires inverse-square mass growth in band width,
cross-scale support, a singular renormalized principal part, or signed cancellation before norm.

## Exact theorem

Let \(Y>1\), \(\eta\ge0\), and define the terminal logarithmic band

\[
 \mathcal P(Y,\eta)=
 \left\{p:\ 0\le\log Y-\log p\le\eta\log Y\right\}.    \tag{1}
\]

Let \(K=(K_{pq})\) be a complex kernel with \(\sum_{p,q}|K_{pq}|<\infty\), supported on
\(\mathcal P(Y,\eta)^2\).  Put

\[
 \mathcal Q_K(t)=\sum_{p,q}K_{pq}(1+p^{it})\overline{(1+q^{it})}. \tag{2}
\]

Then at the explicit moving frequency \(t_Y=\pi/\log Y\),

\[
 \boxed{
 |\mathcal Q_K(t_Y)|
 \le (\pi\eta)^2\sum_{p,q}|K_{pq}|.
 }                                                       \tag{3}
\]

Consequently, for any moving family \(K_Y,\eta_Y\), if

\[
 \eta_Y^2\sum_{p,q}|K_{Y,pq}|\longrightarrow0,          \tag{4}
\]

then \(\mathcal Q_{K_Y}(\pi/\log Y)\to0\).  A lower bound \(|\mathcal Q|\ge c>0\) forces
\(\sum|K_{Y,pq}|\ge c/(\pi^2\eta_Y^2)\).

## Proof

For \(p\in\mathcal P(Y,\eta)\), set \(\theta_p=\pi\log p/\log Y\).  Since
\(e^{i\pi}=-1\) and the unit-circle chord is bounded by arc length,

\[
 |1+p^{it_Y}|=|e^{i\theta_p}-e^{i\pi}|
 \le|\theta_p-\pi|
 ={\pi\over\log Y}(\log Y-\log p)
 \le\pi\eta.                                           \tag{5}
\]

Thus every supported pair term in `(2)` has norm at most
\((\pi\eta)^2|K_{pq}|\).  Unsupported terms vanish.  Absolute convergence, triangle inequality,
and summation of this pointwise majorant give `(3)`.  Statement `(4)` follows immediately.

## Hostile audit

1. Frequency is explicit and coupled to moving aperture; no qualitative far-future recurrence is
   used.
2. Complete ordered prime-pair series is retained.
3. Kernel may be complex, non-Hermitian, indefinite, off-diagonal, and aperture dependent.
4. The theorem needs terminal log-band support.  Cross-scale entries remain outside it.
5. It gives a sharp inverse-square necessary mass law, not a Möbius estimate.  `OPEN-SOURCE-001`
   remains open.

## Positive survivor

A viable moving quadratic Route E source must do at least one of the following:

- carry entrywise mass \(\gtrsim\eta^{-2}\) in a terminal band and canonically renormalize it;
- couple terminal primes to logarithmically separated source scales;
- contain a non-absolutely-summable singular principal part; or
- cancel signed terminal shells before applying positive norm.

It must additionally produce \(D_{\rm anti}\) or within-parity variation at physical-power
strength.  “Moving off-diagonal kernel” without a mass/spread audit is no longer sufficient.

## Formalization target

Formalize terminal-log-band seam bound, pair-term majorant, complete `tsum` inequality, and explicit
smallness corollary over `Nat.Primes × Nat.Primes`.
