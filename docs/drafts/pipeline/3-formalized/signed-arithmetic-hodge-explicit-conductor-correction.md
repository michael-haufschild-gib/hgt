# Explicit conductor cost of the Ramanujan prime correction

## Statement

For each prime \(p\) and positive integer horizon \(y\), the reciprocal Mangoldt mass
on the powers of \(p\) beyond \(y\) is at most \(2\log p/y\).

For each positive conductor \(m\), the actual correction majorant satisfies

\[
\operatorname{ramanujanCorrectionTail}(m,y)
\le \frac{4\phi(m)\log m}{y}.
\]

Consequently, every positive row \(n\) satisfies

\[
\left|\operatorname{poleProfileCorrection}(u_m,y,n)
 +(\log m+\operatorname{tameDifferent}(m))u_m(n)\right|
\le\frac{4\sqrt{\phi(m)}\log m}{y},
\]

where \(u_m=c_m/\sqrt{\phi(m)}\) is the actual normalized Ramanujan mode.

## Mathematical proof

The complete reciprocal Mangoldt mass on one prime tower is bounded by
\(\log p/(p-1)\). If \(p^K\le y\), the finite prefix contains the first \(K\) powers.
Subtracting their geometric sum gives the tail bound

\[
\frac{\log p}{p-1}\,p^{-K}.
\]

Take \(K=\lfloor\log_p y\rfloor\). Since \(y<p^{K+1}\) and
\(p/(p-1)\le2\), the tail is at most \(2\log p/y\).

The existing actual Ramanujan majorant is \(2\phi(m)\) times the sum of these
prime-tower masses over \(p\mid m\). Its infinite sum and finite prefix both
commute with this finite conductor-prime sum. Thus its tail is at most
\(4\phi(m)\sum_{p\mid m}\log p/y\).
The squarefree product of conductor primes divides \(m\), so
\(\sum_{p\mid m}\log p\le\log m\). Finally divide by the positive
\(\sqrt{\phi(m)}\), using the proved normalized row-correction identity.

Every input is an unconditional arithmetic theorem. Positivity of the conductor,
row and horizon specifies the domain; no analytic tail estimate is assumed.

## Formal closure

Module:
`formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TheRamanujanCorrectionHasAnExplicitConductorCost.lean`

Public declarations:

- `localMangoldtTail_le_geometric`
- `localMangoldtTail_le`
- `ramanujanCorrectionTail_le`
- `abs_normalizedRamanujan_correction_le`

The module passes its final individual `lake --old env lean` audit. The three
printed capstones, including all dependencies of the geometric helper, use only
`propext`, `Classical.choice`, and `Quot.sound`. Its olean exists because the
arithmetic family-residual module imports it. The programme umbrella imports it;
no umbrella build is performed.

## Scope

This controls the arithmetic correction uniformly in both row and horizon, with
explicit conductor dependence. Full prime residuals also contain the Mertens
remainder and floor roundoff. Gamma, continuous poles, energy separation and the
modal complement require their own estimates.
