# Route E almost-all pointwise-fallback hybrid

- **ID:** `ROUTE-E-ALMOST-ALL-POINTWISE-FALLBACK-001`
- **Stage:** 5-failed
- **Type:** SOURCE-MECHANISM NO-GO / SHARP THRESHOLD SURVIVOR
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** numerical sanity check only; no mathematical dependency
- **Lean status:** exact finite budget and sharp exponent threshold formalized in
  `MobiusExceptionalFallbackThreshold.lean`

## Proposed mechanism

At a block scale \(U\), use an almost-all short-interval theorem to obtain opposite-sign
Möbius partners at displacement \(U^{\eta+o(1)}\) for ordinary centers.  Put the exceptional
centers through an all-interval theorem with fallback displacement \(U^{\theta+o(1)}\).
If the exceptional set has size \(O(U^{1-\kappa+o(1)})\), one axis has aggregate displacement

\[
\sum_{u\asymp U}d(u)
\ll
U^{1+\eta+o(1)}+U^{1-\kappa+\theta+o(1)}.
\tag{1}
\]

For a balanced \(r\)-axis product, \(N=U^r\), the Cartesian product sum factorizes.  After the
Laplace normalization, its mixed-cube exponent is therefore

\[
\max\{\eta,\theta-\kappa\}.
\tag{2}
\]

## Exact killing threshold

The strict-half target forces

\[
\eta\le\frac12,
\qquad
\theta-\kappa\le\frac12,
\qquad\text{hence}\qquad
\boxed{\kappa\ge\theta-\frac12.}
\tag{3}
\]

This condition is independent of the number of balanced factors: tensoring more axes does not
amplify the exceptional saving, because both the displacement sum and the number of tuples
factorize.

For \(f=\mu\), Theorem 1.7 of Matomäki--Radziwiłł,
*Multiplicative functions in short intervals II* (arXiv:2007.04290), gives at fixed accuracy
\(0<\delta_0<10^{-3}\) and \(h=U^\eta\)

\[
E(U)\ll
U^{1-\eta\delta_0/15}
+U^{1-\delta_0^4/10^{16}}.
\tag{4}
\]

Thus its usable power saving is

\[
\kappa_{\rm MR}
=\min\left\{\frac{\eta\delta_0}{15},
             \frac{\delta_0^4}{10^{16}}\right\}
<10^{-28}.
\tag{5}
\]

Combining this with the all-interval arbitrary-Möbius-sign fallback
\(\theta=0.55+\varepsilon\) would require
\(\kappa\ge0.05+\varepsilon\) by `(3)`.  The gap is polynomial and terminal; changing the
balanced breadth does not repair it.

The 2026 improvement of Menon, *Improved bounds for multiplicative functions in almost all short
intervals* (arXiv:2607.15574), gives for Möbius the analogue of its Liouville mean-square bound

\[
\frac1U\int_U^{2U}
\left|\frac1h\sum_{x<n\le x+h}\mu(n)\right|^2dx
\ll
\frac{(\log\log h)^2}{(\log h)^2}
+\frac{(\log\log U)^4}{(\log U)^2}.
\tag{6}
\]

At a fixed sign-detection threshold, Chebyshev yields only a logarithmic exceptional density.
In exponent notation this is \(\kappa=0\), so it also cannot support a
\(U^{0.55+\varepsilon}\) fallback.

## Strongest positive survivor

Equation `(3)` is the exact hybrid-admissibility boundary.  It leaves one important mechanism
alive: the square-root \(E_3/E_4\) fallback already proved on the parent card has
\(\theta=\tfrac12+o(1)\).  Any genuine power-saving exceptional theorem is analytically
compatible with that fallback.

This survivor changes the open problem.  Almost-all cancellation is potentially useful only when
its exceptional centers are absorbed by the square-root exact-almost-prime incidence.  The
remaining obstruction is then local Hall capacity: a global bound for the number of exceptional
starts does not prevent them from concentrating in intervals whose balanced \(E_3/E_4\) target
set is too sparse.

Lean theorem
`exceptionalFallback_strictHalf_iff_requiredSaving` proves `(3)`;
`sum_displacement_le_good_add_exceptional` proves the exact finite split `(1)`.

## Hostile audit

- The \(0.55+\varepsilon\) fallback is retired, not almost-all input itself.
- Published exceptional sets consist of window starts violating a tolerance; they are not
  automatically the unmatched vertex set assumed in `(1)`.  Even ordinary windows retain their
  exact signed imbalance.  That separate failure is recorded in
  `route-e-almost-all-window-to-vertex-capacity.md`.
- A fixed-width Cartesian tensor does not multiply \(\kappa\); claiming otherwise double-counts
  the tuple normalization.
- The logarithmic 2026 mean-square gain is stronger analytically than earlier log errors but has
  no positive exceptional-set exponent.
- Replacing `(4)` by an unspecified \(o(U)\) exceptional set creates no strict-half estimate.
- The sharp threshold is elementary; standalone novelty is not claimed.  Its application removes
  a quantitatively impossible Route E branch and identifies square-root fallback plus local Hall
  control as the strongest survivor.

## Status

`RETIRED` for every fallback exponent \(\theta>1/2+\kappa\), in particular the published
\(0.55+\varepsilon\) arbitrary-sign all-interval fallback.  Square-root \(E_3/E_4\) fallback
survives and remains part of `OPEN-SOURCE-001`.
