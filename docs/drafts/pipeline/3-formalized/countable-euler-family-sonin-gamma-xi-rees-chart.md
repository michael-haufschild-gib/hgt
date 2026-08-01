# Countable Euler-family Sonin--Gamma--Xi Rees chart

- **ID:** `countable-euler-family-sonin-gamma-xi-rees-chart`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / SOURCE-GLOBAL BRIDGE
- **Scientific status:** `[LEAN-PROVED] [NOT RH] [NO NOVELTY CLAIM]`
- **Source:**
  - `../1-in-progress/polarized-critical-rees-corona-transgression-rh.md`;
  - `../../formal/GaloisForLFunctions/RHTower/SoninSourceGlobalGradedCorona.lean`;
  - `../../formal/GaloisForLFunctions/RHTower/SoninCofinalMobiusGammaXiIncidence.lean`.
- **Statement:** Every countable family of Euler points uniformly separated from
  `Re s = 1` is reconstructed by one critical normal path and one strictly
  cofinal Sonin schedule at the exact pointwise Gamma graph grades.

## Goal

Remove finite-packet dependence from the actual Möbius--Gamma--Xi scalar
incidence.  A countable Euler family with an accumulation point in `s > 1`
determines a holomorphic Euler-side germ.  The theorem therefore closes the
scalar determining-family schedule problem before any Xi divisor is selected.

It does not construct the pre-scalarized Rees--Hardy morphism, prove
contractivity, or prove RH.

## Theorem

Fix real parameters satisfying

\[
0<a,\qquad 0<c<d<a,\qquad 1<r,\qquad a<rc.
\tag{1}
\]

Let \(b>1\), and let \(s_i\ge b\) for every \(i\in\mathbb N\).  Then there
exist

\[
\sigma:\mathbb N\to(1,\infty),\qquad
u:\mathbb N\times\mathbb N\to[0,\infty),\qquad
N:\mathbb N\to\mathbb N
\]

such that:

1. \(\sigma_n\to1\);
2. every tangential path fixes its Euler point exactly,
   \[
   \operatorname{mobiusCriticalBoundaryParameter}(\sigma_n,u_{n,i})=s_i;
   \tag{2}
   \]
3. \(N\) is strictly increasing; and
4. for every fixed \(i\), the genuine Sonin dilation-corner transport at
   depth \(N(n)\) satisfies
   \[
   {\cal T}_{n,i}\longrightarrow
   \operatorname{continuedPrimeArchSourceRelativeTrace}
     \bigl(\operatorname{xiWardCenteredCoordinate}(s_i)\bigr).
   \tag{3}
   \]

Here \({\cal T}_{n,i}\) is exactly
`soninCofinalMobiusGammaXiWardMovingTransport`; no new fitted scalar
functional is introduced.

## Proof

Use the already canonical fixed-Euler normal path

\[
\sigma_n
=1+\frac{b-1}{n+1}.
\tag{4}
\]

Then \(1<\sigma_n\le b\le s_i\) and \(\sigma_n\to1\).  Put

\[
u_{n,i}
=\frac{s_i-\sigma_n}{\sigma_n-1}.
\tag{5}
\]

It is nonnegative, and the exact affine identity already proved in the
finite-packet chart gives `(2)`.

Write \(Z_{\rm sq}(\sigma)\) for `squarefreeMobiusTotal sigma`.  For each
coordinate define its exact Gamma graph scale

\[
\gamma_{n,i}
=(\sigma_n-1)\frac{Z_{\rm sq}(s_i)}{Z_{\rm sq}(\sigma_n)}.
\tag{6}
\]

Every \(\gamma_{n,i}\) is positive.  For fixed \(i\),
\(\gamma_{n,i}\to0\), because \(\sigma_n-1\to0\) and
\(Z_{\rm sq}(\sigma_n)^{-1}\to0\) as \(\sigma_n\to1^+\).

At stage \(n\), let

\[
\varepsilon_n=\min_{0\le i\le n}\gamma_{n,i}.
\tag{7}
\]

The set is nonempty and finite, so \(\varepsilon_n>0\).  Moreover
\(0<\varepsilon_n\le\gamma_{n,0}\), hence
\(\varepsilon_n\to0\).

Apply the countable-packet singular codiagonal theorem to

\[
\begin{aligned}
f_{n,i}&=
  \operatorname{infiniteMobiusCriticalFisherTangentLp}(\sigma_n),\\
d_{n,i}&=
  \operatorname{infiniteMobiusCriticalDampedSignedWeightLp}
    (\sigma_n,u_{n,i})
\end{aligned}
\]

at the common scale \(\varepsilon_n\).  It constructs one strictly increasing
depth \(N(n)\) such that, for every fixed \(i\), both vector legs and their
Sonin codiagonal are transported with error \(o(\varepsilon_n)\).

For fixed \(i\), eventually \(i\le n\).  Equation `(7)` then gives
\(\varepsilon_n\le\gamma_{n,i}\), so the same codiagonal error is
\(o(\gamma_{n,i})\).  Dividing by `(6)` is therefore legitimate at the exact
pointwise graph grade.

Finally, the algebra in the fixed-Euler incidence theorem applies
coordinatewise.  The transported-minus-source Gamma--Xi current is
\(i/2\) times this normalized codiagonal error, while the untransported
current equals the continued Xi source trace exactly by `(2)`.  The first
term tends to zero, proving `(3)` for every \(i\).  The depth schedule is the
same for all coordinates.  `QED`

## Analytic determining family

For example,

\[
s_i=2+\frac1{i+1}
\tag{8}
\]

satisfies \(s_i\ge2>1\) and has accumulation point \(2\) inside the Euler
half-plane.  Hence equality of two holomorphic Euler-side scalar germs on
this family implies equality on their connected common domain.

This is why countable reconstruction is stronger than a sequence of
finite-packet results: one schedule now carries a scalar analytic determining
family.

## Hostile audit

1. The theorem is scalar.  Countably many transported codiagonals do not by
   themselves define an adjointable vector-valued Rees--Hardy operator.
2. The schedule may depend on the enumerated determining family.  The
   singular-grade corona identifies schedules recovering the same reference,
   but full bornological determining-family independence remains open.
3. No Hardy norm or four-unit contraction is proved.  Equation `(3)` is
   incidence, not energy transport.
4. The uniform lower bound \(s_i\ge b>1\) is used only to keep every
   tangential speed nonnegative on one common normal path.  It does not
   weaken analytic determination because `(8)` supplies such a family.
5. Applying the identity theorem requires holomorphy of the two scalar germs
   on a common connected domain.  It does not manufacture the missing
   pre-scalarized morphism.
6. No zero, divisor coordinate, zero-adapted metric, or RH premise enters the
   construction.

## Novelty boundary

Countable diagonal selection, finite minima, and holomorphic identity
theorems are parent mathematics.  The source-specific specialization to the
actual Möbius Fisher two-jet and exact Gamma graph scale is a required bridge,
not a novelty claim.

## Gates

- [x] countable statement source-typed
- [x] complete paper proof
- [x] analytic determining family exhibited
- [x] passive scalar/energy distinction recorded
- [x] Lean theorem
- [x] targeted module build and axiom audit
- [ ] lift scalar determining-family chart to a source-global polarized
      Rees--Hardy morphism

## Log

- 2026-07-30 — Extracted the source-specific countable specialization from
  the generic countable Sonin codiagonal theorem and the finite Möbius--
  Gamma--Xi incidence algebra.
- 2026-07-30 — Formalized as
  `exists_countableEulerFamily_soninGammaXiReesChart` in
  `SoninCountableMobiusGammaXiIncidence.lean`; direct Lean check passed.
