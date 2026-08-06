# Deninger failure-nerve singular Cartier metric

- **Stage:** 3-formalized

- **ID:** `deninger-failure-nerve-singular-cartier-metric`
- **Route:** L / filtered prime-winning failure nerve
- **Status:** fully proved on paper; RH not proved
- **Inputs:** prime-winning face transition and finite coboundary;
  horizontal--vertical antipode weld; Xi normal-cone limit

## Result

Fix exponent depth `m >= 1`.  For a prime `p`, write the normalized actual
face transition as

\[
 \widehat R_{p,m}(s)
 =p^{-m(s-1/2)}Q_{p,m}(s),
 \qquad
 Q_{p,m}(s)=\frac{G_{p,m}(s)}{\sqrt{G_{p,m}(1)}},
\tag{1}
\]

where

\[
 G_{p,m}(s)=\frac{1-p^{-s}}{1-p^{-(m+1)s}}.
\tag{2}
\]

For every finite face `F`, put

\[
 Q_{F,m}(s)=\prod_{p\in F}Q_{p,m}(s),
 \qquad
 h_{F,m}(s)=|Q_{F,m}(s)|^{-2}.
\tag{3}
\]

Then the following statements hold.

### 1. Exact metric purification

For `p` not in `F`,

\[
 h_{F\cup\{p\},m}(s)
 |\widehat R_{p,m}(s)|^2
 =h_{F,m}(s)\,|p^{-m(s-1/2)}|^2.
\tag{4}
\]

Thus the entire nonunitary Euler gauge is removed by a metric transported
from actual Cech vertices, while radial Deninger character remains.

This metric is forced.  If positive vertex weights `k_F` satisfy

\[
 k_\varnothing=1,
 \qquad
 k_{F\cup\{p\}}|\widehat R_{p,m}|^2
 =k_F|p^{-m(s-1/2)}|^2
\tag{5}
\]

on every face edge, then `k_F=h_{F,m}` for every finite `F`.

Consequently tensor-square source-inverse/analytic-dagger mate curvature in
this forced metric is exactly

\[
 |p^{-m(s-1/2)}|^{-2}-|p^{-m(s-1/2)}|^2
 =K_{p^m}(s).
\tag{6}
\]

The actual Gamma reporter comparison already proved in the companion theorem
is therefore not merely a scalar collision: it is radial associated grade of
the uniquely purified finite failure-nerve metric.

### 2. Cofinal metric anomaly

Let `P_x={p:p<=x}`.  Existing cofinal face theorem gives, for `Re(s)>1`,

\[
 \frac{Q_{P_x,m}(s)}{\sqrt{\log x}}
 \longrightarrow
 \frac{e^{\gamma/2}}{\sqrt{\zeta(m+1)}}
 \frac{\zeta((m+1)s)}{\zeta(s)}.
\tag{7}
\]

Therefore

\[
 \boxed{
 (\log x)h_{P_x,m}(s)
 \longrightarrow
 e^{-\gamma}\zeta(m+1)
 \left|\frac{\zeta(s)}{\zeta((m+1)s)}\right|^2.}
\tag{8}
\]

Let `C_m(s)` be the source-positive archimedean depth factor and

\[
 X_m(s)=\frac{\Xi(s)}{\Xi((m+1)s)}
       =\frac{\zeta(s)/\zeta((m+1)s)}{C_m(s)}.
\tag{9}
\]

After Gamma metric completion, `(8)` becomes

\[
 \boxed{
 |C_m(s)|^{-2}(\log x)h_{P_x,m}(s)
 \longrightarrow
 e^{-\gamma}\zeta(m+1)|X_m(s)|^2.}
\tag{10}
\]

At normal scale `s=u/(m+1)`, existing Xi normal-cone theorem gives

\[
 X_m\!\left(\frac{u}{m+1}\right)
 \longrightarrow\frac1{2\Xi(u)}.
\tag{11}
\]

Hence the forced cofinal metric has normal-cone limit

\[
 \boxed{
 h_{\mathrm{nc},m}(u)
 =\frac{e^{-\gamma}\zeta(m+1)}{4|\Xi(u)|^2}.}
\tag{12}
\]

It is not a bounded harmless gauge at Xi divisor.

### 3. Multiplicity-exact Cartier renormalization

If `rho` is a Xi zero of order `d` and

\[
 \Xi(u)=(u-\rho)^d g_\rho(u),
 \qquad g_\rho(\rho)\ne0,
\tag{13}
\]

then

\[
 h_{\mathrm{nc},m}(u)
 =\frac{e^{-\gamma}\zeta(m+1)}
        {4|u-\rho|^{2d}|g_\rho(u)|^2}
\tag{14}
\]

and

\[
 \boxed{
 |u-\rho|^{2d}h_{\mathrm{nc},m}(u)
 \longrightarrow
 \frac{e^{-\gamma}\zeta(m+1)}{4|g_\rho(\rho)|^2}>0.}
\tag{15}
\]

Thus unique finite source metric does have conservative Xi landing, but only
as singular Hermitian metric on Cartier line: pole order is exactly twice
analytic multiplicity, and top-conormal renormalization is finite and
strictly positive.  Any ordinary bounded Hilbert metric extension necessarily
forgets this landing or changes actual finite face metric.

## Proof

Since `Q_{F union {p},m}=Q_{F,m}Q_{p,m}`, equation `(3)` gives

\[
 h_{F\cup\{p\},m}=h_{F,m}|Q_{p,m}|^{-2}.
\]

Substitution of `(1)` proves `(4)`.  Conversely, cancel nonzero radial
character in `(5)` and use `(1)` to obtain

\[
 k_{F\cup\{p\}}=k_F|Q_{p,m}|^{-2}.
\]

Induction on face cardinality from `k_emptyset=1` proves uniqueness.  Relative
squared norm of each edge is therefore squared norm of radial character,
which proves `(6)`.

Take inverse squared absolute values in `(7)`.  Nonzero limit on `Re(s)>1`
permits inversion and yields `(8)`.  Identity `(9)` yields `(10)`, and
normal-cone limit `(11)` yields `(12)` away from Xi divisor.  Factorization
`(13)` inserted into `(12)` gives `(14)`.  Continuity and nonvanishing of
`g_rho` prove `(15)`.

No zero location, RH, or divisor-fitted face weight is assumed.

## Novelty and hostile audit

Not new:

- finite Cech coboundary formula for `Q`;
- Mertens/Euler cofinal limit `(7)`;
- Xi normal-cone limit `(11)`;
- general singular Hermitian metrics on divisor line bundles.

New comparison is forced chain

```text
actual finite prime-winning face gauge
  -> unique metric purifying raw face transport
  -> cofinal Mertens metric anomaly
  -> Gamma-completed |X_m|^2 metric
  -> multiplicity-exact singular Xi Cartier metric.
```

Corpus and targeted literature search found no prior theorem identifying
prime-winning Cech gauge metric with this Xi Cartier pole metric.  This is
noncollision evidence, not priority certificate.

The theorem does not prove antipode equals dagger.  It changes exact frontier:

1. ordinary bounded-metric Cartier landing is ruled out;
2. full mate comparison must act on singular Cartier metric `(12)`;
3. source Bianchi law must be proved after conormal renormalization `(15)`;
4. vanishing cannot be obtained by declaring singular metric regular.

## Formalization target

Lean should formalize unconditionally:

- finite face-gauge and purified metric laws;
- uniqueness of purified diagonal metric;
- equality of purified mate curvature with existing Deninger curvature;
- generic inverse-square limit transport;
- multiplicity-exact local Cartier renormalization.

Actual Mertens/Euler limit `(7)` remains separate analytic infrastructure and
must not be replaced by an assumption disguised as a definition.

- 2026-08-06 — Formalization re-verified on this toolchain: the named Lean module exists, is wired into `GaloisForLFunctions.RHTower`, builds, uses no `native_decide`, and every audited declaration depends only on `propext, Classical.choice, Quot.sound`.  Every gate this card states is closed; what the card lists as still open is its declared successor core, not this theorem.  Card moves to `3-formalized`.
