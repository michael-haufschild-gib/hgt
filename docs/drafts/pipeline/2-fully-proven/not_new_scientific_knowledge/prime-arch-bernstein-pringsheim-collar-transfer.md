# Prime--archimedean Bernstein Pringsheim collar transfer

- **ID:** `prime-arch-bernstein-pringsheim-collar-transfer`
- **Stage:** 2-fully-proven
- **Type:** top-down RH bridge / analytic-continuation criterion
- **Status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean status:** paper theorem; the exact radius theorem is formalized, while the general
  Vivanti--Pringsheim step is not present in the Lean corpus

## Setup

Let

\[
 \Pi_n=\texttt{primeArchEndpointBernsteinPurity}(n)\ge0,
 \qquad
 \chi(z)=\sum_{n\ge0}\Pi_nz^n.                           \tag{1}
\]

The live Lean corpus proves that there is a unique exact real Abel radius `R_A` satisfying

\[
 r_0:=\frac{250000}{251001}<R_A\le1,
 \qquad
 \mathrm{RH}\iff R_A=1.                                 \tag{2}
\]

The same `R_A` is the complex power-series radius of `(1)`.  Indeed, for `|z|<R_A`, choose a real
`t` with `|z|<t<R_A`; summability of `sum Pi_n t^n` gives absolute convergence at `z`.  For every
real `t>R_A`, the defining critical-radius theorem gives divergence, so the complex radius cannot
exceed `R_A`.

## Collar hypothesis

Assume that there are a connected open set `U subset C` and a holomorphic function `F : U -> C`
such that

\[
 [r_0,1)\subset U                                      \tag{3}
\]

and `F` agrees with the germ `(1)` on a nonempty open set immediately to the left of `r_0`.  More
intrinsically, `F` is one coherent holomorphic continuation of the germ `(1)` through the entire
positive real collar `[r_0,1)`.

Then

\[
 \boxed{\text{collar hypothesis}\Longrightarrow\mathrm{RH}.}    \tag{4}
\]

The endpoint `1` itself is deliberately excluded.  No convergence or regularity at `t=1` is
required.

## Proof

Suppose RH is false.  Equation `(2)` then gives

\[
 r_0<R_A<1.                                               \tag{5}
\]

Because all Taylor coefficients `Pi_n` are nonnegative and the radius is finite and positive, the
Vivanti--Pringsheim theorem says that the positive boundary point `z=R_A` is a singular point of
the analytic germ `(1)`: the germ has no holomorphic continuation to a neighborhood of `R_A`.

But `(3)` puts `R_A` in `U`.  The agreement to the left of `r_0`, connectedness of `U`, and the
identity theorem continue the same germ along the real segment to the holomorphic germ of `F` at
`R_A`.  This is the forbidden continuation.  Hence `(5)` is impossible, `R_A=1`, and `(2)` gives
RH.

## Concrete source form

The companion paper theorem

`prime-arch-bernstein-legendre-double-source-kernel.md`

proves the unconditional value relation

\[
 \chi(t)=(L_R\otimes L_R)
 \frac1{\sqrt{1-2t(1-x-y+2xy)+t^2(1-x-y)^2}},            \tag{6}
\]

where `L_R` is the endpoint-normalized prime--Gamma moment functional.  Therefore a concrete
predecessor of RH is:

```text
the independently evaluated prime--Gamma double kernel in (6)
is holomorphic on one connected neighborhood of [r0,1)
  -> no positive Pringsheim singularity occurs before 1
  -> R_A = 1
  -> RH.
```

For a normalized reciprocal-square atom `u`, the conjugate-reflected denominator factors as

\[
 (1-(|u|+|1-u|)^2t)(1-(|u|-|1-u|)^2t).                  \tag{7}
\]

Thus the missing source theorem is exactly exclusion of a reflected algebraic pinch in the thin
collar, not a separate estimate for every `Pi_n`.

## Circularity firewall

The abstract collar hypothesis is equivalent in strength to RH if `F` is allowed to be defined by
the susceptibility series itself.  That use is forbidden.  An admissible provider must construct
`F` from an independent expression involving the continued prime--Gamma trace, the exact theta
source, or a source-side contour/integral formula, and prove its collar holomorphy before invoking
Pringsheim.

In particular, the provider may not use:

- Xi zero locations or real-rootedness;
- the attained amplitude `B` selected under false RH;
- the exact Abel radius or an RH-equivalent coefficient bound;
- a positive representing measure whose existence is already equivalent to RH;
- analytic continuation defined only by the coefficients `Pi_n`.

## Relation to the current competing route

This route is analytically orthogonal to sublinear finite-coefficient or anisotropic-mesh flux
estimates.  It asks for source holomorphy of one algebraic double-kernel value, not a growth bound
for the coefficient sequence or the Li-type quantities currently being studied elsewhere.

## Formalization target

1. Define the complex susceptibility germ on the unconditional disk.
2. Prove that `PrimeArchEndpointBernsteinAbelCriticalRadius R_A` is its complex radius.
3. Add a reusable Vivanti--Pringsheim theorem for nonnegative real coefficients.
4. Define the coherent collar-continuation predicate using the existing `ContinuesAcross` pattern
   from `U0/U0NaturalBoundary.lean`.
5. Prove `(4)` and splice it to the Legendre double-source kernel.
6. Do not formalize until targeted Lean verification is again permitted.

## Literature calibration

Vivanti--Pringsheim states that a power series with nonnegative real coefficients and finite
positive radius `R` is singular at the positive real point `R`; see Flajolet--Sedgewick,
[Analytic Combinatorics, Chapter IV](https://algo.inria.fr/flajolet/Publications/AnaCombi/anacombi.html),
or Melczer, Proposition 2.4 in
[An Invitation to Analytic Combinatorics](https://melczer.ca/files/Melczer-SubmittedManuscript.pdf).
The theorem is classical.  The project contribution is the exact splice from the formal
prime--Gamma susceptibility radius to the source-specific algebraic kernel `(6)`.

## Gates

- [x] complex radius identified from the formal real critical-radius interface
- [x] Pringsheim collar implication proved on paper
- [x] endpoint `t=1` removed from the hypothesis
- [x] concrete double-source provider interface identified
- [x] circularity firewall stated
- [ ] general Pringsheim theorem formalized in Lean
- [ ] independent prime--Gamma collar continuation
- [ ] RH
