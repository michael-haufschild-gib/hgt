# Route U horizontal nodal jet and curvature law

## Status

- Paper proof: complete.
- Lean formalization: complete in
  `RHTower.XiShiftedHorizontalNodalJetCurvature`.
- RH: not proved. Exact remaining obstruction is sign of the horizontal curvature on nodal amplitudes.

## Problem

For a real polynomial `P` of degree `d`, put `a = 2d+1` and let

\[
  E_{y,P}(u)=\sum_q \Re\!\left(
    \frac{z_q(y)P(z_q(y))^2}{(1+u z_q(y))^{a}}
  \right),
  \qquad z_q(y)=\frac1{y+\lambda_q}.
\]

This is the existing shifted-Xi Padé normal energy. Existing denominator-cleared Möbius
transport identifies it with the moment norm of the co-moving degree-`d` polynomial

\[
  T_uP(X)=(1-uX)^d P\!\left(\frac{X}{1-uX}\right)
\]

at mass `y+u`. For a nodal factor `1-cX`, this transport is `1-(u+c)X`. Thus roots are not
independent moving coefficients: they are pullbacks of fixed spectral annihilators.

## Theorem U-HNJ

For every real `w`, every real polynomial `P`, every `j >= 0`, and `y=e^w`,

\[
  E_{y,P}^{(j)}(0)
  =(-1)^j (2d+1)^{\overline j}
    L_y\!\left(P^2X^j\right),
\]

where `x^{overline j}` is the ascending factorial. In particular, if

\[
  M_j=L_y(P^2X^j),
\]

then

\[
  E(0)=M_0,\qquad E'(0)=-aM_1,\qquad E''(0)=a(a+1)M_2.
\]

### Proof

The existing analytic Padé contact germ has coefficient

\[
  [u^j]E_{y,P}(u)=(-1)^j\binom{2d+j}{j}L_y(P^2X^j).
\]

For an analytic scalar germ, the diagonal `j`th iterated derivative at zero is `j!` times this
coefficient. The exact natural-number identity

\[
  j!\binom{2d+j}{j}=(2d+1)^{\overline j}
\]

gives the formula. No zero-location, positivity, numerical, or RH assumption enters.

## Theorem U-HC

Define the horizontal curvature

\[
  \mathcal C_{y,P}
  =aE(0)E''(0)-(a+1)E'(0)^2.
\]

Then

\[
  \boxed{\mathcal C_{y,P}
  =a^2(a+1)\bigl(M_0M_2-M_1^2\bigr).}
\]

### Proof

Substitute the three jets from U-HNJ and factor `a^2(a+1)`.

At the fixed unconditional base `y=e`, set `W=sqrt(e)`. Since `W>1/2` and `W^2=e`, the existing
arithmetic landing identity gives

\[
  \boxed{\mathcal C_{e,P}
  =a^2(a+1)\,
    \mathcal A_{W,P},}
\]

where `A_{W,P}` is the literal rational--Gamma-minus-von-Mangoldt adaptive completed landing.
This is an equality to the actual Route U source, not a model or conditional reporter.

## Universal reinterpretation

The admission connection was a gauge artifact of freezing polynomial coefficients while shifting
the spectral atoms. In the horizontal Möbius gauge, polynomial nodes and atoms move together, the
full connection is absorbed into the odd exponent `2d+1`, and the nodal Turán minor becomes a
normalized curvature of one scalar Xi energy germ.

Equivalently, wherever `E>0`, nonnegativity of the Turán minor is concavity of
`E^(-1/(2d+1))`. The formal theorem uses the denominator-free curvature numerator, so it requires
no positivity premise.

## Hostile audit

1. This does **not** sign the curvature. For the full nodal family, that sign is still equivalent
   to RH by the existing single-minor criterion.
2. It does eliminate the previous source-plus-admission-connection split exactly.
3. It supplies an all-order, connection-free Xi jet hierarchy, not only a first-derivative wrapper.
4. Existing corpus contains denominator-cleared transport and the Padé germ, but not this
   all-order horizontal jet law, curvature factorization, or completed-arithmetic curvature
   identity.
5. Classical Christoffel/Geronimus and Toda literature covers measure transformations and moment
   flows, but the checked primary sources do not state this shifted-Xi odd-cocycle jet/curvature
   identity. Novelty is claimed relative to the corpus and that targeted audit, not as a priority
   claim over all literature.

## No-theatre consequence

The live hard problem is now one scalar statement with no connection bookkeeping:

\[
  \mathcal C_{e,\,X^m\prod_{r\in R}(X-r)}\ge 0
\]

for every finite `R subset (0,1]` and every `m`. Any future producer must sign this literal
rational--Gamma-minus-von-Mangoldt curvature, or pivot. Generic capacity, spread, and frozen-frame
energy cannot receive credit for it.
