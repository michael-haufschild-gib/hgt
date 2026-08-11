# Source-horizontal/Wold neutral-jet bridge

- **ID:** source-horizontal-wold-neutral-jet-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md`, Routes R and T
- **Statement:** Every ordered Route-T residual increment is the neutral jet of a coefficient-faithful, reflection-odd deformation built from the source Gamma Bockstein and adjacent-prime holonomy.

## Goal

Construct a literal pre-divisor bridge between the already-oriented horizontal source carrier and
Route T's vanishing residual primitive. Preserve ordinary-prime order, Xi divisor multiplicity,
and both line-conjugate orientations. Do not assert the missing cofinal exponential control.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, exact coefficient formulas identified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: direct Lean check and targeted module build green; axioms
      `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4 publication-ready

## Heavy conjecture loop

### C1 — global Stokes reflection supplies the missing simultaneous landing — FAILED

The all-cross-prime arithmetic completion retains actual witnesses and coefficients, but no corpus
map sends its horizontal packet to `GlobalPuiseuxWitt.globalWittForm`. The old oriented boundary is
zero on the dense arithmetic source span, and every continuous or closable extension remains zero.
The existing Stokes obstruction therefore remains a receiver, not a producer.

### C2 — central holonomy, Gamma boundary, Green fracture, and source Bockstein are independent — FAILED

They are positive-gauge presentations of the same one-dimensional horizontal grade. In particular,
the marked comparison theorem identifies the Bockstein with a nonzero weight times central
holonomy-minus-identity. Combining them cannot create annihilation.

### C3 — horizontal grade is Route-T spectral translation — SURVIVES AS EXACT BRIDGE

For an ordinary prime `p`, put

\[
 b_p(t)=d_p(p^{-t}-p^t),\qquad d_p=\frac p{(p+1)^2}.
\]

Then

\[
 b_p'(0)=-2d_p\log p.
\]

Define the positive gauge

\[
 g_p=\frac{(1-p^{-1})^3(p+1)^2}{2p^2}.
\]

The depth-one Wold coefficient satisfies the exact identity

\[
 c_p=\frac{(1-p^{-1})^3\log p}{p}=-g_p b_p'(0).
\]

Moreover `1/16 <= g_p <= 9/8`, so this is a boundedly invertible coefficient change, not the
compact smoothing already ruled out elsewhere.

For consecutive ordered primes `p_N,p_{N+1}`, put

\[
 m_N(t)=\frac{(p_{N+1}/p_N)^t-(p_{N+1}/p_N)^{-t}}2,
\]

and

\[
 F_N(t)=-g_{p_{N+1}}b_{p_{N+1}}(t)-m_N(t).
\]

Both terms are reflection odd, and

\[
 F_N'(0)=c_{p_{N+1}}-(\log p_{N+1}-\log p_N)=R_{N+1}-R_N.
\]

For a multiplicity-exact Xi zero copy `q`, the path `u ↦ F_N(u t(q))` retains the copy label and
has neutral jet `t(q)(R_{N+1}-R_N)`; line conjugation negates the entire path.

## Paper proof `[PROVED HERE]`

Let `d_p=p/(p+1)^2`. Since `d/dt p^t|_0=log p` and
`d/dt p^{-t}|_0=-log p`, direct differentiation gives
`b_p'(0)=-2d_p log p`. Multiplying by `-g_p` and cancelling `(p+1)^2` gives

\[
 -g_pb_p'(0)=\frac{(1-p^{-1})^3\log p}{p}=c_p.
\]

For every prime `p>=2`, `(1-p^{-1})^3` lies in `[1/8,1]`, while
`(p+1)^2/p^2` lies in `[1,9/4]`. Therefore
`g_p=(1-p^{-1})^3((p+1)^2/p^2)/2` lies in `[1/16,9/8]`. This proves
uniform positivity and bounded invertibility of the coefficient transport.

Write `r_N=p_{N+1}/p_N>0`. Direct differentiation of
`m_N(t)=(r_N^t-r_N^{-t})/2` gives

\[
 m_N'(0)=\log r_N=\log p_{N+1}-\log p_N.
\]

Hence `F_N'(0)=c_{p_{N+1}}-(log p_{N+1}-log p_N)`. The corpus identity
`R_{N+1}-R_N=c_{p_{N+1}}-(log p_{N+1}-log p_N)` proves the neutral-jet law.
Every constituent is odd in horizontal grade, so `F_N(-t)=-F_N(t)`. Composing with
`u ↦ u t(q)` multiplies the derivative by `t(q)`; the source reflection law
`t(Jq)=-t(q)` then proves literal path negation while leaving the `XiZeroCopy` multiplicity label
present. No limit exchange enters any step.

## Lean realization

`formal/GaloisForLFunctions/RHTower/SourceHorizontalWoldNeutralJetBridge.lean` proves:

- `sourceHorizontalWoldNeutralJetGauge_mul_bocksteinJet` — exact coefficient transport;
- `sourceHorizontalWoldNeutralJetGauge_bounds` — uniform `[1/16,9/8]` bounds;
- `hasDerivAt_sourceHorizontalWoldResidualIncrementDeformation_zero` — full residual-increment jet;
- `sourceZeroHorizontalWoldResidualIncrementDeformation_reflection` — copy-labelled path negation;
- `hasDerivAt_sourceZeroHorizontalWoldResidualIncrementDeformation_zero` — multiplicity-labelled
  Xi specialization.

## Hostile boundary

The exact finite jet theorem does not justify interchanging the cofinal limit in `N` with a
nonzero horizontal deformation or its derivative. Pointwise `R_N → 0` controls only the neutral
jet. Uniform exponential-type control of the full family `F_N(t)` on `|t|<1` is the new analytic
producer; this is the same upper-abscissa content isolated by Route T, now expressed on a literal
source-horizontal deformation.

## New knowledge

Route R's horizontal grade and Route T's prime-log generator are tangent and cotangent views of
one source action. The Wold coefficient is not merely asymptotic to that tangent: it is obtained by
a uniformly bounded positive primewise gauge. The adjacent log mesh is the neutral jet of the
relative holonomy between consecutive prime labels. Thus the complete Route-T residual increment,
including its previously unmatched mesh cocycle, is source-horizontal before divisor
specialization.

## Lean target

`formal/GaloisForLFunctions/RHTower/SourceHorizontalWoldNeutralJetBridge.lean`

## Log

- 2026-08-11 — C1 and C2 killed; C3 frozen and paper proof reduced to exact differentiation and rational bounds.
- 2026-08-11 — C3 paper proof closed and formalized. Direct `lake env lean` and targeted
  `lake build GaloisForLFunctions.RHTower.SourceHorizontalWoldNeutralJetBridge` pass; audited axioms
  are `[propext, Classical.choice, Quot.sound]`.
