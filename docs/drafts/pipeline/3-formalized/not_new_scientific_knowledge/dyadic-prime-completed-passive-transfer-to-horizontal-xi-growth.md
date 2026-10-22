# Dyadic-prime completed passive transfer to horizontal Xi growth

- **ID:** `dyadic-prime-completed-passive-transfer-to-horizontal-xi-growth`
- **Stage:** `3-formalized`
- **Type:** `[BRIDGE] [ROUTE COLLISION] [EXACT CLASSIFICATION]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Source route:** Route I, sharp dyadic prime window
- **Collision target:** retired Route C2, published horizontal Xi growth / theta-kernel positivity
- **Formalized companion:** `dyadic-prime-completed-passive-transfer-to-horizontal-xi-growth-formalized.md`
- **Lean target:**
  `GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowCompletedPassiveTransfer`

## Theorem

Write

```text
t = s - 1/2,
M(s) = sharpPrimeWindowMellin(log 2,s),
E(s) = dyadicSharpPrimeWindowErrorSeries(s),
F(s) = dyadicSharpPrimeContinuedSource(s).
```

On `Re(s)>3/2`, the literal sharp-window identity is

```text
F(s) = 2 M(3/2) zeta(t) + 2 M(s) zeta'(t)/zeta(t) - 2 E(s).       (1)
```

The factor `M(s)` is nonzero already on `Re(s)>1`.  Therefore the source-normalized core

```text
Q(s) = [F(s) - 2 M(3/2) zeta(t) + 2 E(s)] / [2 M(s)]             (2)
```

satisfies exactly

```text
Q(s) = zeta'(t)/zeta(t).                                         (3)
```

In the impedance coordinate `s=1-i z`, so `t=1/2-i z`, define the completed response

```text
P_source(z) = i [Q(1-i z) + 1/t + 1/(t-1) + Gamma_R'(t)/Gamma_R(t)].  (4)
```

The completed-zeta product and affine chain rule give, without a scale or sign ambiguity,

```text
P_source(z) = i xi'(1/2-i z)/xi(1/2-i z)
            = (XiC'/XiC)(-z)                                    (5)
```

throughout the source overlap `Im(z)>1/2`.

Since `XiC` is even, its logarithmic derivative is odd.  Hence the global completed response

```text
P(z) = (XiC'/XiC)(-z) = -(XiC'/XiC)(z)                            (6)
```

has nonnegative imaginary part on the upper half-plane exactly when the classical anti-Herglotz
sign of `XiC'/XiC` holds there.  This is equivalent to RH.  More sharply, under a closed horizontal
Xi-divisor bound `alpha`, `Im P(z)>0` whenever `Im(z)>alpha`.

## Proof

Equation (3) follows from (1) by cancellation and division by `2M(s)`; noncensorship follows from
the exact zero classification of the positive-width rectangular Mellin amplitude.  The logarithmic
derivative identity

```text
xi'/xi(t) = 1/t + 1/(t-1) + Gamma_R'/Gamma_R(t) + zeta'/zeta(t)
```

then proves (5), including the factor `i` forced by `XiC(w)=xi(1/2+i w)`.  Oddness proves (6).
Sondow--Dumitrescu horizontal modulus monotonicity supplies the strict sign beyond every closed
zero-width bound; the converse follows from the existing logarithmic-derivative pole criterion.

## Exhaustion of the transformed-response survivor

The raw response and every nondegenerate real boundary-preserving Möbius postcomposition are
excluded separately: their imaginary parts still take both signs above every height.  The exact
noncensored source normalization (2), followed by archimedean completion, does survive—but (5)
identifies it with the already-existing Route-C2 horizontal Xi response.

An arbitrary dissipative bias such as `iB+F` is not a positive research survivor.  Its far-right
sign can be forced for any absolutely convergent Dirichlet series, while a global holomorphic
extension lets one subtract `iB` and recovers the original RH-equivalent analytic-continuation
problem.  It adds neither a source-forced energy law nor an independent inverse theorem.  Counting
that tautological relabeling as a route would violate the project's anti-theatre rule.

Thus the canonical completed candidate is not a new Route-I mechanism: it collides exactly with
Route C2, where Sondow--Dumitrescu own horizontal Xi-modulus monotonicity and Planat's June 2026
paper owns the theta-kernel positivity representation and critical-strip localization.  Route C2
is already retired as a saturated RH-equivalent divisor detector, so it cannot receive this
survivor.  The equality exhausts the completed-response branch while leaving Route I's arithmetic
source endpoint open.

## Novelty audit

- Sondow--Dumitrescu, *A monotonicity property of Riemann's xi function and a reformulation of the
  Riemann Hypothesis* (2010), own strict horizontal Xi-modulus monotonicity in zero-free
  half-planes.
- Planat, *A Theta-Kernel Reformulation of a Growth Theorem and the Riemann Hypothesis* (posted
  1 June 2026), owns the theta-kernel representation, unconditional exterior positivity, and
  localization of the unresolved obstruction to the critical strip.
- Equations (2)--(5) are exact project-level route bookkeeping and source transport.  They are
  useful, formalized, and not claimed as publication-level new science.

## Gates

- [x] raw impedance no-go retained
- [x] all nondegenerate real Möbius postcompositions excluded
- [x] exact noncensored source normalization proved
- [x] archimedean completion and impedance rotation proved
- [x] completed response identified with literal centered-Xi logarithmic derivative
- [x] completed passivity proved equivalent to RH
- [x] strict horizontal bound transfer proved
- [x] exact collision with retired Route C2 identified; no live handoff claimed
- [x] tautological biased analytic lift rejected by anti-theatre audit
- [x] exact unconditional Lean formalization
- [x] direct source check and focused final leaf build
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`

## Lean closure

`dyadicSharpPrimeZetaLogDerivCore_eq` proves literal recovery of the shifted zeta logarithmic
derivative on the source overlap.  `dyadicSharpPrimeCompletedSourceNormalization_eq_passiveResponse`
then proves the exact completed coordinate equality, while
`dyadicSharpPrimeCompletedPassiveResponseNonnegative_iff_riemannHypothesis` and
`dyadicSharpPrimeCompletedPassiveResponse_im_pos_of_halfPlaneBound` prove the two terminal
passivity statements.  The companion certificate also records the fully formal Möbius closure.
