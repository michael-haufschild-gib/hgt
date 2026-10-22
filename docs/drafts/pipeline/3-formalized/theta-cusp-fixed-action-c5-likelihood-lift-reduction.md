# Theta cusp fixed-action C5 likelihood lift reduction

- **ID:** TC-C5-LIKE-LIFT-REDUCTION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean module:**
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5LikelihoodLiftReduction`
- **Main theorems:** `c5CompletedVelocitySlopeLowerJetNumerator_lt`,
  `c5LikelihoodLowerJetSingleMasterReduction`,
  `two_mul_scale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree`,
  `six_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree`,
  `expTwelve_sub_one_mul_neg_reflectedJetTwo_lt_mixedJetOne`,
  `adaptiveMasterCurvature_lt_completedVelocitySlopeGain`,
  `thetaCuspReflectedActionC5FixedActionJacobian_pos_of_adaptiveReservedCompensation`

## Decisive conjecture and RH passport

The attacked conjecture is strict positivity of literal completed-theta fixed-action C5
compensation for

```text
0 < t < u,   6 <= pi*exp(2u).
```

Success closes the far-tail direct-J chamber, then feeds

```text
local/compact assembly
-> fixed-action seam
-> reflection-odd rank-four/Ptolemy wall
-> cofinal no-escape
-> CLG/TTF or Weil polarization positivity
-> riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg
   or riemannHypothesis_iff_xiWeilPolarization_nonneg
-> RH.
```

Failure kills first-atom perturbative lifting as a global far-tail method; required survivor is an
exact failure chamber or tax invariant for the cofinal chord-reserve route.

## Proven reduction

Write likelihood perturbation channels as

```text
q = reflected likelihood action,
a = first displacement jet,
b = second displacement jet,
c = third displacement jet,
s = centre-action jet,
m = first mixed centre jet,
n = second mixed centre jet.
```

The corpus already gave `a,b,c<0` and `s,m,n>0`. This module proves two stronger facts.

First, the complete third likelihood channel is strictly favorable in literal velocity-slope
transport. Its gain is

```text
t^2 * (completed first jet * n - c * completed centre-action jet) > 0.
```

Therefore every `c,n` likelihood term can be deleted while obtaining a strict lower bound for the
actual completed compensation margin.

Second, convex source geometry collapses all five remaining adverse likelihood quantities to one
positive master loss `y=-b`:

```text
0 < y,
-q < t^2*y,
-a <= t*y,
0 < s < t*y,
0 < m < y.
```

The new ingredients are a strict action/velocity secant law, a strict centre-action/mixed-jet law,
and the upper Hermite--Hadamard inequality applied to literal likelihood curvature. The reusable
upper integral theorem is formalized in
`GaloisForLFunctions.HTGeometry.ConvexIntegralTrapezoid`.

This changes the open far-tail problem from independent control of seven likelihood channels to
one scalar atom-versus-`y` domination. It is a strict proof-burden reduction; it does not claim the
completed tail sign.

Third, the likelihood support gap proves an adaptive strict curvature-cooling law on the full
physical half-line, with constant rate six as a corollary:

```text
2*A(x)*F₂(x) < -F₃(x),
x ↦ exp(A(x))*F₂(x) is strictly decreasing,
6*F₂(x) < -F₃(x),
x ↦ exp(6x)*F₂(x) is strictly decreasing.
```

Consequently reflected endpoints obey

```text
exp(12t)*F₂(u+t) < F₂(u-t),
(exp(12t)-1)*y < (exp(12t)+1)*m.
```

Thus favorable mixed-centre curvature `m` retains an explicit positive fraction of adverse master
loss `y`; it cannot degenerate independently. This is a structural support-gap consequence, not a
computed or optimized tail constant.

More decisively, summing adaptive cooling over both reflected endpoints proves

```text
Z = 2*A(u+t)*F₂(u+t) + 2*A(u-t)*F₂(u-t) < n,
6*y < n,
t²*a_completed*Z < P_full-P_lower.
```

After the C5 coefficient `5` is restored, literal compensation is therefore strictly larger than

```text
lower-jet compensation + 5*t²*a_completed*Z,
```

and in particular larger than `lower-jet compensation + 30*t²*a_completed*y`. Earlier reduction
discarded this full third channel; adaptive reserved compensation retains its guaranteed portion.

## Exact remaining core

Global positivity of `c5CompletedAdaptiveReservedCompensationMargin` is false: its denominator-
cleared fifth seam germ is strictly negative because `F₃+2AF₂<0`. The literal completed margin
instead has the exact decomposition

```text
completed margin = adaptive reserved margin + positive third-channel residual.
```

Thus the sharp direct endpoint is

```text
-residual < c5CompletedAdaptiveReservedCompensationMargin u t.
```

A distinct sufficient homotopy route remains live. Computation with higher-atom amplitude removed
selects the smaller source obligations

```text
M'''(lambda)>0,
M''(0)>=0,
M'(0)>=-M(0)/5.
```

First two make exact first-atom-to-full interpolation convex; third and formal first-atom
compensation then prove full tail positivity. These signs are conjectural and no computed value may
enter Lean. If their source algebra fails, retain the residual-aware direct endpoint or export the
sharp seam obstruction to cofinal chord reserve.

## Corpus and literature audit

Corpus research used the exact atom-plus-likelihood factorization, negative likelihood displacement
jets, positive likelihood centre jets, strict monotonicity of likelihood score and third source jet,
the likelihood support-gap third-cumulant inequality, and exact first-atom compensation. No existing
corpus theorem supplied the action--jet hierarchy, single-master reduction, adaptive cooling law,
exponential master-to-mixed coupling, or quantitative complete third-channel lift.

Primary-source searches through 2026-08-29 found classical Hermite--Hadamard inequalities but no
theta-cusp likelihood fixed-action C5 theorem, no seven-to-one likelihood-channel reduction, and no
corresponding RH proof route. Novelty claim is therefore internal/external-search supported, not a
claim of exhaustive bibliographic certainty.

## Lean audit

- Direct Lean passed for both new modules.
- `lake build GaloisForLFunctions.HTGeometry.ConvexIntegralTrapezoid` passed.
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5LikelihoodLiftReduction` passed.
- Axiom audit for main theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- Both modules are wired into their umbrellas; no umbrella or full build was run.
