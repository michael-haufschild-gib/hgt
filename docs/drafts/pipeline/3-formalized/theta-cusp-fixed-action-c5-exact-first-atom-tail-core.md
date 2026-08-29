# Theta cusp fixed-action C5 exact first-atom tail core

- **ID:** TC-C5-EFATOM-TAIL
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE (paper + Lean 4)
- **Corpus source:** `ThetaCuspSingleAtomReflectedRiccatiContraction`,
  `ThetaCuspAtomLikelihoodCrossDomination`,
  `ThetaCuspFixedActionC5HyperbolicGaussianTailCore`, and
  `ThetaCuspFixedActionC5ExactFirstAtomTailReduction`
- **Statement:** On the physical same-half-line far-tail chamber, the exact reflected first theta
  atom has strictly positive direct-C5 fixed-action compensation under centre-scale flow.

## Result

Put

```
A(u)      = pi*exp(2u),
z(t)      = cosh(2t)-1,
lambda(A) = 3A/(A-3/2)^2,
r(A,z)    = 1-lambda(A)z,
q(u,t)    = 2A(u)z(t)-log(r(A(u),z(t))).
```

For `0<t<=u` and `6<=A(u)`, Lean proves

```
0 < 5P-(14+10v+8v/(exp(q)-1))*H,
```

where `v=t*q_t` and

```
H = q_t*(t*q_tu) - (q_t+t*q_tt)*q_u,
P = q_t*(t*q_tu+t^2*q_ttu)
      - (q_t+3t*q_tt+t^2*q_ttt)*q_u.
```

The exported theorem is
`RHTower.c5SingleAtomCompensationMargin_pos_of_sameHalfLine`.

## Proof `[PROVED HERE]`

The same-half-line geometry first gives new physical envelopes

```
lambda(A)z < (A-3)^2/(2(A-3/2)^2),
(lambda(A)/r)z < (A-3)^2/(A^2-9/2),
lambda(A)/r < 6A/(A^2-9/2).
```

Exact algebra splits the rational base margin into the positive Gaussian base shape times a
highest-jet reserve plus a lower-order rational correction. The reserve is positive because its
four dimensionless loss terms have sum strictly below one under the physical envelopes.

For the lower-order correction, write `w=(lambda/r)z`. Cancellation reduces its sign to

```
57z > 10w(z+2).
```

The same-half-line envelope proves `(lambda/r)(z+2)<3`, so
`10w(z+2)<30z<57z`. The strict hyperbolic inequality `2sinh(2t)>4t` supplies the remaining
positive factor. Hence the rational base margin is positive. The reduction package proves that
this base margin is strictly smaller than the literal Bose-weight compensation margin, yielding
the theorem.

## RH passport

exact first-atom compensation
→ likelihood-interference perturbation bound from the corpus-exact additive action factorization
→ literal theta far-tail compensation
→ local-bivariate and compact-middle assembly
→ global direct-J orientation
→ fixed-action modular-seam comparison
→ reflection-odd rank-four/Ptolemy packet wall
→ cofinal no-escape
→ CLG/TTF or Weil polarization nonnegativity
→ `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` or
  `riemannHypothesis_iff_xiWeilPolarization_nonneg`
→ RH.

This theorem closes the exact first-atom far-tail chamber only. It does not cover `3<A<6`, lift
through likelihood interference or higher atoms, assemble local/compact chambers, or prove RH.

## Novelty and audit

- Corpus supplied the exact reflected action, half-factor geometry, and displacement jets, but no
  mixed-scale physical envelopes, exact compensation decomposition, highest-jet reserve, or
  positive lower-order cancellation.
- Hostile exact-expression searches through 2026-08-29 returned no matching external theorem;
  results concerned unrelated fixed-action mechanics, Riccati control, or string theory.
- Lean module: `RHTower.ThetaCuspFixedActionC5ExactFirstAtomTailCore`.
- Direct Lean and targeted module build pass. Axiom audit: `propext`, `Classical.choice`,
  `Quot.sound` only; no added axioms.
- Formal lint reports only pre-existing unrelated unreachable-module errors; this module is wired
  into `GaloisForLFunctions.RHTower`.

## Log

- 2026-08-29 — corpus-derived physical envelopes, exact base decomposition, reserve estimate, and
  rational-correction cancellation proved on paper and in Lean; umbrella wiring, targeted build,
  axiom audit, hostile novelty search, and lint audit completed.
