# Theta cusp fixed-action C5 exact first-atom tail reduction

- **ID:** TC-C5-EFATOM-RED
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE (paper + Lean 4)
- **Corpus source:** `ThetaCuspSingleAtomReflectedRiccatiContraction`,
  `ThetaCuspAtomLikelihoodCrossDomination`, and
  `ThetaCuspFixedActionC5HyperbolicGaussianTailCore`
- **Statement:** Exact reflected first-atom scale jets are closed, its C5 Bose weight inherits
  the Gaussian `30+72z` floor, and its fixed-action velocity centre transport is strictly
  negative in the structural tail chamber.

## Result

For

```
lambda(A) = 3A/(A-3/2)^2,
d(A)      = (2A d/dA)lambda(A) = -6A(A+3/2)/(A-3/2)^3,
z(t)      = cosh(2t)-1,
r(A,z)    = 1-lambda(A)z,
q(A,t)    = 2Az-log r(A,z),
```

Lean proves the literal scale derivatives of `lambda`, `q`, `q_t`, and `q_tt`. It also proves

```
-6 lambda(A) < d(A) < -2 lambda(A) < 0                 (A>3),
2 q(A,t) < t q_t(A,t)                                  (A>3, t>0, r>0),
30+72z < 14+10(t q_t)+8(t q_t)/(exp(q)-1),
```

and, when `A>=6`, `t>0`, and `r>1/2`,

```
H = q_t * (t q_tu) - (q_t+t q_tt) q_u < 0.
```

On the physical same-half-line `0<t<=u`, the corpus half-factor theorem supplies `r>1/2`, so
the last statement applies whenever `6 <= pi*exp(2u)`.

Finally, if

```
P = q_t*(t q_tu+t^2 q_ttu) - (q_t+3t q_tt+t^2 q_ttt) q_u,
B = 5P-(30+72z)H,
F = 5P-(14+10tq_t+8tq_t/(exp(q)-1))H,
```

then `B<F`. Therefore positivity of the remaining rational-hyperbolic base `B` implies exact
first-atom C5 compensation `F>0`.

## Proof `[PROVED HERE]`

Exact differentiation gives

```
q_u   = z(4A+d/r),
q_tu  = (4A+d/r^2) z_t,
q_ttu = 4(2 lambda d z(z+2)/r^3 + (4A+d/r^2)(z+1)).
```

The coefficient contraction follows by rational algebra. For centre transport, put

```
p=2A+lambda/r, g=lambda^2/r^2,
L=4A+d/r,       M=4A+d/r^2.
```

`A>=6` and `r>1/2` imply `L>0`; `d<0` and `0<r<1` imply `M<L`. Using
`z_t^2=4z(z+2)` gives the exact factorization

```
H = z * (4t p(z+2)M - p z_t L
          -4t(g z(z+2)+p(z+1))L).
```

Replace `M` by the larger `L`. The bracket becomes strictly smaller than

```
L * (p(4t-z_t) - 4t g z(z+2)),
```

which is negative because `z_t=2sinh(2t)>4t`. Thus `H<0`. The exact action is positive and
superquadratic, so the universal Bose tangent yields its weight floor; multiplication by
negative `H` then proves `B<F`.

## RH passport

This package closes the exact first atom's mixed scale jets, Bose-weight comparison, and velocity
transport orientation:

exact first-atom base-margin sign
→ exact first-atom compensation via this reduction
→ likelihood-interference perturbation bound
→ literal theta far-tail compensation
→ local-bivariate and compact-middle assembly
→ global direct-J orientation
→ modular-seam/Ptolemy packet wall
→ cofinal no-escape
→ CLG/TTF or Weil polarization nonnegativity
→ `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` or
  `riemannHypothesis_iff_xiWeilPolarization_nonneg`
→ RH.

This package does **not** prove the rational-hyperbolic base-margin sign or the likelihood lift.

## Novelty and audit

- Corpus previously contained displacement jets and the same-half-line half-factor law, but no
  mixed centre-scale jets, coefficient contraction law, exact Bose-floor inheritance, or
  fixed-action centre-transport sign for the reflected atom.
- Hostile exact-expression searches through 2026-08-29 returned no matching external theorem;
  results concerned unrelated fixed-action mechanics or Riccati control.
- Lean module:
  `RHTower.ThetaCuspFixedActionC5ExactFirstAtomTailReduction`.
- Direct Lean and targeted module build pass. Axiom audit: `propext`, `Classical.choice`,
  `Quot.sound` only; no added axioms.

## Log

- 2026-08-29 — corpus-derived scale contraction and transport factorization proved on paper and
  in Lean; umbrella wiring, targeted build, axiom audit, and hostile novelty search completed.
