# Theta cusp fixed-action C5 hyperbolic Gaussian tail core

- **ID:** TC-C5-HGTAIL
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean 4)
- **Corpus source:** `ThetaCuspSingleAtomReflectedRiccatiContraction`,
  `ThetaCuspReflectedLikelihoodInterferenceFactorization`,
  `ThetaCuspFixedActionC5JacobianCompensation`, `HyperbolicBounds`, and
  `LegStripSteepness`
- **Statement:** Pure hyperbolic Gaussian reflected action has strictly positive direct-C5
  fixed-action compensation for every physical scale `A > 3` and displacement `t > 0`.

## Result

For

```
q = 2 A (cosh(2t)-1),  a = 4 A sinh(2t),
b = 8 A cosh(2t),      c = 16 A sinh(2t),
s = 2q, m = 2a, n = 2b,
H = a*(t*m) - (a+t*b)*s,
P = a*(t*m+t^2*n) - (a+3*t*b+t^2*c)*s,
v = t*a,
W = 14+10v+8v/(exp(q)-1),
```

Lean proves unconditionally

```
0 < 5P-WH
```

whenever `A > 3` and `t > 0`. By the exact compensation law, this is the strict direct-J
orientation of the pure Gaussian part of the first reflected theta atom.

## Proof `[PROVED HERE]`

Put `z=cosh(2t)-1`, `S=sinh(2t)`, `D=S-2t`, and

```
K = z*S + 2*t*z*(2*z+1) - 4*t^2*S.
```

Direct algebra using `cosh^2-sinh^2=1` gives

```
H = -16*A^2*z*D,
P = -16*A^2*K,
5P-WH = 16*A^2*(W*z*D-5K).
```

Two global source-pure bounds then isolate an `A`-independent certificate. First, the sharp Bose
lower tangent

```
8+6q < 10q+8q/(exp(q)-1)        (q>0)
```

follows from two strict-monotonicity derivative arguments. Second,
`2(cosh(2t)-1) <= 2t sinh(2t)` gives the intrinsic ratio
`2tS/z >= 2`. Since `A>3`, also `q>6z`, hence `W>30+72z`.

The remaining exact identity is

```
(30+72z)zD-5K =
  sinh(x)*(72*cosh(x)^2-119*cosh(x)+47+5*x^2)
  - x*(82*cosh(x)^2-129*cosh(x)+47),   x=2t.
```

Its odd Taylor series has zero coefficients at orders `1,3,5`; every later coefficient is
strictly positive. For index `n>=3`, positivity reduces to

```
54*9^n-(160+82n)*4^n+20n^2+268n+194 > 0,
```

with the exponential part proved inductively. The order-seven coefficient is already positive,
so the whole certificate is strict for `x>0`.

## RH passport

This theorem closes exactly the pure Gaussian subcore of the far-tail chamber:

pure Gaussian first-atom compensation
→ control exact first-atom rational correction
→ likelihood-interference perturbation bound
→ literal theta far-tail compensation
→ local-bivariate plus compact-middle assembly
→ global direct-J orientation
→ fixed-action comparison with modular reflection centre
→ reflection-odd rank-four/Ptolemy wall
→ finite packets and cofinal no-escape
→ CLG/TTF or Weil polarization nonnegativity
→ `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` or
`riemannHypothesis_iff_xiWeilPolarization_nonneg`
→ RH.

This theorem does **not** yet control the rational correction
`-log(1-lambda(A)(cosh(2t)-1))`, the likelihood action, or the compact/local chambers.

## Novelty and audit

- Corpus had the exact atom--likelihood factorization and first-atom action jets, but no
  fixed-action C5 sign even for the pure hyperbolic Gaussian core.
- Exact-expression and concept searches through 2026-08-29 found no matching hyperbolic Gaussian
  fixed-action C5 compensation theorem. Nearby theta/cusp and second-level-concavity literature
  does not state this action-level Jacobian certificate.
- Lean module:
  `RHTower.ThetaCuspFixedActionC5HyperbolicGaussianTailCore`.
- Direct Lean and targeted module build pass. Axiom audit: `propext`, `Classical.choice`,
  `Quot.sound` only; no added axioms.

## Log

- 2026-08-29 — corpus-derived conjecture, hostile proof search, paper proof, Lean proof, umbrella
  wiring, targeted build, and axiom audit completed.
