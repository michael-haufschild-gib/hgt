# Von Mangoldt translation-value constraint

- **ID:** `von-mangoldt-translation-value-constraint`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/VonMangoldtTranslationValueConstraint.lean`

## Statement

Let

\[
E(s)=\sum_{n\ge1}\frac{\Lambda(n)}{n^s}
\]

on its Euler half-plane.  For every $h\in\mathbb C$,

\[
E(h+x)=E(x)\quad\text{for all sufficiently large real }x
\quad\Longleftrightarrow\quad h=0.
\]

The same equivalence holds for the actual continued prime carrier `infinitePrimeFlux`.  In the
spectral coordinate used by the moving completed trace, the translation is $h=iz$; hence its
prime channel can vanish cofinally only for $z=0$.

## Proof

Write

\[
c_h(n)=\frac{\Lambda(n)}{n^h}.
\]

The identity $E(h+x)=E(x)$ is the equality of the L-series of $c_h$ and $c_0$ for all large
real $x$.  Both coefficient streams have finite absolute-convergence abscissa, so L-series
coefficient uniqueness gives $c_h(n)=c_0(n)$ for every $n\ne0$.

At $n=p^m$,

\[
c_h(p^m)=\log p\,\exp(-m\log(p)h).
\]

Consequently every Euler translation character annihilates the finite translation operator
$T_h-1$.  Ray-complete Euler translation faithfulness forces $T_h-1=0$.  Evaluating this
operator at its support point $h$ shows $h=0$.  The converse is immediate.

For `infinitePrimeFlux`, sufficiently large real translation places both arguments in
$\operatorname{Re}(s)>1$, where it is exactly the von Mangoldt L-series.

## Formal declarations

- `shiftedVonMangoldtCoeff_prime_pow_exp`;
- `VonMangoldtTranslationValueConstraint`;
- `vonMangoldtTranslationValueConstraint_iff`;
- `InfinitePrimeFluxTranslationValueConstraint`;
- `infinitePrimeFluxTranslationValueConstraint_iff`;
- `MovingVonMangoldtValueConstraint`;
- `movingVonMangoldtValueConstraint_iff`.

## Top-down consequence

The channel decomposition of the moving determinant now has a faithful arithmetic coordinate:

```text
cofinal equality of the moving all-prime value channel
  -> zero spectral displacement                                      [Lean]

far-right completed determinant positivity                           [paper]
  + source-selected orientation/winding constraint                   [open]
  -> central trace-Hankel positivity                                 [Lean]
  -> RH.                                                             [Lean]
```

The first implication discharges source-marking faithfulness.  It does not discharge the open
orientation/winding constraint: an injective value coordinate does not determine the sign of the
completed Hankel determinant along the path to the center.

## Gates

- [x] exact all-prime coefficient recovery
- [x] cofinal function-value formulation
- [x] actual `infinitePrimeFlux` formulation
- [x] moving spectral-coordinate formulation
- [x] no Xi divisor, RH premise, cutoff, or project axiom
- [x] imported by the RHTower umbrella
