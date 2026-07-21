# Completed prime--Gamma moving Hankel reflection

- **ID:** `completed-prime-gamma-moving-hankel-reflection`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[TOP-DOWN VALUE RELATION]`, `[REFLECTION]`
- **Scientific status:** `[PROVED] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaMovingHankelReflection.lean`
- **Parents:** `completed-prime-gamma-hankel-far-right-anchor.md`;
  `CompletedPrimeGammaMovingHankel.lean`
- **Statement:** The moving completed prime--Gamma moment germ reflects by `z -> -z` when its base
  reflects by `sigma -> 1-sigma`; every even moment, finite Hankel matrix, and determinant is
  therefore exactly invariant under base reflection.

## Theorem

Write

```text
T_sigma(z) = i (logDeriv(xi)(sigma + i z) - logDeriv(xi)(sigma)),
G_sigma    = normalizedTraceMomentGerm(T_sigma).
```

The completed functional equation gives the exact two-variable relations

```text
T_(1-sigma)(z) = -T_sigma(-z),
G_(1-sigma)(z) =  G_sigma(-z).
```

Lean then proves, for every jet order `k`,

```text
iteratedDeriv k G_(1-sigma) 0
  = (-1)^k * iteratedDeriv k G_sigma 0.
```

The moving Hankel family reads only the even jets.  Consequently, for every finite size `n`,

```text
completedMovingHankelMatrix n (1-sigma)
  = completedMovingHankelMatrix n sigma,

completedMovingHankelDet n (1-sigma)
  = completedMovingHankelDet n sigma.                         (1)
```

No zero location, determinant sign, moment representation, or RH hypothesis occurs.

## Top-down impact

The paper-proven far-right anchor supplies a positive endpoint for each fixed determinant.  Equation
`(1)` automatically supplies the matching far-left endpoint and halves the continuation problem:
only the real half-line from the far right to `1/2` needs independent control.  Any real determinant
zero or sign obstruction away from the center has its mirror at `1-sigma`.

This is a positive constraint theorem.  Reflection does not transport positivity through an
intervening zero; rather, it identifies precisely what a source-side continuation theorem must
exclude on one half-line.  The remaining live chain is

```text
positive far-right determinant anchor                         [paper]
  + source-side exclusion of determinant zeros on [1/2, +infinity) [open]
  + moving determinant reflection                             [Lean]
  -> positive central determinant for every finite size
  -> RH.                                                       [Lean]
```

## Formalization

- `completedMovingRelativeTrace_one_sub`
- `completedMovingMomentGerm_one_sub`
- `iteratedDeriv_completedMovingMomentGerm_one_sub`
- `analyticTraceMoments_completedMovingMomentGerm_one_sub`
- `completedMovingHankelMatrix_one_sub`
- `completedMovingHankelDet_one_sub`

The first three declarations now specialize the source-independent affine-folding results in
`HTGeometry/ReflectionFoldedMomentGerm.lean`.  Definition unfolding identifies
`completedMovingRelativeTrace` with `affineRelativeTrace (logDeriv xi)` and the moving normalized
germ with `reflectionFoldedMomentGerm (logDeriv xi)`; `logDeriv_xi_reciprocity` supplies the sole
anti-reflection premise.  The real even-moment and determinant consequences retain their existing
public statements.

## Gates

- [x] derive the translated trace anti-reflection from the completed functional equation
- [x] carry reflection through the normalized divided difference, including its center value
- [x] prove all-order jet parity
- [x] prove matrix and determinant invariance
- [x] import through the `RHTower` umbrella
- [x] refresh generated formal indexes
- [x] narrow-build and axiom-audit the capstone
