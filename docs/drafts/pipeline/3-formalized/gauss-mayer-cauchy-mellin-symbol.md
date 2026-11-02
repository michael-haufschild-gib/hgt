# Mellin symbol of the actual Cauchy transform

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.
- **Input:** [continued Epstein transform](gauss-mayer-epstein-continuation.md).
- **Lean:** `RenormalizedIntersectionTheory/GaussMayerCauchyMellinSymbol.lean`, namespace `MayerCauchyMellinSymbol`.

## Exact result

For the actual kernel `MayerQuadraticCone.cauchyKernel`, the Mellin integral
converges absolutely and equals

```text
M K_w(u) = Γ((u+1)/2) Γ((w+1−u)/2)
           / (√π Γ((w+1)/2)),
Re w>0,  −1<Re u<Re w+1.
```

The multiplier never vanishes in this strip and is invariant under
`u↦w−u`. Both moments `u=0,w` equal one throughout `Re w>0`.

For real `r>0` and every real frequency `ξ`,

```text
M K_r(r/2+iξ) = |Γ((r+2)/4+iξ/2)|²
               / (√π Γ((r+1)/2)) > 0.
```

## Proof

Set `x=t²` in the actual integral. The half-line beta parameters are
`(u+1)/2` and `(w+1−u)/2`, both with positive real part. The existing
proved beta integral has a nonzero Gamma value, which also certifies
Bochner integrability. The power substitution and Mellin shift preserve
absolute convergence. Cancellation against the actual Cauchy
normalization gives the quotient.

Gamma has no zeros or poles at these arguments, giving nonvanishing.
Reflection interchanges the numerator factors. At `u=0`, `Γ(1/2)=√π`
gives unit mass; reflection gives the other unit moment. On the real
central line the numerator arguments are conjugates. Gamma conjugation
and positivity on the positive real axis give the positive norm square.

## Lean certificate

- `cauchyKernel_hasMellin`: actual integral and absolute convergence.
- `symbol_reflection`, `symbol_ne_zero`: symmetry and nonvanishing.
- `cauchyKernel_mellin_zero`, `cauchyKernel_mellin_spectral`: full-half-plane unit moments.
- `symbol_central`, `centralSymbol_pos`, `cauchyKernel_central_hasMellin`: exact positive central multiplier.

Direct production check passed. All eight declarations have only
`propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

## Boundary

This is positivity of the actual Cauchy transform's Mellin multiplier.
A Hermitian form for the Mayer operator still requires an actual operator
relation and control of scattering boundary terms. No full spectral
classification, fixed zero-free strip, or RH conclusion follows here.
