# Uniform complex Cauchy contraction fails

- **Stage:** 5-failed
- **Type:** NO-GO WITH FORMALIZED POSITIVE SURVIVORS
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.
- **Lean:** `RenormalizedIntersectionTheory/GaussMayerCauchyBoundaryAmplification.lean`, namespace `MayerCauchyBoundaryAmplification`.

## Failed candidate

The bound `|M K_w(w/2)|≤1` does not hold throughout `0<Re w<1`.
For every real `τ≠0` and every `ε>0`, there is `0<σ<min(1,ε)` such that

```text
|M K_(σ+iτ)((σ+iτ)/2)| > 1.
```

This is the actual Cauchy kernel and an absolutely convergent Mellin
integral, not an assigned value outside the convergence strip.

## Exact positive survivors

The [strict real-parameter bound](../3-formalized/gauss-mayer-real-cauchy-contraction.md)
remains valid, with its exact positive squared-energy deficit. Both its
paper proof and Lean formalization are complete.

Gamma reflection also gives the exact boundary law, for all real `α,τ`:

```text
|m(iτ, α+iτ/2)|² = cosh(πτ/2)
                  / (cos(πα/2)²+sinh(πτ/4)²),
```

where `m` is the [certified Gamma multiplier](../3-formalized/gauss-mayer-cauchy-mellin-symbol.md).
For `τ≠0`, every real Mellin weight amplifies. This boundary law and its
interior continuation are fully formalized.

## Proof

Set `z=(α+1)/2+iτ/4`. The numerator Gamma arguments are `z` and
`1−conj(z)`. Conjugation and reflection turn their squared norm into
`π²/|sin(πz)|²`, where the sine norm is
`cos(πα/2)²+sinh(πτ/4)²`. The denominator follows from
`|Γ(1/2+iy)|² cosh(πy)=π`.

When `τ≠0`, the numerator of the boundary quotient is
`1+2 sinh(πτ/4)²`; its denominator is at most `1+sinh(πτ/4)²`.
Thus the modulus exceeds one. The central quotient
`Γ((w+2)/4)²/(√π Γ((w+1)/2))` is holomorphic for `Re w>−1`.
Continuity moves central boundary amplification into arbitrarily small
positive real parts. The actual Mellin formula supplies absolute
convergence and identifies those values with the actual integral.

## Lean certificate

`symbol_boundary_norm_sq`, `symbol_boundary_norm_gt_one`, `symbol_half`,
`differentiableAt_central`, `exists_source_central_amplification`, and
`not_source_central_contractivity` passed the direct production check.
All six have only `propext`, `Classical.choice`, and `Quot.sound` as
transitive axioms.

## Scope

The [sharp high-frequency law](../3-formalized/gauss-mayer-cauchy-high-frequency.md)
now gives limiting modulus `2^((1−σ)/2)` for every fixed `σ>0` and
admissible real Mellin weight. Thus every fixed `0<σ<1`, including the
right half of the critical strip, eventually amplifies at half the
spectral frequency. That exact threshold and its full Lean certificate
strengthen the positive survivor. The
[global central envelope](../3-formalized/gauss-mayer-normalized-cauchy-schur.md)
is strictly `2^((1−Re w)/2)` and sharp on every positive abscissa;
its paper proof and Lean formalization are complete. The
[sharp actual operator norm](../3-formalized/gauss-mayer-cauchy-sharp-operator.md)
now equals the central modulus: for every `0<σ<1` and all large heights,
there are actual logarithmic `L²` fields whose norm increases under Cauchy
averaging. Strict contraction at every height holds exactly for
`σ≥1`; a common strict gap exists exactly for `σ>1`. These statements
have complete paper proofs and seven audited Lean declarations. Other Mayer Hermitian or Krein forms remain open.
