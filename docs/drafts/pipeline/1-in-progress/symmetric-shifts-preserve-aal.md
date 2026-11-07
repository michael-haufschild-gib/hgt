# Symmetric shifts preserve the asymptotic abscissa law

- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Statement:** For `a≥0`, the high-height-to-all-height zero-bound law for
  `ξ(s+a)ξ(s−a)` is equivalent to AAL for `ζ`.

## Proof

For any complex function `F`, put `G(s)=F(s+a)F(s−a)`. A bound `Re ρ≤σ`
on all zeros of `G` is equivalent to the bound `Re ρ≤σ−a` on all zeros of
`F`: translate an `F`-zero right by `a` for one direction; split a product
zero into its two factors for the other. Real translation preserves
imaginary parts, so the same equivalence holds with any fixed height cutoff.
Consequently the implication from an eventual bound to a global bound is
unchanged by symmetric shifts.

For `F=ξ`, Hardy's unbounded critical-line zeros exclude eventual bounds
below `1/2`. Above `1/2`, the existing equivalence between eventual height
bounds and finite right tails identifies this implication with
`RHTower.AsymptoticAbscissaLaw`.

## Consequence

`SelfImprovementFailsOnShiftedProducts.lean` concerns `Θ<1 ⇒ Θ=1/2`.
Its shifted family is not an independent counterexample to AAL: it satisfies
AAL exactly when the original zero configuration does. This distinction
does not prove AAL for the original configuration.

## Verification

Lean formalization pending. No unconditional AAL decision claimed.
