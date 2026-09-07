# CLG/TTF explicit compact odd compensation

- **Stage:** 3-formalized
- **Scope:** Unconditional positivity of the literal corrected odd determinant on `0≤x≤137/2000`, with an explicit mass-normalized margin.
- **Full chain:** Literal theta source → every signed center-mixed Hankel section nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.
- **Remaining:** After the [global-energy extension to `8/95`](clg-ttf-global-modular-energy-compensation.md), the fixed interval `(8/95,7/16)` before the [scale-seven positive final ray](clg-ttf-scale-seven-compensated-tail.md), then positivity at every order. Global rank-six positivity and RH remain open.

## Exact source coordinates

Let `M=completedThetaProfile>0`, `u=−Re(modularDrift)`, `a=modularGapAmplitude`, and `w=modularTransverseShear`. The corpus's compact tube gives

`0≤u≤1`, `17≤a≤20`, `0≤w≤1`

for every `x∈[0,137/2000]`. The exact source equations are

`u′=−3+u²/3+3a/4`, `a′=−2aw`,

`w′=2+a/2+2u²/9+2uw/3`, `M′=uM/6`.

Writing `Φ` for the complete theta source, define

`Q=u²/24+a/16−3/8`,

`P=5u³/144+7ua/96−5u/16−aw/8`.

Then `Φ=MQ` and `Φ′=MP`. At every order, `Φ⁽ⁿ⁾=M F_n`, where the polynomial recurrence is the Lie derivative along the displayed vector field plus multiplication by `u/6`. The reflected jet is exactly

`j_n=M² Σ_i binom(n,i)(−1)^(n−i)F_iF_(n−i)`.

Consequently the native odd determinant and its leading minor factor as `H=M⁶h(u,a,w)` and `Δ=M⁴d(u,a,w)`. Explicit source and reflected polynomials through order ten, followed by real ring identities, establish these equalities without a source truncation.

## Positive correction reserve

Set `G=3Φ²+2xΦΦ′` and

`g₀=3Q²−(137/1000)Q(aw/8+5u/16)`.

On the box, `Q≥11/16`, `aw/8+5u/16≤45/16`, and `P≥−(aw/8+5u/16)`. Since `0≤2x≤137/1000`, this gives

`G≥M²g₀`, `g₀≥1`, hence `G≥M²>0`.

For the second inequality, the factor `3Q−(137/1000)(aw/8+5u/16)` is at least `3/2`, so `g₀≥(11/16)(3/2)>1`.

## Exact determinant certificate

Put `t=(a−17)/3∈[0,1]`. The normalized determinant has the exact decomposition

`h(u,17+3t,w)+10⁹d(u,17+3t,w)g₀(u,17+3t,w)=B(u,t,w)+R(u,t,w)`.

Here `B` has degree at most three in each variable. The explicit expansion of `B−10¹⁴` in the tensor Bernstein basis has strictly positive rational coefficients. Every basis term is nonnegative on the unit cube, so `B≥10¹⁴`.

The remainder is an explicit sum of positive rational multiples of nonnegative monomials, or of those monomials times `max(0,1−u^it^jw^k)`. On the unit cube the maximum equals its second argument. Substitution and ring normalization verify the displayed identity; elementary order laws prove `R≥0`.

Thus the whole box satisfies `h+10⁹dg₀≥10¹⁴`. The inequalities use exact rational coefficients and kernel-checked symbolic identities; no numerical source evaluation supplies a proof premise.

## Literal determinant conclusion

The corpus proves `Δ>0` at every real center. Multiplying the normalized bound by `M⁶`, and using `G≥M²g₀`, gives

`H+10⁹ΔG≥10¹⁴M⁶`.

Since `G>0`, increasing the coefficient preserves this bound. Therefore, for every `C≥10⁹` and every `0≤x≤137/2000`,

`H_C(x)≥10¹⁴M(x)⁶>0`.

The canonical coefficient satisfies `10⁹<K_*<3·10⁹`, so its determinant is positive throughout the same explicit interval. The existing flux comparison then yields a positive corrected weighted odd determinant at every `a>0` and `0<r≤137/1000`. The flux still integrates to zero, preserving the literal mixed tenth moment.

This settles an explicit initial interval. The separate [scale-seven theorem](clg-ttf-scale-seven-compensated-tail.md) proves positivity for `x≥7/16`. The [global-energy comparison](clg-ttf-global-modular-energy-compensation.md) extends the initial interval to `8/95`. The gap `(8/95,7/16)` and the all-order cone remain open.

## Lean landing and verification

- `PolynomialODEOddCompactSourceJets` and the scalar/reflected modules give the exact all-order interface and finite jet realizations.
- `PolynomialODEOddCompactHeadExpansion`, `PolynomialODEOddCompactCrossMinors`, and the three `Product` modules prove the real determinant through separate factored products; `PolynomialODEOddCompactScalarExpansion` recombines them.
- `PolynomialODEOddCompactCubic`, the seven `Remainder` modules, and `PolynomialODEOddCompactDeterminant` prove the positive compact comparison.
- `ThetaCuspOddCompactSourceCoordinates`, `ThetaCuspOddCompactCorrectionReserve`, and `ThetaCuspOddCompactCompensation` realize the source and prove the literal interval conclusions.

All 29 new modules passed targeted `lake env lean` checks. Finished scratch sources were copied identically into their module paths, retaining only needed oleans. Every new module is wired exactly once into its theorem-area umbrella; no full or umbrella build was run. All 371 new public names have no outside declaration conflicts. Formal lint passes; the largest new file has 1426 lines.

Only five new capstones were audited for axioms: the abstract compact lower bound, the all-order actual source-jet bridge, the literal corrected determinant lower bound, canonical compact positivity, and corrected weighted compact positivity. Each reports only `propext`, `Classical.choice`, and `Quot.sound`. No axiom or numerical proof premise was added.
