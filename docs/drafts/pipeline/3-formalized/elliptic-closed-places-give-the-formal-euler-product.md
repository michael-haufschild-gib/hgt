# Actual elliptic closed places give the formal Euler product

- **Stage:** 3-formalized
- **Statement:** For `y²=x³−x` over `F₃`, the degree-cutoff products
  `P_N=(1−X)∏_{d(v)≤N}(1−X^{d(v)})` converge coefficientwise to `P`,
  and `P⁻¹` equals the actual point-count zeta series.

## Proof

The proved bounded-degree finiteness makes every product finite. Factors
of degree greater than `n` leave coefficients through `n` unchanged.
Thus `[X^n]P_N` stabilizes for `N≥n`; these coefficients define `P`.
Its constant coefficient is one.

The negative logarithmic ghost `−XP′/P` is additive on products.
The factor of degree `d` contributes `d` at positive multiples of `d`,
and the infinity factor contributes one at every positive degree.
The proved actual closed-point count identifies this sum with the
projective extension point count. The ghost of `P⁻¹` has the opposite
sign. Constant-one ghost uniqueness therefore identifies `P⁻¹` with
the existing point-count zeta series.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticFormalEulerProduct.lean`:
`tendsto_ellipticEulerPartial`, `ellipticEulerProduct_logGhost`,
`ellipticEulerProduct_inv_eq_zeta`. Direct Lean check passed. All three
capstones use exactly `propext`, `Classical.choice`, `Quot.sound`.
