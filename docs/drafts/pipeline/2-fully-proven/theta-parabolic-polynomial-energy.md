# General weighted polynomial exterior estimate

- **Stage:** 2-fully-proven
- **Type:** THEOREM — Lean audit pending
- **Source:** `ThetaCuspSections/LegendrePolynomialKernel`.

Let `R>0`, `deg p≤n`, and
`E_R(p)=∫₋ᴿᴿ((1−b²/R²)p(b))² db`.
For `|b|≥10R`,

`p(b)² ≤ (16/15)(100/99)²(n+5/2)c_(n+2)²/R · (|b|/R)^(2n) E_R(p)`.

Apply the general Legendre kernel to
`q(x)=(1−x²)p(Rx)`, of degree at most `n+2`.
Its interval energy is `E_R(p)/R`. For `x=|b|/R≥10`,
`(x²−1)²≥(99/100)²x⁴`. Cancel this positive factor from the kernel
bound, retaining exponent `2n` and the leading coefficient `c_(n+2)`.
If `E_R(p)=0`, the bound forces `p` to vanish on an infinite ray;
hence `E_R(p)>0` for every nonzero polynomial.

Exact formalization: `ThetaCuspSections/ParabolicPolynomialKernel.lean`.
