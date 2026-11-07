# Coupled analytic tail of the theta current

- **Stage:** 2-fully-proven
- **Type:** THEOREM — Lean audit pending
- **Source:** `ThetaCuspSections/TheSharpCurrentTail`.

For every real `b` and `|a|≤1/2`,

`|current(a,b)| ≤ 1125000 |a| exp(−7|b|/5)`.

Set `H(z)=ΞC(b−iz)ΞC(b+iz)`. This entire function is even. On `|z|=3/2`,
the existing strip bound gives

`|H(z)| ≤ 10⁶ exp(−(7/10)(|b+Im z|+|b−Im z|))`
`≤10⁶ exp(−7|b|/5)=B`.

Subtract Cauchy's derivative formulas at `a` and `−a`. Evenness gives

`2H′(a)=(2πi)⁻¹ ∮ H(z)[(z−a)⁻²−(z+a)⁻²] dz`.

The difference of the two kernels is `4az/(z²−a²)²`. On the circle,
`|z²−a²|≥9/4−1/4=2`, so its norm is at most `(3/2)|a|`.
The normalized circle integral therefore gives `2|H′(a)|≤(9/4)B|a|`.
Real symmetry of `ΞC` identifies `H(a)=|ΞC(b−ia)|²` and `H′(a)=current(a,b)`.

The factor `32` improvement retains the common contour phase and evenness
before taking absolute values. No new zero verification is used.

Exact formalization target: `ThetaCuspSections/CoupledCurrentTail.lean`.
