# Actual character contours have uniform conductor cost

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** For each `ε>0`, one pair `c,B>0` works for all nonprincipal characters modulo every `q≥1`. Set `L=log(q(T+5))`, `M=Bq^εL³`. For `x≥1`, `T>0` and `0<δ≤cq^(-ε)/L²`, the actual signed tent sum is bounded by

`(2π)^(-1)[16x^(1+δ)/(δ²T) + Mx^(1−δ)π/(1−δ) + 4Mδx^(1+δ)/T²]`.

## Proof

[PROVED HERE] The [uniform logarithmic-derivative theorem](../3-formalized/dirichlet-logarithmic-derivatives-have-uniform-conductor-cost.md) supplies nonvanishing and bound `M` throughout the closed rectangle with real endpoints `1±δ` and imaginary endpoints `±T`; choose its constant `c≤1/8`. The actual integrand `−(L'/L)(s,χ)x^s/s²` is analytic in a neighborhood of that rectangle, so its contour integral vanishes.

The existing exact signed Perron identity is absolutely integrable on the right line. Its two infinite tails total at most `16x^(1+δ)/(δ²T)`, using the actual absolute-convergence bound `|L'/L|≤8/δ²`. The left edge costs at most `Mx^(1−δ)π/(1−δ)`, since the full integral of `((1−δ)²+t²)^(-1)` is `π/(1−δ)`. Each horizontal edge costs at most `2Mδx^(1+δ)/T²`. The rectangle identity and triangle inequality give the displayed bound, including both tails and both horizontal edges. The constants precede the quantifiers over modulus and character.

## Formalization and scope

Lean: `GaloisForLFunctions/RHTower/DirichletCharacterUniformPerron.lean`; audit pending. The only width restriction is numerical; every analytic input is supplied by the actual character. Selecting a common contour scale, signed unsmoothing, and residue recovery remain necessary for the growing-conductor source theorem.
