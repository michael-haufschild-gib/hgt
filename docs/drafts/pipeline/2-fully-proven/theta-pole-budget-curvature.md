# Pole-budget curvature of the theta source

- **Stage:** 2-fully-proven
- **Type:** THEOREM — Lean audit pending
- **Source:** `ThetaCuspSections/ExplicitCurrentCore`; `RHTower/WeilDeletionZeroSide`.

For the complete theta source, its second moment satisfies
`∫₀∞ x² Φ(x) dx ≤ (4/169) Ξ(0)`.
Consequently `Ξ(b) ≥ Ξ(0)(1−4b²/169)` for every real `b`.

Write `λ=(ρ−1/2)/i`, `A=Re(λ²)`, `B=Im(λ²)`. Existing zero geometry gives
`A>81/4`. The exact identity

`82(A+1/4)(A²+B²)−81A((A+1/4)²+B²)`
`=A(A+1/4)(A−81/4)+(A+41/2)B² ≥0`

proves `Re(λ⁻²) ≤(82/81) Re(1/(ρ(1−ρ)))`.
Both series are absolutely summable. Their exact sum rules yield
`2∫₀∞x²Φ(x)dx ≤ Ξ(0)(82/81) poleSharpConstant`.
The existing bound `poleSharpConstant≤233/5000` implies the stated moment
bound by rational arithmetic. Integrating `cos(bx)≥1−b²x²/2` against the
positive source proves the parabolic minorant.

The pair-floor estimate also holds on `|b|≤13/2`: the online denominator is
at most `a²+γ²+13|γ|+169/4`, while off-line zeros have `|γ|>67`.
Thus `Re ξ′/ξ≥0.0076a` on this wider window. Aperture monotonicity of
`|ΞC|²` and `Ξ(0)≥49/100` give
`current(a,b)≥(a/275)(1−4b²/169)²` for `0<a≤1/2`, `|b|≤13/2`.

This retains real-part cancellation discarded by the previous norm estimate.
It does not by itself pay another rank.

Exact formalization: `ThetaCuspSections/PoleBudgetCurvature.lean`.
