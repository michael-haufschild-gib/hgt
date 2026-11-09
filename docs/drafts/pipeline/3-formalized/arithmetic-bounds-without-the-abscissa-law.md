# Arithmetic bounds without the abscissa law

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Module:** `ExceptionalLayerTheory/ArithmeticBoundsWhenTheAbscissaLawFails.lean`.

## Statements

Either AAL holds, or the Mertens sum satisfies `|M(x)| ≤ C x^β` for some
`C ≥ 0` and `0 ≤ β < 1`, for every integer `x ≥ 1`.

Either AAL holds, or there is `1/2 ≤ β < Θ`, with `β < 1`, such that
heavy prime returns satisfy `log t ≥ c y^(1−β)` for some `c > 0`.
Here heaviness has precision `1/1000`, the return tolerance is at most
`1/20`, and the conclusion holds for sufficiently large `y` and `t`, as
specified in the Lean statement. The exponent is strictly larger than
`1−Θ`: the finite top layer does not determine this return obstruction.

## Proof

Failure of AAL gives a top zero layer strictly below one, hence quasi-RH.
The established Möbius-rate equivalence supplies the Mertens bound.
The bilateral spectral-gap theorem also bounds all sufficiently high
zeros in a narrower strip with endpoint `β < Θ`. Applying the heavy-return
theorem to that tail gives exponent `1−β`.

## Lean verification

Direct `lake --old env lean` check exited 0. Declarations
`asymptoticAbscissaLaw_or_mertens_power_saving` and
`asymptoticAbscissaLaw_or_stronger_heavy_return_power_bound` depend only on
`propext`, `Classical.choice`, `Quot.sound`. Imported by
`ExceptionalLayerTheory.lean`. These alternatives assert neither failure
of AAL nor quasi-RH, and do not contradict one another.
