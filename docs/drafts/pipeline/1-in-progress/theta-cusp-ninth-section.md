# Ninth theta section

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** For every `0<a<1/2`, the actual signed center-mixed theta Hankel matrix of size nine is positive definite.

The strict eighth section supplies the head. Parity reduces the new sign
to the integrated even five-dimensional block. Its unconditional sign
remains open.

## Established source restrictions

Every real constant pair of fourth/fifth diagonal flux loads is
[excluded globally](../5-failed/theta-cusp-fifth-even-origin-obstruction.md),
including the weighted representative at each critical aperture. The exact
positive origin region is nevertheless classified by its two Schur thresholds.

For the coupled loads
`u₁=(0,0,1,420,0)`, `u₂=(0,0,0,1,1568)`, the native origin form
is positive on their common kernel `span(e₀,e₁,v₈)`. The last-pair load
alone leaves an indefinite kernel. Both facts are formalized.

The [coupled origin-and-tail repair](../3-formalized/theta-cusp-fifth-even-coherent-origin-tail-repair.md)
preserves every mixed entry and the eighth-degree scale-seven witness.
However, [every common coefficient fails globally](../5-failed/theta-cusp-fifth-even-common-coupled-obstruction.md):
origin positivity requires `C>10⁹`, while scale seven rejects `C≥10⁹`.

The [unequal pair `(10⁸,10¹²)`](../3-formalized/theta-cusp-fifth-even-unequal-origin-repair.md)
is strictly positive near zero and cofinally, but the
[sixth-degree obstruction](../5-failed/theta-cusp-fifth-even-large-coupled-load-obstruction.md)
excludes every `C≥10⁸`, `D≥0` at scale seven, natively and at every
critical aperture.

## Remaining source problem

At `x₇=½log(7/π)`, put
`w=(-6272,336,-2,1/420,0)` and
`v₈=(-658560,47040,-420,1,-1/1568)`.
The [actual sixth-degree capacity](../3-formalized/theta-cusp-fifth-even-sixth-direction-capacity.md)
is `B₆∈(16·10⁶,50·10⁶)`, with weighted capacity
`B₆,a∈(B₆,70·10⁶)`. The corresponding directional energies are positive
exactly when `C+D/176400<B₆` and `C+D/176400<B₆,a`.

The [reduced pair `(C,D)=(10⁷,10¹²)`](../3-formalized/theta-cusp-fifth-even-reduced-coupled-repair.md)
is positive definite near the actual origin and cofinally, also at every
positive aperture. It passes the sixth-degree test at every critical aperture
and preserves the positive eighth-degree witness. The full matrix nevertheless fails at scale seven: a rational Schur direction
has positive native energy but negative corrected energy. It also fails at
every sufficiently small positive aperture. The
[Schur obstruction](../5-failed/theta-cusp-fifth-even-reduced-coupled-schur-obstruction.md)
also supplies the exact positive directional capacity.

The remaining constant-load question is full matrix compatibility between
the origin and the negative-compensation region. Neither separate Hermite
tests nor origin-and-tail positivity decides it. Independent coefficients
remain open; allowing a cross term
`E(u₁u₂ᵀ+u₂u₁ᵀ)`, with `C,D≥0` and `E²≤CD`, also preserves the common kernel and
zero-integral flux.

The [complete common kernel at scale seven](../3-formalized/theta-cusp-scale-seven-common-kernel.md)
is positive definite, with an explicit quadratic floor in adapted coordinates.

The [complete native fifth block at scale seven](../3-formalized/theta-cusp-scale-seven-native-fifth.md)
is also positive definite, with normalized quadratic floor `23f₁²/100`.

The [remaining endpoint conjecture](theta-cusp-coupled-endpoint-gap.md) is `U₇+S₀/G(0) ≻ 0`, where
`U₇=S₇/(−G(x₇))` and `S₀,S₇` are the actual complementary Schur forms
in the same load coordinates. This would give a positive coefficient matrix
satisfying both endpoint constraints. The inequality is unproved;
endpoint compatibility alone would still leave the intervening interval.

A global source certificate with a strict origin neighborhood would give
the integrated fifth block's strict sign. Radius-dependent matrix fluxes
remain outside the constant-load obstructions.
