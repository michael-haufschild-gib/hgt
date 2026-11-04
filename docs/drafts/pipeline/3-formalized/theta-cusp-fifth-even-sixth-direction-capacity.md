# Sixth-degree capacity of coupled theta loads

- **Stage:** 3-formalized; complete-source and matrix canonical checks pass.
- **Wall:** Σ6; no integrated rank-nine sign claimed.
- **Claim:** The scale-seven sixth-degree test has exact native capacity `B₆∈(16·10⁶,50·10⁶)` and weighted capacity `B₆,a∈(B₆,70·10⁶)` for `0<a<1/2`.

Let `x₇=½log(7/π)`, `r₇=2x₇`, `f=f₁(x₇)`, and
`w=(-6272,336,-2,1/420,0)`. This is the sixth Hermite polynomial at
variance `56`, divided by `420`. Write `E₆=wᵀH₅(x₇)w`.
For `u₁=(0,0,1,420,0)` and `u₂=(0,0,0,1,1568)`,
`u₁·w=-1`, `u₂·w=1/420`. Thus the coupled correction reads exactly
`L=C+D/176400` in this direction.

Retain the first two theta atoms and set `z=e^(−21)`, so `0<z≤10⁻⁹`.
Their normalized energy is
`P₆(49,14)+8zP₆(196,35)+16z²P₆(784,56)`, where `P₆`
is the quadratic form of the radial moment polynomials in `w`.
The proved radial coefficient tables give this expression strictly between
`89·10⁶·121` and `199·10⁶·121`. The Cauchy remainder in the same
quadratic form is at most `10⁶ f²`. Consequently

`88·10⁶ f² < E₆ < 200·10⁶ f²`.

At scale seven the first-atom slope is exactly `−197f/22`.
The source remainder bounds give `f≤Φ≤1.01f` and `Φ′≥−9.1f`;
`x₇≤7/16` then gives `G(x₇)>−(11/2)f²`.
The established opposite bound is `G(x₇)≤−(229/55)f²`.
Therefore

`B₆=E₆/(−G(x₇)) ∈ (16·10⁶,50·10⁶)`.

For the literal weighted flux, put `W_a=r₇sinh(ar₇)` and
`F_a=K_a′(r₇)<0`. The strict aperture slack gives `F_a>W_aG(x₇)`,
while the established bound gives `F_a≤−3W_af²`. Hence

`B₆,a=W_aE₆/(−F_a)`, with `B₆<B₆,a<70·10⁶`.

The native and weighted directional energies are positive exactly when
`L<B₆` and `L<B₆,a`, respectively. Every `C≥10⁸`, `D≥0` is
strictly negative at this point, including the explicit positive-origin
pair `(10⁸,10¹²)`. Conversely, `(10⁷,10¹²)` has `L<16·10⁶`
and passes both sixth-degree tests. This asserts positivity in one
direction; full matrix positivity remains separate.

Lean: `EvenFiveBoundary.sixth_energy_bounds`, `sixthCapacity_bounds`,
`sixthWeightedCapacity_exceeds_source`, and `sixthWeightedCapacity_bounds`
in `ThetaCuspSections/FifthEvenInheritedLoadBoundary.lean` prove the
actual source estimates. In `FifthEvenCoherentRepair.lean`,
`coupledRepair_sixth_positive_iff` and
`coupledWeightedRepair_sixth_positive_iff` identify the exact matrix-form
regions; `coupledRepair_not_posSemidef_of_large_first` and its weighted
counterpart prove the obstruction. `reduced_coupledRepair_sixth_positive`
and `reduced_coupledWeightedRepair_sixth_positive` prove the smaller pair's
directional positivity. All seventeen statements pass canonical checks
and use only `propext`, `Classical.choice`, and `Quot.sound`. Both modules
are in the owner umbrella.
