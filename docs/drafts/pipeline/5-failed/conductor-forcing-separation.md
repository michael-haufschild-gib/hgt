# Exact separation of the conductor and forcing criteria

- **ID:** CDG-CONDUCTOR-FORCING-SEPARATION
- **Stage:** 5-failed — overlap of these sufficient criteria retired
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Count:** Excluded from the significant-contribution count.

## Scope

The existing sufficient conductor-horizon condition and sufficient
polar-corrected companion-forcing certificate have disjoint apertures.
This concerns those two certificates; it says nothing about the actual sign
of the odd detector between them and does not retire elliptic localization.

## Exact positive survivor

For the existing detector energy `H = deepZeroEnergyBound a delta w` and
norm bound `N = deepZeroNormBound a delta`, with their ordinary parameter
range `a>0`, `delta>=0`, and `0<w<=a/4`,

```
H <= (N/2) exp(delta a),
2 H^2 <= (N^2/2) exp(2 delta a).
```

Every successful certificate therefore satisfies

```
768 A log(|gamma|+3) < exp(2 delta a).
```

The first estimate follows from `w<=a`, `(wa)^(5/2)<=a^5`, and
`sinh^2(delta(a-2w))<=cosh^2(delta a)`, then
`cosh(delta a)<=exp(delta a)`. The leading forcing cost is at least
`384 A log(|gamma|+3) N^2`; every omitted cost term is nonnegative.
Cancellation of positive `N^2` gives the necessary aperture threshold.
This signal bound is the quantitative survivor, not a new positivity law.

For `delta<=1/2`, the exponential is at most `exp a`. The conductor
condition bounds `4 exp a` by `log(|gamma|+3)`, contradicting that necessary
threshold. The separation includes the endpoint `delta=1/2` and needs no
asymptotic height restriction.

## Second pass and status

Keeping the depth in `exp(2 delta a)` gives a necessary aperture law stronger
than the negative disjointness statement alone. The proof provides no
sufficient certificate above that threshold, so such a converse is not
asserted. No new arithmetic sign or exceptional-set estimate was found.

Paper argument and exact Lean proof are complete in
`ConjugateDiagonalGeometry/TheConductorForcingGap.lean`.
The individual source-only `lake --old env lean` check passed.
`two_mul_deepZeroEnergy_sq_le`, `forcing_requires_exponential_aperture`, and
`conductor_forcing_disjoint` each depend only on `propext`, `Classical.choice`,
and `Quot.sound`. The module is wired into its umbrella without compiling
the umbrella. The positive survivor and negative comparison are both verified;
only the overlap route is retired. Elliptic localization remains open.
