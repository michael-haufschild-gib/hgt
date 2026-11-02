# Period relations of the actual Mayer scattering state

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 2–3.
- **Input:** [observable scattering state](../3-formalized/gauss-mayer-holomorphic-scattering-state.md).

## Theorem

For the certified state `H_w`, put `Φ_w(a)=H_w(a−1)` on the real period
segment `[1/2,7/2]` of the actual disc. For `Re w>0`, `w≠2`,

```text
Φ_w(a) = a^(−w) Φ_w(1/a)                         (1/2≤a≤2),
Φ_w(a) = Φ_w(a+1)+(a+1)^(−w) Φ_w(a/(a+1))       (1≤a≤2).
```

Every displayed argument lies in the actual disc. These are a concrete
period-function bridge toward a Hermitian realization; no positive form
or classification of all eigenfunctions is assumed.

## Proof mechanism

In `Re w>2`, the real-period state is the sum of two Barnes double zeta
series. Swapping the two cone coordinates and scaling all positive real
denominators proves inversion reciprocity. The difference between transfer
series at `z` and `z+1` is their first branch. The constant forcing cancels,
giving the shift relation for `H`; inversion then gives the three-term
identity for `Φ`.

Multiply by `w−2`. The certified filled state is holomorphic on the whole
right half-plane, as are all fixed positive-real powers. Continue both
identities from the absolute chamber and divide by `w−2`.

## Boundary of the claim

The corpus's native modular cutoff source has a nonzero forcing vector,
even though its bilinear pairing with the full scattering field vanishes
(`SelbergScatteringCutoffForcing`). Scalar cancellation cannot be treated
as an unforced Hilbert eigenfunction. The available deck Maass–Selberg
bound assumes level at least two and a cusp vector; it does not supply
the required level-one Mayer scattering form.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerScatteringPeriod.lean`:
`periodValue_barnes`, `reciprocity_absolute`, `reciprocity`,
`three_term_absolute`, `three_term`. Both identities include `w=1`;
only the actual state pole `w=2` is excluded.

All five declarations pass the kernel audit with only `propext`,
`Classical.choice`, and `Quot.sound`.
