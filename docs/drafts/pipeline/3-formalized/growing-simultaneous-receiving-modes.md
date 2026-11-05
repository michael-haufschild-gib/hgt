# Growing simultaneous receiving modes

- **ID:** growing-simultaneous-receiving-modes
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** review-0411 §2.1, A37.

## Result

For each critical multiple `K>0`, there is a monotone mode cutoff `R(X)→∞`
with `R(X)!≤X` eventually. At conductor cutoff `M(X)=R(X)! X²` and horizon `X⁴⁰`,
uniformly over charges `|t_m|≤1`, `1≤m≤R(X)`:

- exact harmonic neutrality and prescribed generator coordinates;
- vanishing adjunction, physical input square and complete physical energy;
- every complementary receiver reads `t_m/80`, with maximal error tending to zero;
- receiver norm squares approach `1/20` uniformly over the growing mode set.

The conductor cutoff is monotone, tends to infinity, and eventually satisfies
`M(X)≤X³`. Every prescribed infinite real charge profile, including unbounded
profiles, also admits a growing cutoff with these receiving limits. That cutoff
may depend on the profile. No numerical growth rate for `R(X)` is asserted.

## Proof

The fixed-mode statements are in `SimultaneousCompleteReceivingLaw`.
Linearity of the centered packet reduces uniform signed errors to a finite matrix.
Polarization reduces the complete quadratic energy to its values on basis vectors
and their sums. Finite sums of these errors give charge-independent bounds.
The adjunction estimate already has an explicit common-prime-mass denominator.

Choose a common threshold `T_r` at tolerance `1/(r+1)`, including the factorial
constraint. Set `R(X)=max{r≤X : r=0 or T_r+r≤X}`. The admissible sets increase,
and every fixed `r` is eventually admissible. Thus `R` is monotone and cofinal;
the error bound `1/(R(X)+1)` tends to zero. The same construction applied to
the fixed finite restrictions of an arbitrary charge profile proves its
unbounded-profile variant. Finally `R(X)!≥1` gives `M(X)≥X²`, and the imposed
factorial constraint gives `M(X)≤X³`.

## Lean

Source: `CriticalScaleArithmeticRigidity/ReceivingCharges/GrowingSimultaneousReceivingModes.lean`.
Namespace: `GaloisForLFunctions.CriticalScaleArithmeticRigidity`.

- `tendsto_simultaneousReceivingError`
- `eventually_simultaneousReceivingControl`
- `exists_growing_simultaneousReceivingControl`
- `exists_growing_simultaneousReceiving_vanishing`
- `exists_growing_prescribedReceiving`
- `exists_growing_simultaneousReceiving_conductors`

Direct source check and all six transitive axiom audits passed; only `propext`,
`Classical.choice`, and `Quot.sound` occur. Owning umbrella wired; import closure
acyclic and excludes that umbrella. A37 is closed.
