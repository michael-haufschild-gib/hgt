# Off-line recurrence forces divergent zeta residue mass

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Γ215; approximate arithmetic constituents.
- **Statement:** If a nonzero real-scale Wiener expansion has a zero in a strip about the critical line, the sum of `mρ ‖ζ(ρ)/ρ‖` over all its strip zeros diverges, without assuming purity.

## Proof

1. Split Euler products into a fixed head and an exponential prime tail. Hardy
   evaluation and prime-torus second moments control the tail outside arbitrarily
   small Haar measure. Prime-flow equidistribution and disc-uniform Euler
   approximation transfer a fixed positive floor to zeta at all but a small
   proportion of heights. The functional equation gives the left-side floor.
2. An off-line zero of a holomorphic almost-periodic function recurs in discs
   through a set of shifts of positive lower density. Where zeta exceeds the
   floor, a recurrent zero `p` satisfies `b ≤ |p| |ζ(p)/p|`.
3. A summable family of weights cannot support those shadows: dominated
   convergence gives `Σ min(1/T,wᵢ) → 0`, hence the total measure of fixed-length
   intervals selected by `wᵢ ≥ b/(2T)` is `o(T)`.
4. Thus any off-line zero forces divergence of the unweighted zeta residues.
   Multiplicity is at least one. If all zeros lie on the critical line, the
   summable-pole jump law gives the multiplicity-weighted divergence directly.

## Lean

- `RHTower.exists_zeta_offLine_disc_floor` — compiled, from
  `ZetaDiscLowerBoundsAtTypicalHeights` and `ZetaDiscLowerBoundsOnBothSides`.
- `HTGeometry.eventually_volume_weighted_vertical_shadows_le` — compiled in
  `SummableMassHasSparseShadows`.
- `ConstituentTheoryOfTheZeros.not_summable_zeta_weights_of_offLine_zero` — compiled.
- `ConstituentTheoryOfTheZeros.expansion_zero_forces_nonsummable_residues` —
  compiled in `OffLineZerosForceNonsummableResidues`.

All four modules passed `lake --old env lean`; programme umbrellas are wired.

This removes the purity restriction from residue divergence. B153 for bounded
constituents remains open. No zeta lower-bound or residue-summability input is assumed.
