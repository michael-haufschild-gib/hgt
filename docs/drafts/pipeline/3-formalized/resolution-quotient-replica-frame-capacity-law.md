# Resolution-quotient replica frame-capacity law

- **ID:** `resolution-quotient-replica-frame-capacity-law-formalized`
- **Stage:** 3-formalized
- **Status:** `[LEAN-FORMALIZED] [TARGET-SIDE BRIDGE] [NOVELTY UNVERIFIED]`
- **Paper proof:**
  `../2-fully-proven/resolution-quotient-replica-frame-capacity-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ResolutionQuotientReplicaFrameCapacityLaw`
- **Date:** 2026-08-14

## Formalized theorem set

For every nonempty finite family of normalized finite-dimensional pure states and every
Hilbert--Schmidt resolution `delta`, Lean constructs a nonempty finite maximal separated subset.
It proves that subset covers the complete family at radius `delta` and remains strictly
`delta`-separated:

```text
exists_maximalSeparated_finset_cover
exists_resolutionPacking_projector_cover
```

The module proves the exact normalized-projector identity

```text
||P_psi-P_phi||_HS^2 = 2 - 2 Fidelity(psi,phi)
```

and uses it to bound complete replica frame energy of every separated center dictionary:

```text
F_r <= N^(-1) + (1-N^(-1)) (1-delta^2/2)^r.
```

If the off-diagonal replica remainder is at most `N^(-1)`, Lean proves `F_r <= 2N^(-1)`.
Declarations:

```text
norm_finitePureProjectorEuclidean_sub_sq
finite_average_pow_le_diagonal_offDiagonal
resolutionPacking_replicaFrameEnergy_le
exists_resolutionPacking_replicaFrameEnergy_le
resolutionPacking_replicaFrameEnergy_le_two_inv
```

Finally, every capture of an original target at projector radius `epsilon` transfers to one center
at radius `epsilon+delta`; normalized-projector fidelity is at least
`1-(epsilon+delta)^2/2`, and every replica power preserves that lower bound when the threshold is
nonnegative:

```text
resolutionPacking_completeTarget_transfer
finitePureStateFidelity_ge_of_projector_distance_le
resolutionPacking_fidelity_transfer
resolutionPacking_replicaFidelity_transfer
```

The module then substitutes the `2/N` estimate into the already formalized adaptive
observer--spectral law.  Every qualifying weighted shortcut history obeys the same
centralizer-centered recurrence-energy inequality with target factor `2/N`:

```text
adaptive_resolutionPacking_shortcuts_force_recurrence_energy
```

## Verification

Commands run from `formal/`:

```text
lake env lean /tmp/hgt_resolution_packing.lean
lake env lean GaloisForLFunctions/HTGeometry/ResolutionQuotientReplicaFrameCapacityLaw.lean
lake build GaloisForLFunctions.HTGeometry.ResolutionQuotientReplicaFrameCapacityLaw
lake env lean /tmp/hgt_resolution_axioms.lean
```

Results:

- scratch proof: pass, no warnings;
- direct module check: pass;
- targeted leaf build: pass; no umbrella/full build run;
- module wired into `GaloisForLFunctions.HTGeometry`;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact frontier consequence

Raw circuit labels or raw occupied endpoint cardinality are not the certified capacity.  Formal
target-side invariant is cardinality of a resolution packing of occupied projectors.  The capstone
closes this target-geometry factor in the adaptive observer--spectral law.

It does **not** bound the centralizer-centered source recurrence energy, prove Brown first-onset
growth, establish a monotone or linear ramp, or select the first recurrence time.  Those remain the
open source-side problem for one ordinary time-independent local Hamiltonian.  The separate paper
counterexample showing why raw cardinality fails is not formalized in this module.
