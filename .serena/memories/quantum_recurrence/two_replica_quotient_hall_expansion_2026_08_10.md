# Two-replica quotient Hall expansion (2026-08-10)

## Result
New module: `formal/GaloisForLFunctions/HTGeometry/TwoReplicaQuotientHallExpansion.lean`.

Abstract kernel-saturation promotion:
if a family of linear maps kills `N`, a subspace `Ustar` maximizes family deficiency, and
`finrank Ustar ≤ finrank shadow(Ustar) + finrank N`,
then every `U` satisfies
`finrank U ≤ finrank shadow(U) + finrank (U ⊓ N)`.
Proof applies the maximum-defect property to `U ⊔ N`, uses unchanged shadow because the family kills N, and the modular finrank identity.

Two-replica specialization for q-local collective Pauli commutators on a preconnected register with q ≥ 2:
1. Every collective commutator kills the global identity and global replica swap.
2. Every subspace loses at most its own intersection with the synchronized identity/swap plane.
3. Every subspace disjoint from that plane is rank nondecreasing under the complete q-local shadow.
4. The simultaneous common kernel is exactly the synchronized plane.

Umbrella import added in `formal/GaloisForLFunctions/HTGeometry.lean`.

## Verification
- `lake env lean GaloisForLFunctions/HTGeometry/TwoReplicaQuotientHallExpansion.lean` passed.
- Final targeted `lake build GaloisForLFunctions.HTGeometry.TwoReplicaQuotientHallExpansion` passed.
- Axiom audit on abstract promotion, kernel inclusion, quotient Hall law, and exact common-kernel theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` in new module.
- Generated `formal/LEAN_API.md`, `formal/LEAN_GAPS.md`, `formal/LEAN_OVERVIEW.md` refreshed.
- Global lint failure is unrelated: concurrent modules not imported by theorem-area umbrella.

## Meaning / corrected frontier
This closes the specific two-replica q-local mixed-subspace Hall/common-kernel statement and strengthens the older canonical +2 maximum-deficiency bound into an exact intersection-corrected law. It is new to this corpus; no external-priority claim was made.

Later same-session corpus audit found arbitrary-replica central-Casimir Hall and positive-length two-local word Hall were already formalized in `CentralCasimirCommonKernelCorrection.lean` and `FiniteReplicaTwoLocalPauliWordHall.lean`. Therefore growing-replica algebraic Hall is not the live Brown obstruction. The remaining core is nonlinear quenched static-to-circuit transfer: finite-scale undistortion / complete shortcut packing after return and carrier excision.

A newly arrived free-Fock Pauli cavity branch does not directly close this: it is a free/noncrossing surrogate, while ordinary static Gaussian coefficients retain crossing Wick contractions. See `mem:quantum_recurrence/static_gaussian_crossing_memory_2026_08_10`.