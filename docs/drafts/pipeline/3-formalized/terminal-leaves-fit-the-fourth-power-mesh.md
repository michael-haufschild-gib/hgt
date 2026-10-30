# Terminal leaves fit the fourth-power mesh

- **ID:** terminal-leaves-fit-the-fourth-power-mesh
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/fourth-power-mesh-signed-saving.md
- **Statement:** At `M = N²`, the canonical square-root core has nonempty
  energy at most `(9/25)N⁵`. At `M = j⁴`, its normalized nonempty energy is
  at most `(9/25)j²`, hence its prefix is at most `(9/25)J³`.

## Proof

**[PROVED HERE]** Let `P_M = criticalMovingSquareCore M` and let
`L_p = mobiusDivisorSelectionFibre M P_M {p}`. The existing quotient estimate
`sum_mobiusDivisorPrimeFibre_sq_le_quotient` gives
`L_p² ≤ (9/25)M floor(M/p)² ≤ (9/25)M³/p²`.
At `M = N²`, every unprocessed prime exceeds `N`. Thus
`Σ L_p² ≤ (9/25)N⁶ Σ_{n>N}n⁻² ≤ (9/25)N⁵`, using
`Sieve.tsum_inv_sq_shift_le`. The case `N = 0` is empty.
`mobiusDivisorSelectionEnergy_terminal` identifies this sum with retained
energy minus the head square. Substituting `N = j²` and dividing by `j⁸`
gives the mesh bound; summing `j² ≤ J²` over at most `J` terms gives its prefix.

## Meaning

The nonempty fibres already fit the requested cubic mesh scale. This does
not bound the complete signed source: terminal completion adds the leaves
to the head before squaring. Cancellation in that scalar sum remains open.

## Verification

- [x] Dependency-closed paper proof from existing quotient and terminal identities.
- [x] `RHTower.criticalMovingSquareCore_leafEnergy_le` and
  `RHTower.criticalMovingSquareCore_energy_sub_head_sq_le` prove the square-cutoff bound.
- [x] `RHTower.criticalMovingSquareCore_fourthMesh_leafPrefix_le` proves the cubic prefix bound.
- [x] `lake --old env lean GaloisForLFunctions/RHTower/MobiusDivisorTerminalLeafMeshBound.lean`
  passes; all six public declarations depend only on `propext`, `Classical.choice`,
  and `Quot.sound`. Imported by `RHTower.lean`.
