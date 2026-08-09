# Multi-time polyhedral horizon — formalized

- **ID:** `multi-time-polyhedral-horizon-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `multi-time-polyhedral-horizon.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `.../InterfinityGeometry/MultiTimeRegions.lean` | the open convex polyhedra `𝒪_β ⊇ D_β` and their coordinate description |
| `.../InterfinityGeometry/ParametricSmoothness.lean` | **smoothness of parametric averages** — differentiation under the integral sign, absent from mathlib |
| `.../InterfinityGeometry/MultiTimeHadamard.lean` | Hadamard's lemma in one coordinate of several |
| `.../InterfinityGeometry/MultiTimeFixedFaces.lean` | the Boolean lattice of fixed faces and its deepest stratum |
| `.../InterfinityGeometry/MultiTimeIntegrability.lean` | the cubical source cochain lies in the weighted space; the norm factorizes |
| `.../InterfinityGeometry/MultiTimeTensorFinitePart.lean` | the tensor finite part, the iterated coboundary, face stability in both directions |
| `.../InterfinityGeometry/MultiTimeSectorialPhase.lean` | the tensor sectorial limit and the conormal phase covector |

## Audited declarations

Namespace `GaloisForLFunctions.HTGeometry.Interfinity`.

Item 1 — `integrable_multiLaplaceCochain_sq` (finite for every finite time tuple, exactly because
`β_j > −2`), `integral_multiLaplaceCochain_sq` (the squared norm factorizes),
`multiLaplaceCochain_add` (the coordinatewise cocycle law).

Item 2 — `mem_multiObserverRegion_iff`, `mem_multiStableRegion_iff`, `multiStableRegion_subset`,
`isOpen_multiObserverRegion`, `isOpen_multiStableRegion`, `convex_multiObserverRegion`,
`convex_multiStableRegion`, `multi_deathCut_add`, `multiStableRegion_eq_iff` — the two regions are
open convex polyhedra with the stated coordinate description; `tensor_iterated_coboundary` and
`tensor_iterated_difference_eq_alternating_sum` — applying the difference of transport and identity
in every coordinate returns the tensor source pairing, and that iterated difference is the
alternating sum over the face lattice; `tensor_sourcePairing_eq_cube` — the tensor source pairing
is the cubical integral of the source cochain; `tendsto_tensorFaceOrbit`,
`not_tendsto_tensorFaceOrbit`, `tensorFaceStable_iff` — face stability of every nonempty face holds
exactly on `D_β`.

Item 3 — `multi_eq_face_singleton`, `multi_eq_face` (the common fixed subspace of the times in `J`
is the face restriction), `multi_eq_smul_delta` (the deepest stratum is the line spanned by
evaluation at the origin), `zeroAt_comp`, `faceChart_comp` (the Boolean lattice structure).

Item 4 — `tendsto_ctensorFinitePart`, `tendsto_ctensorFinitePart_ray`
(`(∏_j R_j^{a_j}) T_z η_a → c ∏_j Γ(a_j)e^{-ia_jθ_j} δ₀`), `hasFDerivAt_terminalPhase` and
`phaseCovector_single` (the phase differential is the conormal covector, with `j`-th component
`−a_j`), `phaseCovector_single_eq_deficit` (`−a_j = −β_j − ρ_j`),
`hasDerivAt_multi_terminal_arg` (the angular slope of the argument in one coordinate),
`arg_terminalPhase`.  The `a_j = 0` coordinates obey the one-dimensional logarithmic law
`tendsto_ctransportedFinitePart_log` of the companion card
`spectral-terminal-horizon-model-formalized.md`.

Every listed declaration is unconditional: `#print axioms` reports exactly `propext`,
`Classical.choice`, `Quot.sound`.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry.InterfinityGeometry
```

## Boundary

The parametric-smoothness theorem needed for the several-variable Hadamard lemma had to be built
from scratch: mathlib differentiates under the integral sign once, but has no statement preserving
every finite order.  The tensor statements are formalized on tensor charts, which is exactly the
class the card's own proof uses ("`(6)` and the semigroup are tensor products").
