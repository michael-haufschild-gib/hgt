# Stable-primitive exactness topology — formalized

- **ID:** `stable-primitive-exactness-topology-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `stable-primitive-exactness-topology.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/StablePrimitiveExactness.lean` | cochain slices, stable-primitive quotients, the two short exact sequences |
| `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/StableDeathRegion.lean` | death regions, the stable-exactness topology, observer covariance |
| `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/StableScottRealization.lean` | the Scott and Sierpinski realizations, specialization preorder, `T₀` reflection |

All three are reachable from `GaloisForLFunctions.HTGeometry` through
`GaloisForLFunctions.HTGeometry.InterfinityGeometry`.

## Audited declarations

Namespace `GaloisForLFunctions.HTGeometry.Interfinity.CochainSlice`, except the last covariance
group which lives in `GaloisForLFunctions.HTGeometry.Interfinity.SliceEquiv`.

- `stable_shortExact`, `dbar_injective`, `range_dbar` — the stable-primitive sequence
  `0 → A/(S ⊔ ker d) → Z^n/dS → Z^n/dA → 0`;
- `compare_shortExact`, `ker_compare`, `compareKernelEquiv` — the comparison sequence for
  `S ≤ T` and the exact identification of its kernel;
- `compare_ne_zero_of_toOrdinary_ne_zero` — immortality of classes with nonzero ordinary image;
- `mem_map_d_iff`, `dbarEquiv` — the three-gate criterion and the exact-slice collapse;
- `isUpperSet_deathRegion`, `upperSet_le_exactnessTopology` — death regions are upper sets and the
  exactness topology is coarser than the upper Alexandrov topology;
- `SliceEquiv.deathRegion_comp`, `SliceEquiv.image_deathRegion`, `SliceEquiv.continuous_of_sliceEquiv`,
  `SliceEquiv.homeomorph` — covariance of death regions along a slice isomorphism, continuity, and
  the induced homeomorphism;
- `exactnessTopology_eq_induced_scott`, `exactnessTopology_eq_induced_scott_range`,
  `exactnessTopology_eq_induced_sierpinski`, `exactnessTopology_eq_induced_sierpinski_range` — the
  topology is exactly the initial topology of the profile map into the Scott/Sierpinski targets;
- `specializes_joint_iff`, `inseparable_joint_iff` — the observable preorder is coordinatewise
  inclusion of stable-coboundary profiles, and the `T₀` reflection identifies observers exactly
  when every profile agrees.

Every listed declaration is unconditional: `#print axioms` reports exactly `propext`,
`Classical.choice`, `Quot.sound`.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry.InterfinityGeometry
```

## Boundary

The formalized statements are the paper card's, with the ambient category kept concrete: a slice is
a linear map with a designated cocycle submodule containing its range, which is exactly what all
statements of the card use.  No topological vector-space structure is assumed on the chain groups,
because none is used.
