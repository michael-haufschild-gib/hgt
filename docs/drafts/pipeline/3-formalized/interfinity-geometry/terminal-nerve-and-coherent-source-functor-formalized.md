# Terminal nerve and coherent source functor — formalized

- **ID:** `terminal-nerve-and-coherent-source-functor-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `terminal-nerve-and-coherent-source-functor.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/CoherentSourceFunctor.lean` | exponential-character detection and the three-way equivalence |
| `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/GramPhase.lean` | the cyclic Gram phase, its gauge invariance and its Bianchi identity |
| `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/GramNerve.lean` | the Gram-labelled terminal nerve as an `SSet`, persistence, face monotonicity |
| `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/GramStateSystem.lean` | realizability of labelled tuples by a finite-state clock system |
| `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/GramHornObstruction.lean` | an explicit nonfillable horn in `EuclideanSpace ℂ (Fin 3)` |

## Audited declarations

Namespace `GaloisForLFunctions.HTGeometry.Interfinity`.

- `tendsto_iff_tendstoLocallyUniformly_exp` — exponential characters detect their exponents;
- `hasCoherentBoundary_of_tendstoWeakStar`, `tendstoWeakStar_of_hasCoherentBoundary`,
  `coherent_source_tfae` — existence of a stable primitive, weak-star convergence of the source
  orbit, and coherence of the boundary are equivalent;
- `isStablePrimitive_unique` — uniqueness of the stable primitive;
- `cyclicPhase_gramGauge`, `cyclicPhase_bianchi` — gauge invariance of the cyclic phase and its
  Bianchi identity on a Hermitian Gram label;
- `nerve`, `nerveMap` — the Gram-labelled terminal nerve is a simplicial set and observer
  strengthening induces a simplicial map;
- `isUpperSet_gramDeathRegion`, `gramDeathRegion_subset_face`, `csInf_face_le_csInf` — death regions
  are upper sets and every face dies no later than its simplex;
- `realized_stateOverlapDatum_iff`, `realizes_stateOverlapDatum_iff`, `exists_state_neBot` — the
  realizability criterion for a finite-state clock system;
- `not_xRealizes_fullTriangle`, `yRealizes_fullTriangle`, `edge_realizes_iff` — an explicit horn
  with the same labelled one-skeleton as a fillable triangle but with no filler.

Every listed declaration is unconditional: `#print axioms` reports exactly `propext`,
`Classical.choice`, `Quot.sound`.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry.InterfinityGeometry
```

## Boundary

The nerve is built directly as a functor `SimplexCategoryᵒᵖ ⥤ Type u` with bundled `Type`
morphisms; the horn obstruction is a concrete three-vector configuration, not an abstract
existence claim.
