# Affine observer holonomy and the global-section law — Lean certificate

- **ID:** `affine-observer-holonomy-and-global-section-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `affine-observer-holonomy-and-global-section-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Modules

| File | Contents |
|---|---|
| `HTGeometry/AffineObserverHolonomy.lean` | §1–2 rooted spanning-tree gauge, §3 the global-section theorem |
| `HTGeometry/ObserverFieldEquation.lean` | §4 observer field equation, §5 uncertainty trichotomy, §6 gauge covariance, §8 countable contexts |
| `HTGeometry/HolonomyGeneratingSet.lean` | §7 tree independence and generating-set defect comparison |

Namespace `GaloisForLFunctions.HTGeometry`.

## Card statement to Lean name

| Card | Lean |
|---|---|
| §2 spanning-tree gauge with affine transport | `TreeGauge` |
| §2 tree-exact sections are exactly the based ones | `IsTreeExact`, `IsBased`, `isTreeExact_iff_isBased` |
| §3 chord data, based holonomy and its source current | `ChordData`, `ChordData.holonomy`, `ChordData.current` |
| §3 Thm 3.1 unified objects are affine holonomy fixed points | `ChordData.chord_eq_iff_holonomy`, `ChordData.isExact_iff` |
| §3 linear case: the source current vanishes | `treeGauge_a_eq_zero`, `ChordData.isExact_linear_iff` |
| §4 defect operator, current vector, holonomy Laplacian, energy | `holonomyDefect`, `currentVector`, `holonomyLaplacian`, `sourceCurrent`, `holonomyEnergy` |
| §4 Thm 4.1 exactness is a zero of the energy and a normal equation | `exact_iff_energy_eq_zero`, `holonomyLaplacian_apply_of_exact`, `solutionSet_eq`, `ker_holonomyLaplacian` |
| §5 Cor 5.1 exact, hard and almost-invariant regimes | `holonomy_tfae`, `exists_almost_invariant_unit_sequence`, `ker_holonomyDefect_ne_bot_iff` |
| §6 Prop 6.1 frame covariance of holonomy and energy | `gaugeHolonomy`, `gaugeHolonomy_apply`, `holonomyEnergy_gauge`, `exact_gauge_iff` |
| §7 Prop 7.1(1) the exact root values do not depend on the tree | `rootSolutionSet`, `rootSolutionSet_tree_independent` |
| §7 Prop 7.1(3) two finite generating sets bound each other's defect | `unitaryDefect`, `exists_defect_bound`, `defectSumSq_le_of_closure` |
| §8 Thm 8.1 and Cor 8.2 cofinal observer globalization | `observerContext`, `nonempty_iInter_observerContext_iff`, `tendsto_infDist_observerContext_of_empty` |

§7(2), conjugacy of based holonomy groups under a change of root, is the gauge covariance
`gaugeHolonomy` / `exact_gauge_iff` applied to the root transport.

## Verification

Foreground per-file elaboration and a cached foreground `lake build` of the three modules pass.
The axiom audit of `holonomy_tfae` and `defectSumSq_le_of_closure` reports only `propext`,
`Classical.choice`, `Quot.sound`.

## Boundary

The holonomy law is a statement about affine transport data on a graph of Hilbert spaces.  It
identifies the obstruction to a global section; it does not exhibit any arithmetic realization of
that obstruction.
