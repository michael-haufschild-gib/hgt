# Static-orbit net no-go and circuit Bellman law — formalized closure

- **ID:** `static-orbit-net-no-go-and-circuit-bellman-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./static-orbit-net-no-go-and-circuit-bellman-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [FRONTIER CORRECTION]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.EuclideanSphereCoveringBound` (new)
- `GaloisForLFunctions.HTGeometry.StaticOrbitNetBellmanLaw` (new)
- `GaloisForLFunctions.HTGeometry.ExactPenaltyCircuitBellman` (reachable layers, layer distance)
- `GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw` (Duhamel, reused)
- `GaloisForLFunctions.HTGeometry.BoxDimension` (`externalCoveringNumber_image_le`, reused)

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

**Theorem A — small complete cover**
1. `HTGeometry.externalCoveringNumber_image_le` (already in the corpus) — equations `(1)`–`(2)`:
   an `ε/L`-cover of the source maps to an `ε`-cover of the image.
2. `volume_ball_eq_pow_mul`, `card_mul_pow_le_of_separated_finset`,
   `finite_and_ncard_le_of_separated` — the volumetric packing bound: an `η`-separated subset of a
   Euclidean ball of radius `R` is finite with `#S · (η/2)^m ≤ (R + η/2)^m`.
3. `exists_separated_net` — a maximal separated subset is an `η`-net obeying that bound;
   `exists_unitSphere_lipschitz_net` is equations `(3)`–`(4)`:
   every `L`-Lipschitz image of the unit sphere has an `ε`-net of at most `(1 + 2L/ε)^m` actual
   image points.

**Theorem B — the ordinary local-Hamiltonian shell**
4. `coefficientHamiltonian`, `isSelfAdjoint_coefficientHamiltonian`,
   `sum_abs_le_sqrt_card_mul_norm`, `norm_coefficientHamiltonian_sub_le` — equation `(5)` and the
   `√m` coefficient bound.
5. `norm_coefficientEvolution_sub_le` — equation `(6)`, from the corpus Duhamel bound
   `selfAdjoint_unitaryEvolution_norm_sub_le`.
6. `exists_staticOrbit_net` — equations `(7)`–`(8)`: a finite set of *actual orbit endpoints* of
   cardinality at most `(1 + 2|t|√m/ε)^m` covering the whole coefficient-sphere orbit image.

**Theorem C — the exact local-circuit recursion**
7. `reachSet_zero`, `reachSet_succ` — equation `(10)`.
8. `sSup_image_reachSet_succ` — equation `(12)` in the general form: any pairing intertwining the
   gate action with a pullback on the second argument obeys the max-plus recursion.
9. `sSup_unitaryOverlap_reachSet_succ` — its literal unitary-overlap instance
   `Y_{s+1}(v) = max(Y_s(v), sup_g Y_s(g* v))`.
10. `Monotone.map_ciSup_of_finite`, `sSup_image_reachSet_succ_monotone` — equation `(14)`: every
    increasing reader obeys the same law.
11. `infDist_union`, `infDist_image_act`, `layerDist_succ` — equations `(15)`–`(16)`, the min-plus
    metric recursion.

**Theorem D — robust Bellman calibration lower bound**
12. `le_length_of_bellmanCalibration` — equation `(19)`:
    `C_ε(v) ≥ Φ(v) − Φ(χ) − Lε` for every gate-Lipschitz calibration.

## Verification

- `lake env lean` clean, no warnings, on both new modules.
- `lake build GaloisForLFunctions.HTGeometry.StaticOrbitNetBellmanLaw` — green.
- `#print axioms` on statements 2–12: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella imports present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

The frozen core `(20)`–`(21)` (autonomous Bellman escape at the Brown schedule) is open research
on the parent cards, not formalization debt for Theorems A–D.
