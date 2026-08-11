# Witt formation mechanics core — formalized

- **ID:** ULF-WFM-2-LEAN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper parent:**
  `../../../2-fully-proven/universal-law-field/witt-formation-mechanics/witt-ghost-formation-conservation-reconstruction-and-adams-memory-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.WittFormationMechanics`
- **Status:** [LEAN-CERTIFIED FINITE CORE] [UMBRELLA WIRED] [NO AXIOMS ADDED]
  [EXACT ADAMS MEMORY] [NOT RH]

## Certified surface

For a finite complex mode packet, Lean proves:

1. signed exterior and complete-homogeneous formation obey exact coefficientwise inverse
   conservation;
2. Newton's identity generates the exterior response from ghost/power-sum response;
3. equality of the first `r` ghosts reconstructs the full unordered `r`-mode multiset;
4. Adams intervention extracts the corresponding spaced ghost subsequence;
5. a surjective powered-mode bucket aggregates the ghost sequence with exact nonzero multiplicity
   weights;
6. the aggregate modes generate the post-Adams characteristic-polynomial recurrence;
7. every saturated Hankel window has rank exactly the number of distinct powered-mode buckets;
8. every nonzero constant recurrence has order at least that bucket count;
9. distinct nonnegative real modes preserve full memory under every positive Adams power.

Principal declarations:

- `witt_formation_conservation`;
- `wittGhost_exterior_newton`;
- `wittGhost_reconstructs_modes`;
- `wittGhost_adams`;
- `packetMoment_bucket_eq_adamsGhost`;
- `adamsGhost_recurrence_of_bucket`;
- `adamsGhost_hankel_rank_of_bucket`;
- `adamsGhost_minimal_recurrence_order`;
- `positiveReal_adamsGhost_hankel_rank`.

## Exact boundary

Lean certifies finite formation/ghost/exterior fusion and the fourth-organ memory theorem. It does
not construct an infinite completed Witt source, a singular source admission theorem, a
reflection-marked Euler--Gamma realization, a hypertranscendence theorem, or any RH selection
statement. Those remain outside the proved surface.

Generic finite packet recurrence and Hankel factorization are reused from existing corpus modules.
The certified fused delta is their exact Adams collision specialization together with formation
conservation and first-`r` ghost reconstruction.

## Verification

- direct command:
  `lake env lean GaloisForLFunctions/HTGeometry/WittFormationMechanics.lean`;
- compiled leaf audit:
  `lake build GaloisForLFunctions.HTGeometry.WittFormationMechanics`;
- final umbrella audit:
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` (passes, 11,626 jobs);
- axiom audit targets conservation, reconstruction, recurrence, exact Hankel rank, minimal
  recurrence order, and positive-real rank; each reports only `propext`, `Classical.choice`, and
  `Quot.sound`;
- no `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, or computation certificate occurs in
  the module.

## Log

- 2026-08-11 — finite fusion, conservation, reconstruction, Adams aggregation, exact memory rank,
  recurrence minimality, and positive-real chamber elaborated and compiled in Lean.
