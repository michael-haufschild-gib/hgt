# Broadcast--clone fracture, recovery isometry, and cofinal properness — Lean certificate

- **ID:** ULF-FCM-1-LEAN
- **Stage:** 3-formalized
- **Paper parent:**
  `broadcast-clone-fracture-recovery-isometry-and-cofinal-properness-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.FormationCloneRigidityLaw`,
  `GaloisForLFunctions.HTGeometry.FormationCloneRigidityCompletion`
- **Status:** `[LEAN-CERTIFIED FULL SURFACE] [NO SORRY] [NO ADMIT] [NO AXIOM]`
  `[NO OPAQUE] [NO UNSAFE] [UMBRELLA WIRED] [NO OPEN PAPER CLAUSE]`

## Certified theorem surface

Lean certifies every dependency-closed theorem and corollary on the paper card:

1. affinity nonnegativity, the probability upper bound, and exact endpoint characterizations;
2. Euclidean root-Hellinger distance, its triangle inequality and affinity formula;
3. Markov data processing for affinity and Hellinger distance;
4. arbitrary-depth product mass and affinity multiplicativity;
5. exact lower clone-defect wall and its strict positivity in the overlapping nonidentical chamber;
6. full exact common-cloner existence iff classification, with explicit identical and singular
   constructions;
7. cofinal properness for every unbounded depth sequence with vanishing total Hellinger error;
8. common split-recovery affinity and root-Hellinger isometry;
9. deterministic diagonal broadcast, every coordinate marginal, Dirac iff independent formation,
   and exact Rényi-entropy fracture;
10. reflection/reindex equivariance for packets, products, diagonal broadcast, affinity, and
    Hellinger distance;
11. reflected-family selection under both nonsingularity and literal common-positive support.

Capstones include:

- `finiteFormationClone_exists_iff`;
- `finiteFormationHellinger_cloneDefect_lowerBound`;
- `finiteFormationClone_cofinalProperness`;
- `finiteFormationHellinger_splitRecovery`;
- `finiteFormationAffinity_diagonalPower_eq_exp_renyi`;
- `finiteDiagonalPower_eq_independentPower_iff_dirac`;
- `finiteFormationClone_reflectedSelection_of_commonPositive`.

## Verification

Direct leaf checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/FormationCloneRigidityCompletion.lean
exit 0
```

Final targeted build:

```text
lake build GaloisForLFunctions.HTGeometry.FormationCloneRigidityCompletion
Built GaloisForLFunctions.HTGeometry.FormationCloneRigidityCompletion
Build completed successfully (8657 jobs).
```

Kernel axiom audit of all listed capstones:

```text
[propext, Classical.choice, Quot.sound]
```

The completion module contains no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `decide`,
`native_decide`, or computational proof shortcut.  It is imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Boundary

The formal theorem remains exactly the finite Markov law proved on paper.  It does not assert the
paper card's explicitly excluded arithmetic producer: no pre-zero source cloner is assumed or
constructed, and no RH endpoint is encoded.
