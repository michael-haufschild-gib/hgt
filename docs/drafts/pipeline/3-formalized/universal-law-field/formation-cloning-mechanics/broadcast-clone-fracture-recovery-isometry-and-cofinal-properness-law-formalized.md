# Broadcast--clone fracture and recovery isometry -- formalized core

- **ID:** ULF-FCM-1-LEAN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper parent:**
  `../../../2-fully-proven/universal-law-field/formation-cloning-mechanics/broadcast-clone-fracture-recovery-isometry-and-cofinal-properness-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.FormationCloneRigidityLaw`
- **Status:** `[LEAN-CERTIFIED CORE] [NO SORRY] [NO ADMIT] [NO AXIOM]`
  `[UMBRELLA WIRED] [PAPER COFINAL METRIC EXTENSION OPEN]`

## Certified theorem surface

The module proves:

1. `finiteFormationAffinity_nonneg`;
2. `finiteFormationAffinity_le_one` for normalized nonnegative packets;
3. `finiteFormationAffinity_markovDataProcessing` for the existing
   `FiniteMarkovKernel` structure;
4. `finiteFormationAffinity_independentPair`, the exact tensor-square law;
5. `finiteFormationAffinity_splitRecovery`, exact information neutrality of a common recovery
   row;
6. `finiteFormationClone_affinity_extreme`, forcing affinity `0` or `1` under one common exact
   independent cloner;
7. `no_finiteFormationClone_of_interiorAffinity`, excluding every such cloner when affinity lies
   strictly between the two extremes.

The main proof is not an encoded scalar lemma.  It formalizes the full finite Markov mechanism:
fibrewise square-root Cauchy--Schwarz, Markov mass conservation, tensor-product factorization, and
the final extreme-point rigidity argument.

## Verification

Direct source check:

```text
lake env lean GaloisForLFunctions/HTGeometry/FormationCloneRigidityLaw.lean
exit 0
```

Final module build:

```text
lake build GaloisForLFunctions.HTGeometry.FormationCloneRigidityLaw
Built GaloisForLFunctions.HTGeometry.FormationCloneRigidityLaw
```

Umbrella audit:

```text
lake build GaloisForLFunctions.HTGeometry
Built GaloisForLFunctions.HTGeometry
Build completed successfully (18293 jobs).
```

Axiom audit through a temporary import file reports only:

```text
[propext, Classical.choice, Quot.sound]
```

Project lint finds no defect in this module.  The repository-wide lint currently fails on unrelated
unreachable modules already present in the shared dirty worktree; the new module is reachable from
`GaloisForLFunctions.HTGeometry` and is absent from that failure list.

## Exact formal boundary

The paper's quantitative approximate-cloning bound and cofinal limit use the triangle inequality
for Hellinger distance across changing product spaces.  Those clauses remain paper-proved.  They
are not hidden as assumptions in Lean and are not counted as formalized here.
