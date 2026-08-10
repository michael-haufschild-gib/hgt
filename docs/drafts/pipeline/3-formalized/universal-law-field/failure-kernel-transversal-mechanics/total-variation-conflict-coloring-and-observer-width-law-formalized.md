# Total-variation conflict coloring and observer-width law — formalized

- **ID:** ULF-FKT-TVCC-1
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveTVConflictColoring`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified laws

For finite deterministic observers and finite real profile systems, Lean certifies:

1. exact positive/negative Jordan masses on every observer fibre;
2. fibre overlap defect equals the minimum of positive and negative masses;
3. zero fibre defect iff no opposite-sign pair is collapsed in that fibre;
4. simultaneous preservation of every declared pairwise total variation iff observer labels form a
   proper coloring of the task-conflict relation;
5. existence of a lossless `q`-label observer iff the relation is `q`-colorable;
6. every collapsed conflict edge forces strict loss for its witnessing task;
7. every finite symmetric irreflexive relation is realized exactly by nonnegative Dirac profile
   pairs.

No `sorry`, `admit`, added axiom, `opaque`, `unsafe`, or computational proof is used.

## Audit

- direct foreground elaboration: pass;
- project formal lint: pass;
- axiom print on seven capstones: `[propext, Classical.choice, Quot.sound]` only;
- final foreground Universal Law Field umbrella build: pass, 11,516 jobs.

## Exact certification boundary

Lean certifies finite conflict width.  The paper card's infinite compactness sentence is an
application of the classical de Bruijn--Erdos theorem and is not re-formalized here.  No topology,
measurability, equivariance, completion, or cross-stage coherence structure is inferred from
colorability.

## Field meaning

Observer loss now has a typed finite resource mechanism.  Some failures are alphabet-width
failures: declared distinctions require more observer colors.  If abstract finite colorability is
uniformly bounded but an admitted global observer still fails, the remaining obstruction belongs
to a different mechanism—analytic admission or coherence.  The theorem therefore separates two
causes that route-specific no-gos repeatedly conflate.

