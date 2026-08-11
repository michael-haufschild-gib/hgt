# Finite coherent-history envelope, reconstruction, interference, and recurrence law — formalized

- **ID:** ULF-HIST-1
- **Stage:** 3-formalized
- **Paper source:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/coherent-history-mechanics/finite-coherent-history-envelope-reconstruction-interference-and-recurrence-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.CoherentHistoryMechanics`
- **Status:** [LEAN-PROVED CORE] [AXIOM-AUDITED] [UMBRELLA-BUILT]

## Certified statements

Lean proves:

1. total phase extraction reconstructs each complex history weight;
2. positive weights plus an anchored phase-Gram coordinate reconstruct the coherent weight up to
   the single anchor phase;
3. the exact two-history phase-dispersion identity and nonnegativity;
4. entrywise complex modulus is the unique least positive matrix majorant;
5. the matrix interference defect is entrywise nonnegative;
6. the exact three-stage associativity conservation identity;
7. the closed rational witness has coherent period two;
8. its positive history envelope expands the ray `(1,2)` by `(7/5)^n` and tends to infinity;
9. the unconditional closed capstone joins recurrence and open positive history.

## Exact formal boundary

The paper's arbitrary finite-history conditional-variance identity is not yet formalized.  Lean
certifies its two-history polar core, least-majorant theorem, full matrix composition law, and closed
fourth-organ witness.  No claim is made that the actual arithmetic source supplies the required
history presentation.

## Verification

`lake env lean GaloisForLFunctions/HTGeometry/CoherentHistoryMechanics.lean` passes.

`lake build GaloisForLFunctions.HTGeometry.UniversalLawField` passes in the foreground with
11,611 jobs.  Axiom prints for every listed theorem and the closed capstone report only `propext`,
`Classical.choice`, and `Quot.sound`.
