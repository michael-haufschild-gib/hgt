# Raw finite Witt trace realization

- **Status:** retired
- **Reason:** finite-stage Frobenius--Verschiebung trace blindness
- **Closure theorem:** `ULF-FVBLIND-1`
- **Lean:** `GaloisForLFunctions.HTGeometry.FinitePermutationFVTraceBlindness`

## It cannot be this

Analytic grade cannot be the trace or supertrace of a raw finite cyclotomic Witt stage.  Frobenius
is a basis permutation and `F V=q` gives `V=q F^{-1}`; consequently the squared supertrace is

`(1-q^2) #Fix(F^2)`,

which has no spectral-character parameter.

## Positive survivor

Finite stages still supply integral lattices, formation histories, orbit counts, and exact
Frobenius--Verschiebung relations.  Grade can occur only in the derived defect produced when those
stages are assembled by an unbounded completion.  Required object is therefore a
trace-versus-completion transgression class, not another finite-stage trace.

## Attempts ruled out

- fixed finite integral matrix with character-dependent eigenvalues;
- finite permutation Frobenius supertrace;
- normalized finite orbit trace as rapidity carrier;
- inserting character weights before integral completion.

The last move changes source category and merely assumes the analytic character it was meant to
derive.

## Log

- 2026-09-02 -- exact fixed-point formula proved on paper and in Lean; positive completion survivor
  retained.
