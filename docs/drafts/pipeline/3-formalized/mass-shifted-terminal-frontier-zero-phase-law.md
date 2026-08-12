# Mass-shifted terminal-frontier zero phase law

- **ID:** mass-shifted-terminal-frontier-zero-phase-law
- **Stage:** 3-formalized
- **Type:** STRICT SHIFTED MOMENT POSITIVITY + EXACT FRONTIER RH PHASE
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3

## Conjecture loop

1. **C1 — RH gives only positive semidefinite shifted blocks.** **FAILED.** Under RH every shifted
   reciprocal atom is positive real.  The occupied reciprocal-square support is infinite, and the
   positive-mass Möbius translation is injective on it.  A nonzero finite polynomial therefore
   misses at least one translated atom, making its shifted Hankel energy strictly positive.
2. **C2 — terminal frontier may retain positive mass under RH because failure uses non-PD rather
   than non-PSD.** **FAILED if C1 closes.** Strict positivity empties every failure set, whose real
   supremum is exactly zero.
3. **C3 — zero terminal frontiers may still coexist with false RH.** **FAILED.** Existing false-RH
   curvature renewal produces occupied terminal frontiers above every real threshold, hence in
   particular a positive frontier.

## Target

Proved unconditionally in Lean:

\[
 \mathrm{RH}\iff \forall n,\ \tau_n=0,
\]

where `τ_n` is the canonical terminal frontier of degree-`n+2` shifted-Xi positive-definite
failure.  This is a classification theorem, not an RH proof: open burden remains excluding the
positive cofinal frontier phase without assuming RH.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/XiShiftedTerminalFrontierZeroPhaseLaw.lean`

Capstones:

- `xiZeroCopyReciprocalSquare_range_infinite`;
- `xiShiftedReciprocalSquare_eq_iff`;
- `xiShiftedReciprocalSquare_range_infinite`;
- `exists_xiShiftedReciprocalSquare_not_root_of_polynomial`;
- `xiShiftedReciprocalHankelQuadratic_pos_of_riemannHypothesis`;
- `xiShiftedMomentHankelMatrix_posDef_of_riemannHypothesis`;
- `xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis`;
- `xiShiftedHigherBlockTerminalFrontier_eq_zero_of_riemannHypothesis`;
- `riemannHypothesis_iff_forall_xiShiftedHigherBlockTerminalFrontier_eq_zero`.

Direct `lake env lean` passes warning-free.  Targeted module `lake build` passes.  `#print axioms`
reports only `propext`, `Classical.choice`, and `Quot.sound` for strict energy, strict matrix
positivity, and the exact RH phase equivalence.
