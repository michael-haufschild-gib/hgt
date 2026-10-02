# Gram-spectral cutoffs cannot recover the literal Burnol cubic charge

- **ID:** TG-C3-GRAM-CUTOFF
- **Stage:** 5-failed
- **Type:** FALSIFIED candidate; THEOREM (Lean) positive survivor
- **Source:** `../1-in-progress/tg-source-conjecture-loop-2026-10-01.md`

## Candidate and exact obstruction

Candidate: replace the known diagonal prime-depth masks by spectral cutoffs of the
complete Burnol Gram, hoping their failure to commute with the theta frame creates
nonzero ordinary cubic charge.

`RHTower.primeBurnolTheta_primeMatrix_trace_eq_zero` proves the complete source trace
`Tr((W tensor I_2)cC)=0` for every prime-depth matrix W. No commutation with the Gram or
frame is required. Spectral cutoffs are included. This retires this candidate, not TG.

## Strongest positive survivor

Every complete prime-depth block of cC is exactly `[[A,B],[B,-A]]`. The two matrices A,B
reconstruct the entire current, and every reporter has an exact pairing with these two
channels. See `../3-formalized/tg-burnol-theta-quarter-turn-cancellation.md` for the full
paper proof, exact declarations, and successful direct Lean/axiom audits.

**New insight:** prime mixing alone does not evade the cancellation. The common theta
quarter-turn symmetry survives arbitrary mixing of prime-depth labels. A continuing
construction must retain theta-sensitive channels or justify a source change breaking
that symmetry; index identification and the arithmetic sub-unit bound remain open.
