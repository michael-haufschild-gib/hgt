# Deninger ordinary-integer BV Green--Stokes radial comparison

- **Paper:** [deninger-ordinary-integer-bv-green-stokes-radial-comparison.md](new_scientific_knowledge/deninger/deninger-ordinary-integer-bv-green-stokes-radial-comparison.md)
- **Lean module:** `GaloisForLFunctions.RHTower.Deninger.DeningerOrdinaryIntegerBVGreenStokesRadialComparison`
- **Status:** formalized unconditionally
- **Scope:** exact boundary-evaluation comparison and critical-line classification; no physical
  Stokes annihilation or RH claim

## Formalized statements

- positive-integer sequence carrier, ordinary Wold shift and backward map;
- reciprocal Green multiplier and ordinary divisibility projection;
- exact identities `S_n^* S_n = 1`, `S_n S_n^* = P_n`, and
  `S_n^* Q S_n = n^-1 Q`;
- operator Green--Stokes relation
  `B_n = [S_n^*, Q S_n] = n^-1 Q - P_n Q`;
- literal realization of `B_n` as Hochschild boundary
  `b(S_n^* tensor Q S_n)`;
- normalized physical conormal evaluation of the ordinary-integer BV boundary;
- reflection law for that evaluation;
- reflected difference equals Deninger tensor-square radial mate curvature;
- actual multiplicity-exact Burnol conormal radial defect equals index times reflected BV
  Green--Stokes evaluation;
- physical conormal evaluation kills this boundary exactly on the critical line.

Operator identity and its Hochschild primitive are formalized on the algebraic positive-integer
sequence carrier; scalar comparison then identifies its physical coefficient. Module deliberately
does not package physical conormal marginal as cyclic trace, since that descent is exact
RH-bearing open core.
