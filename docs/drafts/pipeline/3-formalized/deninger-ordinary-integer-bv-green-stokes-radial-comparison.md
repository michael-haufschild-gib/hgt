# Deninger ordinary-integer BV Green--Stokes radial comparison

- **Paper:** [deninger-ordinary-integer-bv-green-stokes-radial-comparison.md](../2-fully-proven/new_scientific_knowledge/deninger/deninger-ordinary-integer-bv-green-stokes-radial-comparison.md)
- **Lean module:** `GaloisForLFunctions.RHTower.DeningerOrdinaryIntegerBVGreenStokesRadialComparison`
- **Status:** formalized unconditionally
- **Scope:** exact boundary-evaluation comparison and critical-line classification; no physical
  Stokes annihilation or RH claim

## Formalized statements

- normalized physical conormal evaluation of the ordinary-integer BV boundary;
- reflection law for that evaluation;
- reflected difference equals Deninger tensor-square radial mate curvature;
- actual multiplicity-exact Burnol conormal radial defect equals index times reflected BV
  Green--Stokes evaluation;
- physical conormal evaluation kills this boundary exactly on the critical line.

Operator identity B_n = [S_n^*, Q S_n] = n^-1 Q - P_n Q = b(S_n^* tensor Q S_n)
uses parent Wold/Hochschild infrastructure already proved on paper; this module formalizes new
Route-L scalar comparison to existing physical coefficient. It deliberately does not package
physical conormal marginal as cyclic trace, since that descent is exact RH-bearing open core.
