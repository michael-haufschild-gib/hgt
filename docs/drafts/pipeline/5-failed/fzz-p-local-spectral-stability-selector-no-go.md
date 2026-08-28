# FZZ-P local spectral stability as selector

- **ID:** FZZ-P-HC5-NG
- **Stage:** 5-failed
- **Type:** SHARP DYNAMICAL NO-GO WITH POSITIVE SURVIVOR
- **Route:** Use real spectrum of a finite source-native FZZ Krein interaction as the dynamical law
  selecting critical-line Mellin modes.
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityDiagonalRieszStabilization`

## Failed premise

HC4 showed formal Krein self-adjointness plus chiral interaction remains unstable.  A natural
successor is that some source-native local Hermitian interaction restores spectral reality only at
the critical-line geometry and thereby forces reflected Mellin matching.

## Exact killing theorem

At every positive scale the unit diagonal HC3 reporter has source-metric Riesz representative

`E^-1[[0,Q],[0,-P]]`.

The entirely source-defined negative coupling `gamma=-E` makes the perturbed generator satisfy

`A^2=P A`

with explicit real eigenvalues `0,P`.  This construction uses no Mellin parameter, divisor, Xi
zero, or target.  Local spectral reality is therefore available unconditionally on every source
scale and cannot select horizontal zero placement.

## Strongest positive survivor

The survivor is an exact, coefficient-faithful stabilization mechanism:

- full trace, determinant, and characteristic-discriminant laws for every real coupling;
- canonical negative source-gap coupling;
- rank-one triangular collapse and polynomial identity;
- complete real-spectrum proof with explicit eigenpairs;
- simultaneous proof that the generating diagonal energy is still an exact critical-line
  reflection detector.

Paper proof and unconditional Lean formalization are complete in
`../3-formalized/fzz-p-diagonal-riesz-stabilization.md`.

## New insight

Finite-block spectral stability and reflected-energy matching are logically different source laws.
The former can be manufactured from the local FZZ coefficients alone; the latter remains
RH-strength on parity-Mellin divisor modes.  A surviving FZZ/GFZZ dynamics must enforce
bioriented/reflected matching or introduce mode-sensitive nonlocal structure, not merely produce a
real local spectrum.

## Status

- exact no-go and positive survivor proved on paper;
- all source algebra and spectral claims formalized in Lean;
- direct Lean, targeted build, and axiom audit passed;
- literature search found no exact collision; independent priority audit remains.

## Log

- 2026-08-28 — Local spectral-stability selector retired after unconditional source-gap
  stabilization; positive survivor formalized before retirement.
