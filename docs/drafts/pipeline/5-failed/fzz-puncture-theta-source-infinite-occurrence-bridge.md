# FZZ puncture–theta-source infinite-occurrence bridge

## Status

Route F1 retired as a circular cross-route interface. Strongest positive survivor is formalized in
Lean.

## Attempted conjecture F1

For a puncture Mellin spectral point `ρ`, set `z(ρ) = (ρ - 1/2)(-i)`. Conjecture that nontrivial
zeros of the exact FZZ continuum Mellin divisor are exactly noninvertibility occurrences of the
fixed theta-source pencil `I + z(ρ)B`, that every occurrence supplies a nonzero theta-source
eigenvector, and that real occurrence coordinates are exactly real-energy horizon-dilation modes.

## Proof outcome

All mathematical clauses hold unconditionally:

- `Re z(ρ) = Im ρ` and `Im z(ρ) = 1/2 - Re ρ`;
- `z(ρ)=E∈ℝ` exactly when `ρ=1/2+iE`;
- source-pencil occurrence exactly equals `xi ρ = 0`, hence exactly a nontrivial zero of the
  FZZ-labelled Mellin divisor;
- every occurrence supplies a nonzero vector of the fixed theta-source Hilbert space with
  eigenvalue `-z(ρ)⁻¹`;
- a real FZZ-labelled horizon mode at energy `E` is exactly noninvertibility of the fixed
  theta-source Fredholm pencil at `E`;
- FZZ-labelled dilation completeness is equivalent both to reality of every occurrence coordinate
  and to reality of the fixed theta-source operator's nonzero spectrum.

## Why route fails

`fzzCigarContinuumMellinDivisor` is definitionally `riemannZeta`. Therefore the exact bridge imports
the completed divisor before the theta-source pencil is consulted. It does not construct a complex
cigar continuation or prove its divisor comparison from literal FZZ/GFZZ coefficients. The final
reality condition remains exactly RH-strength.

This closes the tempting “use an existing infinite determinant as the missing FZZ occurrence”
shortcut. Infinite dimensionality is genuine, but source provenance is wrong for an independent
FZZ producer.

## Positive survivor

The affine rotation gives a dependency-closed compatibility law between two separately formalized
RH interfaces. Unlike finite FZZ polynomial pencils, the fixed theta-source pencil carries every
nontrivial completed zero with an actual eigenvector and agrees exactly with the real-energy mode
equation on the critical line. This is useful as a target specification for any future literal
FZZ/GFZZ operator: it must reproduce this pencil divisor or an independently proved equivalent,
without defining its complex divisor to be zeta.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarPunctureThetaSourceInfiniteOccurrenceBridge.lean`.

Key declarations:

- `fzzPunctureThetaSourceOccurrence_iff_nontrivialMellinZero`
- `exists_thetaSource_eigenvector_of_fzzPunctureOccurrence`
- `fzzPunctureHorizonDilationMode_iff_thetaSourcePencil_not_isUnit`
- `fzzPunctureHorizonDilationComplete_iff_thetaSourceCoordinateReal`
- `fzzPunctureHorizonDilationComplete_iff_thetaKernelOperator_nonzero_spectrum_real`

## Corpus audit

- `FZZCigarScatteringSpectralAsymmetry` proves only the positive-real Mellin identity obtained from
  the exact reflection-delay/Bose kernel.
- `FZZCigarPunctureDilationCompletenessEndpoint` labels `riemannZeta` as the continued divisor and is
  already classified in `docs/reports/endpoints.md` as circular.
- `FZZCigarProtectedDelayPointModeNoGo` excludes the literal scalar protected-delay point mode.
- finite bare, affine, polynomial, and incidence FZZ pencil modules exclude fixed finite regular
  substitutes.
- `HedenmalmThetaSourceCompressedInverseDeterminant` supplies the actual infinite-dimensional
  source pencil, but from the Jacobi-theta route rather than FZZ dynamics.

## Literature audit (27 August 2026)

- Ashok–Troost, *A Twisted Non-compact Elliptic Genus*, arXiv:1101.1059, derives continuum spectral
  asymmetry from exact cigar reflection amplitudes. It does not construct the FZZ-to-Hedenmalm
  compact pencil or the above cross-route compatibility law:
  https://arxiv.org/abs/1101.1059
- Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494, constructs a
  theta-based differential-pair eigenvalue problem and explicitly leaves the inner-product/
  self-adjointness mechanism open. It does not derive its source from FZZ cigar reflection data:
  https://arxiv.org/abs/2606.17494
- Targeted searches found no primary source deriving a Fredholm/Hedenmalm operator from the FZZ
  cigar continuum delay. Absence claim remains bounded by the searched arXiv corpus.

Novelty verdict: exact Lean cross-route bridge appears corpus-new and literature-unlocated, but it
is **not a significant RH advance** because the FZZ complex divisor was imported definitionally.

## Lean verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarPunctureThetaSourceInfiniteOccurrenceBridge.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarPunctureThetaSourceInfiniteOccurrenceBridge`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Module is wired into `GaloisForLFunctions.RHTower` umbrella.
- Global lint has no error in this module; current failures are unrelated concurrently owned
  unreachable-module entries.

## Surviving open core

Construct a complex continuation and occurrence operator from literal FZZ/GFZZ source data, then
prove its divisor comparison without defining the object in terms of `riemannZeta`, `xi`, `XiC`,
or an enumerated zero set. After that, prove the resulting orientation/spectral-reality law.
