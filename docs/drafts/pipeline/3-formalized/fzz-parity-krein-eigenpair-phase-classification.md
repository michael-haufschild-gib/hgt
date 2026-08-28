# FZZ parity Krein eigenpair phase classification

## Status

Formalized in Lean. Conjecture F12-A and its conjugate-pair strengthening are proved
unconditionally.

## Theorem

For every physical scale `beta>0`, the balanced coordinate `y_beta` of the
positive-imaginary literal FZZ source eigenline has

`Re y_beta < 0`, `Im y_beta > 0`, and `pi/2 < arg(y_beta) < pi`.

Every critical logarithmic lift of this coordinate therefore has ordinate in the exact open
quarter-period window

`(2*pi*k + pi/2, 2*pi*k + pi) / log 2`, `k in Z`.

Conversely, on `Re rho=1/2`, equality between the centered dyadic Mellin character and `y_beta`
holds if and only if the ordinate has the exact integer-lift form

`Im rho = (arg(y_beta) + 2*pi*k) / log 2`.

The balanced coordinate of the negative-imaginary source eigenline is exactly `conjugate(y_beta)`
and its principal phase lies in `(-pi,-pi/2)`. Thus the full literal Krein eigenpair occupies only
the two strict left-half quarters of every dyadic Mellin phase period.

## New knowledge

F11's source-native critical mode is phase-rigid. Varying physical scale does not free its dyadic
Mellin phase: one orientation remains in the upper-left quadrant and its conjugate remains in the
lower-left quadrant. The exact critical-line fibre theorem rules out hidden logarithm branches as
a source of missing modes.

Lean modules:

- `formal/GaloisForLFunctions/RHTower/FZZCigarParityKreinEigenlinePhaseWindow.lean`
- `formal/GaloisForLFunctions/RHTower/FZZCigarParityKreinEigenpairCofinalEscape.lean`

Key declarations:

- `fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg`
- `fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im_pos`
- `fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_im_window`
- `fzzCigarParityDyadicMellinCharacter_eq_eigenline_iff_lift_ordinate`
- `fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate_eq_star`
- `fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate_arg_window`

## Corpus audit

- F7 supplies the exact all-scale conjugate Krein eigenvectors.
- F10 supplies the balanced Mellin coordinate.
- F11 supplies the unit positive-eigenline coordinate and principal critical Mellin parameter.
- Fresh `formal_tools.py research` searches found no existing source-phase quadrant theorem, full
  logarithmic-fibre classification, or conjugate-pair phase classification for these objects.

## Literature audit (28 August 2026)

- Blasi–Scolarici–Solombrino, *Pseudo-Hermitian Hamiltonians, indefinite inner product spaces and
  their symmetries*, arXiv:quant-ph/0310106, gives abstract pseudo-unitary and pseudo-antiunitary
  symmetry structure but no FZZ/Fermi balanced Mellin phase classification:
  https://arxiv.org/abs/quant-ph/0310106
- Jafferis–Schneider, *Semi-Classical Analysis of the String Theory Cigar*, arXiv:2004.05223,
  analyzes cigar reflection amplitudes and complex saddles but not this coefficient-faithful
  two-scale Krein eigenpair or its dyadic Mellin fibres: https://arxiv.org/abs/2004.05223
- Takook, *Krein Space Quantization and a Spectral Interpretation of the Riemann ξ-Function*,
  arXiv:2606.13932, develops a recent Krein-space critical-line framework but does not contain the
  FZZ phase-window or fibre theorem: https://arxiv.org/abs/2606.13932
- Targeted searches found no exact synthesis. Absence claim is bounded by searched primary-source
  corpus.

Novelty verdict: exact coefficient-faithful FZZ eigenpair phase image and logarithmic-fibre
classification appear corpus-new and literature-unlocated.

## Lean verification

- Direct checks passed with `lake env lean <file>` for both modules.
- Targeted builds passed for
  `GaloisForLFunctions.RHTower.FZZCigarParityKreinEigenlinePhaseWindow` and
  `GaloisForLFunctions.RHTower.FZZCigarParityKreinEigenpairCofinalEscape`.
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Both modules are wired into `GaloisForLFunctions.RHTower` umbrella.
- Authoritative global lint reports no error in either module; current errors are unrelated
  pre-existing unreachable-module entries.

## Consequence

The exact phase classification is the positive survivor of the failed literal-eigenpair divisor
route. Any replacement must add source directions whose balanced phases reach the missing right
half-circle; changing scale or logarithm branch cannot do so.
