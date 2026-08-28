# FZZ parity Krein antiunitary critical eigenline

## Status

Formalized in Lean. Conjecture F11 proved unconditionally.

## Theorem

For every physical scale `beta>0`, the canonical FZZ parity source-Krein operator `A_beta` and the
canonical source-metric antiunitary `J_beta` satisfy

`A_beta J_beta = -J_beta A_beta`.

The positive-imaginary source eigenvalue obeys `-conjugate(lambda_beta)=lambda_beta`; consequently
the reflected eigenvector is again a `lambda_beta` eigenvector. More strongly, its eigenline is
projectively fixed by `J_beta`.

In the F10 half-density coordinate, the eigenline has the explicit ratio

`y_beta = a_beta (lambda_beta-p_beta)/q_beta`,

where `a_beta=sqrt(r_beta/p_beta)`, and Lean proves the exact identity

`|y_beta|=1`.

Define

`rho_beta = 1/2 + i arg(y_beta)/log 2`.

Then `Re rho_beta=1/2`, its centered dyadic Mellin character is exactly `y_beta`, and the original
source eigenvector factors as

`v_beta = q_beta w_beta(rho_beta)`

for F10's balanced carrier. Its balanced reflected grade crossings therefore agree
unconditionally.

## New knowledge

Literal FZZ parity source coefficients now generate, at every positive scale, an explicit
source-native dynamical eigenmode lying exactly on the centered critical Mellin wall. This is not a
critical-line parameter inserted by hand: unit modulus follows algebraically from the negative
Fermi-Hankel determinant, the Krein discriminant, and the forced source half-density.

The result closes existence and orientation of one canonical critical mode per scale. It does not
prove RH because no theorem yet identifies every parity-Mellin divisor zero with this scale family.
The remaining burden is a precise divisor-incidence/surjectivity theorem.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityKreinAntiunitaryCriticalEigenline.lean`.

Key declarations:

- `fzzCigarParityDilatedKreinOperator_sourceMetricReflection_anticommute`
- `fzzCigarParityDilatedKreinEigenlineBalancedCoordinate`
- `norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate`
- `fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter`
- `fzzCigarParityDyadicMellinCharacter_eigenlineCriticalParameter`
- `fzzCigarParityDilatedKreinEigenvector_eq_balancedCriticalMellinCarrier`
- `fzzCigarParitySourceMetricReflection_kreinEigenvector_projectivelyFixed`
- `fzzCigarParityDilatedKreinOperator_reflectedEigenpair`
- `fzzCigarParityDilatedKreinEigenline_balancedCrossing_eq_reflection`

## Corpus audit

- F7 supplied the all-scale source-Krein eigenpair and oriented grade crossing.
- F9 supplied the source-metric antiunitary.
- F10 supplied the balanced Mellin carrier and exact critical-line crossing detector.
- Fresh searches found no existing anticommutation, unimodular eigenline-coordinate theorem, or
  exact critical Mellin factorization for these FZZ source objects.

## Literature audit (28 August 2026)

- Blasi–Scolarici–Solombrino, *Pseudo-Hermitian Hamiltonians, indefinite inner product spaces and
  their symmetries*, arXiv:quant-ph/0310106, classifies pseudo-unitary and pseudo-antiunitary
  symmetries abstractly. It contains no FZZ/Fermi source matrix, Mellin half-density, or critical
  eigenline factorization: https://arxiv.org/abs/quant-ph/0310106
- Scolarici–Solombrino, *On the pseudo-Hermitian nondiagonalizable Hamiltonians*,
  arXiv:quant-ph/0211161, relates pseudo-Hermiticity to antilinear symmetry and spectral pairing,
  but does not derive this anticommuting source model or its unit Mellin coordinate:
  https://arxiv.org/abs/quant-ph/0211161
- Jafferis–Schneider, *Semi-Classical Analysis of the String Theory Cigar*, arXiv:2004.05223,
  derives cigar reflection data from complex saddles, but no Krein antiunitary critical eigenline:
  https://arxiv.org/abs/2004.05223
- Takook, *Krein Space Quantization and a Spectral Interpretation of the Riemann ξ-Function*,
  arXiv:2606.13932, supplies a recent Krein-space ξ framework restricted to the critical line, but
  not this literal FZZ source construction or all-scale explicit factorization:
  https://arxiv.org/abs/2606.13932
- Targeted primary-source searches found no exact synthesis. Absence claim remains bounded by the
  searched arXiv corpus.

Novelty verdict: source-exact FZZ anticommutation, projectively fixed Krein eigenline, unit balanced
coordinate, and explicit critical Mellin carrier factorization appear corpus-new and
literature-unlocated.

## Lean verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityKreinAntiunitaryCriticalEigenline.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParityKreinAntiunitaryCriticalEigenline`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Module is wired into `GaloisForLFunctions.RHTower` umbrella.
- Authoritative global lint has no error in this module; current failures are unrelated
  concurrently owned unreachable-module entries.

## Remaining gate

Prove that the scale map `beta ↦ rho_beta` captures every open-strip parity-Mellin divisor mode, or
derive a richer infinite-dimensional FZZ operator whose critical eigenlines have the full divisor.
Any statement assuming `FZZCigarParityMellinMode rho_beta` merely restates the missing incidence and
does not close it.
