# FZZ parity quadratic eigenphase completion

- **ID:** HC24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** FZZ-P
- **Date:** 2026-08-28
- **Statement:** Four quadratic interaction channels of the literal conjugate FZZ source eigenlines cover every unit complex phase; divisor completeness for those channels is equivalent to RH.

## Goal

Solve F13's demanded positive survivor: construct a genuinely nonlinear source sector that reaches
the right-half phases unavailable to the literal linear eigenpair, then state the exact remaining
divisor-landing burden without fitting a source to a zero.

## Result

Let `y(beta)` be the balanced positive-imaginary literal source eigenline. HC24 defines four
quadratic, source-derived channels:

- `positiveSquare = y(beta)^2`;
- `conjugateSquare = star(y(beta))^2`;
- `product = y(beta) * star(y(beta)) = 1`;
- `negativeProduct = -(y(beta) * star(y(beta))) = -1`.

It proves:

1. every unit complex phase equals one channel at some `beta>0`;
2. every channel has norm one;
3. equality of a centered dyadic Mellin character with any channel forces `Re rho=1/2`;
4. every critical-line dyadic Mellin character has an exact channel realization;
5. local channel realizability is equivalent to critical-line placement;
6. quadratic channel completeness for every open-strip zeta zero is equivalent to RH.

This is the exact kinematic completion missing from F13. Degree one is cofinally incomplete;
degree two has full unit-circle phase capacity.

## Proof certificate

For non-real unit `z`, an explicit algebraic square root is placed in the strict upper-left
quadrant. HC23 realizes that root as `y(beta)`. Squaring realizes the lower semicircle; squaring its
conjugate realizes the upper semicircle. The two real boundary phases are the normalized product
and its negative. Unit norm follows from HC23's source normalization and multiplicativity.

The dyadic Mellin character has norm `2^(1/2-Re rho)`. Since every quadratic channel has norm one,
channel equality forces `Re rho=1/2`. Conversely the critical line gives unit norm, and phase
surjectivity supplies an exact channel. Quantifying this local equivalence over all open-strip zeta
zeros gives the global RH equivalence.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityQuadraticEigenphaseCompletion.lean`.

Main declarations:

- `FZZCigarParityQuadraticEigenphaseChannel`
- `fzzCigarParityQuadraticEigenphase`
- `exists_pos_fzzCigarParityQuadraticEigenphase_eq_of_norm_one`
- `norm_fzzCigarParityQuadraticEigenphase`
- `fzzCigarParityDyadicMellinCharacter_eq_quadraticEigenphase_forces_critical`
- `exists_pos_fzzCigarParityQuadraticEigenphase_eq_dyadicMellinCharacter_iff`
- `FZZCigarParityQuadraticEigenphaseDivisorComplete`
- `fzzCigarParityQuadraticEigenphaseDivisorComplete_iff_rh`

Verification: direct `lake env lean` passed; target-only `lake build
GaloisForLFunctions.RHTower.FZZCigarParityQuadraticEigenphaseCompletion` passed (9761 jobs);
all eleven audited endpoints report only `[propext, Classical.choice, Quot.sound]`.

## Literature and corpus novelty audit

Mandatory corpus searches covered FZZ/GFZZ nonlinear interactions, quadratic phases, parity/Krein
source sectors, and divisor incidence. No prior corpus theorem supplies full unit-circle phase
capacity from the literal FZZ source or identifies its divisor-completeness condition with RH.

Primary-source searches checked Ikhlef--Jacobsen--Saleur (arXiv:1109.1119) and
Jafferis--Schneider (arXiv:2004.05223) for cigar reflection/density structure, together with the
Krein/pseudo-Hermitian sources Mostafazadeh (arXiv:quant-ph/0606173),
Blasi--Scolarici--Solombrino (arXiv:quant-ph/0310106), and Feinberg--Riser
(arXiv:2109.09221). Within those searched sources, no theorem constructs these four
coefficient-faithful quadratic FZZ eigenphase channels, proves exact unit-circle surjectivity, or
gives the stated RH endpoint. Novelty claim is bounded to corpus plus these searches as of
2026-08-28.

## Gates

- [x] 0 -> 1: corpus-derived nonlinear survivor, no divisor specialization
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: unconditional Lean theorem, target build, axiom audit
- [ ] 3 -> 4: standalone publication draft

## Remaining burden

HC24 closes phase capacity, not source dynamics. Remaining open core is a literal FZZ interaction
or evolution law, fixed independently of zeta zeros, that forces each divisor mode into its
quadratic channel. The global quantified landing law is exactly RH-equivalent; assuming it would be
circular. Next conjectures must derive a source-first invariant, transfer law, or spectral
selection mechanism rather than choose `beta` and channel from the target divisor.

## Log

- 2026-08-28 — conjectured from F13 obstruction and HC23 exact quadrant image
- 2026-08-28 — paper proof closed by algebraic square-root quadrant reduction
- 2026-08-28 — formalized, wired, target-built, and axiom-audited
