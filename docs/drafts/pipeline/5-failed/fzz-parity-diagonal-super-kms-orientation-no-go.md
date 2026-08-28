# FZZ parity diagonal super-KMS orientation no-go

## Status

Route F3 retired. Diagonal graded KMS/passivity does not orient the source-first FZZ parity divisor.
Strongest positive survivor is formalized in Lean.

## Attempted conjecture F3

Combine the literal FZZ parity-delay Mellin transform with the corpus's exact Born graded KMS
dilation covariance. Test whether positivity, summability, and all-dilation covariance select the
critical physical inverse temperature `β=1`, corresponding to `Re s=1/2` in the half-dilated gauge.

## Proof outcome

The selection conjecture is false, with an unconditional exact counterexample:

- real values of the source-first FZZ parity Mellin transform are exactly the real Fermi Mellin
  normalizer;
- at every `σ>0`, this actual source mass is strictly positive;
- for every `β>0`, the parity charge series is summable and every positive integer dilation obeys
  the exact graded super-KMS covariance law;
- consequently every positive `β` is diagonally admissible;
- `β=2` is an explicit admissible noncritical temperature, so diagonal admissibility cannot force
  `β=1`.

## Why route fails

All tested diagonal data are temperature-universal on the full positive half-line. Neither
positivity of the literal source mass, convergence of the graded charge trace, nor exact dilation
covariance distinguishes the half-density grade. The obstruction is structural, not a missing
estimate: the proposed selection predicate is refuted by a closed witness.

This retires any FZZ orientation argument depending only on diagonal charge weights, their positive
partition mass, and integer-dilation covariance. It does not retire off-diagonal cigar scattering,
interacting correlators, nonlinear response, singular boundary data, or reflection-coupled kernels.

## Positive survivor

The literal FZZ parity source has a temperature-universal graded KMS phase. For every positive
inverse temperature its Mellin mass is a strictly positive real normalizer and its entire tower of
integer dilations transforms by the exact character `k^(-β/2)`. This is a dependency-closed source
law, and it sharply specifies what any successful orientation mechanism must add: information that
couples distinct grades or boundary sectors rather than another diagonal equilibrium identity.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityDiagonalSuperKMSNoGo.lean`.

Key declarations:

- `fzzCigarParityMellin_ofReal_eq_fermiMellinNormalizer`
- `fzzCigarParityMellin_ofReal_pos`
- `fzzCigarParityDiagonalSuperKMSAdmissible_of_pos`
- `exists_fzzCigarParityDiagonalSuperKMSAdmissible_ne_one`
- `not_fzzCigarParityDiagonalSuperKMSSelectsCritical`

## Corpus audit

- `FZZCigarParityDelaySourceContinuation` constructs the literal parity-delay source and its
  source-first complex Mellin continuation.
- `FermiMellinObserver` proves strict positivity of the real Fermi Mellin normalizer.
- `BornEtaGrading` proves graded supertrace summability and positivity for every `β>0`.
- `BornSuperKMSCovariance` proves exact positive-integer dilation covariance for every real `β`.
- `BornDilatedGradedKMSWallUniversalityLaw` independently warns that diagonal graded phase data
  survives through a temperature strip rather than selecting one wall.

No corpus theorem previously identifies these universal KMS laws with the literal FZZ parity
source and supplies the explicit noncritical counterexample.

## Literature audit (27 August 2026)

- Ashok–Troost, *A Twisted Non-compact Elliptic Genus*, arXiv:1101.1059, derives the noncompact
  elliptic genus and interprets its non-holomorphic term through boson/fermion continuum spectral
  asymmetry. It does not connect the cigar parity source to Salem's Mellin criterion or prove the
  all-temperature diagonal no-go: https://arxiv.org/abs/1101.1059
- Hikida–Schomerus, *The FZZ-Duality Conjecture — A Proof*, arXiv:0805.3931, proves cigar–sine-
  Liouville correlator duality, including spectral-flow sectors. It does not formulate a zeta/Salem
  divisor or a KMS temperature-selection theorem: https://arxiv.org/abs/0805.3931
- González–Negrín, *A new equivalence to the Riemann Hypothesis by means of the Salem integral
  equation*, arXiv:2604.15396, gives a Salem-kernel RH equivalence but no FZZ provenance, graded
  supertrace, or KMS orientation mechanism: https://arxiv.org/abs/2604.15396
- Targeted searches found no primary source combining literal FZZ parity delay, Salem's Fermi
  Mellin transform, and a diagonal super-KMS critical-temperature selector. Absence claim remains
  bounded by the searched arXiv corpus.

Novelty verdict: exact source-level temperature-universality theorem and sharp diagonal-selection
no-go appear corpus-new and literature-unlocated. They are significant as an obstruction and
replacement law, but do not close the remaining RH orientation burden.

## Lean verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityDiagonalSuperKMSNoGo.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParityDiagonalSuperKMSNoGo`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Module is wired into `GaloisForLFunctions.RHTower` umbrella.
- Global lint has no error in this module; current failures are unrelated concurrently owned
  unreachable-module entries.

## Surviving open core

Derive a genuinely off-diagonal, interacting, nonlinear, or singular orientation law from literal
FZZ/GFZZ data. It must distinguish `β=1` using information absent from all diagonal charge weights
and their dilation covariance, then force every zero of the source-first parity Mellin continuation
onto `Re s=1/2`.
