# FZZ parity Krein grade-crossing orientation

## Status

Formalized in Lean. Conjecture loop F6 succeeded. Finite source-level orientation extracted;
full interacting FZZ/GFZZ lift remains open.

## New source law

Let `P(t)=1/(exp(t)+1)` be the literal parity-subtracted FZZ delay source and form its two-scale
Hankel block from

`p=P(1), q=P(2), r=P(4)`.

The preceding no-go theorem constructs the canonical source-Krein-self-adjoint operator with
positive-imaginary eigenvalue `lambda` and neutral eigenvector

`v+ = (q, lambda-p)`.

Define the natural scale grade by `D(u₁,u₂)=(0,u₂)` and its crossing form by
`C(u)=B(u,Du)`, where `B` is the literal FZZ two-scale Hermitian pairing. Then Lean proves the exact
coefficient-faithful law

`C(v+) = q^2 * lambda`.

Consequently `Im C(v+)>0` and `C(v+) != 0`. For the conjugate eigenmode
`v-=(q, star lambda-p)`, Lean proves

`C(v-) = -C(v+)` and `Im C(v-)<0`.

Thus neutral Krein norm does not erase all source orientation: the natural multiplicative-scale
grade canonically distinguishes the conjugate nonreal pair before any Xi divisor specialization.

## Main result and significance

The two-scale FZZ block is indefinite and its canonical source-Krein-self-adjoint operator has
nonreal neutral eigenmodes, so ordinary positivity and fixed Krein self-adjointness cannot establish
spectral reality. This theorem identifies the exact positive survivor of those obstructions: a
transverse, oppositely oriented grade crossing on the two neutral eigenlines.

This closes the finite coefficient-level question of whether a source-native orientation remains.
It does not prove RH. Remaining burden is substantially sharper:

- construct the corresponding grade and crossing form for the full interacting FZZ/GFZZ response;
- prove every parity-Mellin divisor mode lands in one globally fixed physical crossing chamber;
- derive critical-line confinement from that chamber law without assuming divisor geometry.

## Lean artifact

Module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityKreinGradeCrossingOrientation.lean`.

Key declarations:

- `fzzCigarParityTwoScaleGrade`
- `fzzCigarParityTwoScaleGradeCrossing`
- `fzzCigarParityTwoScaleKreinEigenvector_gradeCrossing`
- `fzzCigarParityTwoScaleKreinEigenvector_gradeCrossing_im_pos`
- `fzzCigarParityTwoScaleConjugateKreinEigenvector_gradeCrossing`
- `fzzCigarParityTwoScaleKrein_conjugatePair_gradeCrossing_oriented`

## Corpus basis and novelty audit

- `FZZCigarParityTwoScaleKreinSelfAdjointNoGo` supplies the literal indefinite source pairing,
  canonical Krein-self-adjoint operator, nonreal eigenpair, and neutral eigenvectors.
- `FiniteHankelBoundaryKreinCrossing` identifies a grade crossing as the orientation surviving on a
  null cone, but does not contain this FZZ source or coefficient law.
- `BlackHoleTemperatureUniversalKreinSign` shows that a source-controlled scale family can select
  an axis while fixed-temperature data cannot, but does not derive this two-scale FZZ crossing.
- Corpus searches found no prior exact identity `C(v+)=P(2)^2 lambda` or conjugate-pair
  orientation theorem for the parity FZZ source.

Novel contribution is the exact source-coefficient crossing invariant and its strict conjugate-pair
orientation. General Krein-signature and Hamiltonian-Hopf principles are not claimed as novel.

## Literature audit (27 August 2026)

- Morrison–Hagstrom, *Continuum Hamiltonian Hopf Bifurcation I*, arXiv:1308.3807, develops
  signatures for continuous Hamiltonian spectra, not the FZZ parity source or this crossing
  coefficient: https://arxiv.org/abs/1308.3807
- Hagstrom–Morrison, *Continuum Hamiltonian Hopf Bifurcation II*, arXiv:1308.6161, proves
  Krein-like signature and bifurcation theorems, but not this FZZ normal form:
  https://arxiv.org/abs/1308.6161
- Creutzig–Hikida, *Higher rank FZZ-dualities*, arXiv:2010.14681, derives interacting FZZ-type
  dualities but supplies no Krein crossing or RH-Mellin chamber law:
  https://arxiv.org/abs/2010.14681
- Targeted searches found no primary source combining a parity-subtracted FZZ delay kernel with a
  source-Krein grade crossing. Absence claim is bounded by searched sources.

## Verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityKreinGradeCrossingOrientation.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParityKreinGradeCrossingOrientation`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Wired into `GaloisForLFunctions.RHTower` umbrella.
- Global lint reports no error in this module; failures are unrelated concurrently owned
  unreachable modules.
