# FZZ parity Krein eigenpair cofinal divisor escape

## Status

Route FZZ-P-F12/F13 retired. Literal all-scale two-dimensional FZZ source Krein eigenpair is
unconditionally divisor-incomplete. Exact phase/fibre survivor is formalized in Lean.

## Attempted conjecture

Use F11's source-native unit Krein eigenline, its conjugate partner, and continuous physical scale
to represent every nontrivial parity-Mellin divisor mode. Logarithmic branches were allowed, so the
claim tested the full literal eigenpair rather than only one principal parameter.

## Exact killing theorem

Let `chi(rho)=exp(log(2)*(rho-1/2))`. Lean proves:

For every real height `H`, there exists `rho` such that

- `riemannZeta rho = 0`,
- `0 < Re rho < 1`,
- `H < Im rho`, and
- for every `beta>0`, `chi(rho)` equals neither balanced member of the literal FZZ source Krein
  eigenpair.

The proof uses no RH hypothesis and no numerical zero computation. The positive source line has
phase in `(pi/2,pi)` modulo `2*pi`; its conjugate has phase in `(-pi,-pi/2)` modulo `2*pi`.
Titchmarsh's shrinking zero-gap theorem, already formalized in the corpus, places an actual zeta
zero arbitrarily high inside a fixed neighbourhood of an integer dyadic phase turn. That
neighbourhood is disjoint from both source quarter-windows. The uniform strip theorem then removes
trivial zeros, yielding an actual nontrivial open-strip zero.

Lean modules:

- `formal/GaloisForLFunctions/RHTower/FZZCigarParityKreinEigenlineCofinalEscape.lean`
- `formal/GaloisForLFunctions/RHTower/FZZCigarParityKreinEigenpairCofinalEscape.lean`

Killing declarations:

- `exists_riemannZeta_zero_not_fzzCigarParityKreinEigenline_above`
- `fzzCigarParityDyadicMellinCharacter_ne_conjugateKreinEigenline_of_near_integer_turn`
- `exists_riemannZeta_zero_not_fzzCigarParityKreinEigenpair_above`

## Why route fails

Scale dependence changes phase only inside strict left-half quadrants. Integer logarithm branches
repeat those quadrants periodically and add no new phase. Since actual zeta zeros occur cofinally
near integer phase turns, no scale assignment and no branch assignment can make the literal pair
surjective onto the divisor. This obstruction holds even if RH is true because it concerns
ordinate phase incidence, not zero real parts.

## Positive survivor

The exact phase image and exact critical-line fibre are fully classified:

- positive eigenline: `pi/2 < arg < pi`;
- conjugate eigenline: `-pi < arg < -pi/2`;
- every positive-line preimage on `Re rho=1/2` is precisely an integer logarithmic lift;
- matching either unit eigenline forces critical-line placement.

This gives a sharp replacement hypothesis: a viable FZZ operator must introduce additional source
directions covering the missing right-half dyadic phases. More scales, the conjugate eigenline, or
different logarithm branches cannot repair the literal two-dimensional block.

Positive survivor card:
`docs/drafts/pipeline/3-formalized/fzz-parity-krein-eigenpair-phase-classification.md`.

## New insight

F11 closed existence of one source-native critical mode but left divisor incidence open. The new
cofinal escape theorem closes that burden negatively for the entire literal conjugate pair, not
merely the preferred positive orientation. The next FZZ-P proof attempt must be genuinely
higher-rank or dynamically interacting; two source coordinates are terminal.

## Corpus audit

- `FZZCigarParityAllScaleKreinCrossing` supplies both exact source eigenvectors.
- `FZZCigarParityKreinAntiunitaryCriticalEigenline` supplies the positive unit coordinate.
- `FZZCigarParityKreinEigenlinePhaseWindow` supplies exact lifts and phase separation.
- `TitchmarshZeroGap` proves the unconditional shrinking zero-gap theorem.
- `SuzukiTitchmarshUniqueness` supplies `exists_uniform_riemannZeta_zero_window`, the exact uniform
  input needed here.
- Mandatory `formal_tools.py research` searches found no existing theorem connecting these zero
  windows to FZZ eigenpair phase incidence.

## Literature audit (28 August 2026)

- Titchmarsh, *The Theory of the Riemann Zeta-function*, Theorem 9.12, supplies the unconditional
  shrinking zero-window input; the corpus contains its closed Lean proof.
- Garunkštis–Laurinčikas–Macaitienė, *Zeros of the Riemann zeta-function and its universality*,
  Acta Arithmetica 181 (2017), reviews unconditional uniform distribution of zero ordinates and
  proves related scaled-ordinate distribution results: DOI 10.4064/aa8583-5-2017,
  https://www.impan.pl/shop/en/publication/transaction/download/product/111324
- Garunkštis–Panavas, *Discrete universality theorem for the Lerch zeta-function with shifts
  involving the imaginary parts of the Riemann zeta-function zeros*, Ukrainian Mathematical
  Journal 73 (2021), reviews the Elliott–Hlawka zero-ordinate distribution mechanism:
  https://umj.imath.kiev.ua/index.php/umj/article/download/893/9103/
- Jafferis–Schneider, arXiv:2004.05223, and Takook, arXiv:2606.13932, contain no coefficient-faithful
  FZZ eigenpair incidence or cofinal escape theorem.
- Targeted searches for the exact Titchmarsh/FZZ/Krein/Mellin synthesis found no match. Absence
  claim is bounded by searched primary-source corpus.

Novelty verdict: cofinal actual-zeta-zero escape from both members of the literal all-scale FZZ
Krein eigenpair appears corpus-new and literature-unlocated. It resolves the outstanding F11
divisor-incidence burden as a terminal no-go, but does not prove RH.

## Lean verification

- Direct checks passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityKreinEigenlineCofinalEscape.lean` and
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityKreinEigenpairCofinalEscape.lean`.
- Targeted builds passed for both named modules.
- Main theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Modules are wired into `GaloisForLFunctions.RHTower` umbrella.
- Authoritative global lint reports no error in these modules; current errors are unrelated
  pre-existing unreachable-module entries.

## Surviving open core

Construct and justify a higher-rank or interacting FZZ/GFZZ source whose phase image reaches the
right half-circle, then prove divisor incidence from its dynamics. Repackaging the literal
two-coordinate Krein block is ruled out cofinally.
