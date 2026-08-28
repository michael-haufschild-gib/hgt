# FZZ parity Fermi–Hankel positivity no-go

## Status

Route F4 retired. Bare multiplicative Fermi–Hankel positivity, including every nondegenerate
diagonal reweighting, fails on the first two source scales. Strongest indefinite survivor is
formalized in Lean.

## Attempted conjecture F4

Use the literal FZZ parity delay to define the symmetric multiplicative Hankel kernel
`K(x,y)=P(xy)`, where `P(t)=1/(exp t+1)` on positive delays. Conjecture that this source-exact
off-diagonal kernel, perhaps after a positive local change of density, is positive semidefinite and
can supply the Hilbert geometry orienting its Mellin divisor.

## Proof outcome

The conjecture fails at the smallest nontrivial block. On scales `1` and `2`, Lean proves

`P(1) P(4) - P(2)^2 < 0`.

Moreover:

- diagonal congruence by arbitrary weights `w₁,w₂` multiplies this determinant by
  `(w₁w₂)^2`;
- every nonzero real reweighting therefore retains a strictly negative determinant;
- in particular no positive diagonal density makes this block positive semidefinite;
- the bare quadratic form has an explicit strict positive direction `(1,0)` and an explicit strict
  negative direction `(P(2),-P(1))`.

## Why route fails

Positive-semidefinite kernels have nonnegative principal minors. The literal FZZ parity kernel has
a strict negative two-point principal minor, and local changes of measure act by diagonal
congruence, which cannot change its determinant sign. Thus neither passage to a continuous
positive density nor scale-local normalization can turn this source into a positive Hilbert
kernel.

This retires positive Fermi–Hankel orientation. It does not retire indefinite/Krein dynamics,
nonlocal source corrections, or interactions whose kernel is not a diagonal congruence of
`P(xy)`.

## Positive survivor

The first two literal FZZ parity scales carry an exact Lorentzian signature: their quadratic form
has both a strict positive and a strict negative direction, and every nondegenerate diagonal
reweighting preserves the negative determinant. This is a source-derived indefinite geometry,
stronger than mere failure of one normalization. Any surviving operator route must use that
indefinite structure honestly or add a genuinely nonlocal correction.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityFermiHankelPositivityNoGo.lean`.

Key declarations:

- `fzzCigarParityTwoScaleHankelMinor_neg`
- `fzzCigarParityTwoScaleReweightedMinor_eq`
- `fzzCigarParityTwoScaleReweightedMinor_neg`
- `not_fzzCigarParityPositiveDiagonalHankelPSD`
- `fzzCigarParityTwoScaleQuadratic_pos`
- `fzzCigarParityTwoScaleQuadratic_neg`

## Corpus audit

- `FZZCigarParityDelaySourceContinuation` gives the literal source identity
  `P(t)=1/(exp t+1)`.
- `SalemFermiModeIntegral` supplies its multiplicative Mellin action and exact zeta divisor.
- `FZZCigarParityDiagonalSuperKMSNoGo` forces the search beyond diagonal equilibrium data.
- No prior corpus theorem computes a source-exact off-diagonal principal minor of this
  multiplicative Fermi kernel or proves invariance of its strict negative sign under all diagonal
  reweightings.

## Literature audit (27 August 2026)

- Yafaev, *Criteria for Hankel operators to be sign-definite*, arXiv:1303.4040, develops general
  sign-function criteria for additive Hankel kernels and explains the relation between positive
  Hankel operators and positive Laplace representations. It does not treat the multiplicative FZZ
  kernel `1/(exp(xy)+1)` or this two-scale congruence obstruction:
  https://arxiv.org/abs/1303.4040
- Niemiec, *Positive Hankel operators, positive definite kernels and related topics*,
  arXiv:2001.06552, studies abstract positive Hankel realizations and double positivity. It does not
  identify or classify the FZZ/Salem multiplicative kernel: https://arxiv.org/abs/2001.06552
- Khare, *Multiply positive functions, critical exponent phenomena, and the
  Jain–Karlin–Schoenberg kernel*, arXiv:2008.05121, studies total positivity and Hankel-kernel
  preservers for different kernels. It does not contain the literal Fermi-product minor above:
  https://arxiv.org/abs/2008.05121
- González–Negrín, arXiv:2604.15396, uses Salem's Fermi integral equation for an RH equivalence but
  does not assert positivity of its multiplicative kernel: https://arxiv.org/abs/2604.15396
- Targeted searches found no primary source stating this exact FZZ/Salem two-scale negative-minor
  law. Absence claim remains bounded by the searched arXiv corpus.

Novelty verdict: exact source-level negative principal minor, diagonal-congruence no-go, and
explicit Lorentzian survivor appear corpus-new and literature-unlocated. They close one substantive
orientation family but do not discharge RH.

## Lean verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityFermiHankelPositivityNoGo.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParityFermiHankelPositivityNoGo`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Module is wired into `GaloisForLFunctions.RHTower` umbrella.
- Global lint has no error in this module; current failures are unrelated concurrently owned
  unreachable-module entries.

## Surviving open core

Construct a literal indefinite/Krein FZZ interaction or a genuinely nonlocal source correction
whose orientation is not erased by reflection pairing. Prove from that dynamics—not from a
positive reweighting of `P(xy)`—that every zero of the source-first parity Mellin transform has
real part `1/2`.
