# 001: arithmetic-symmetry-compatible global Meyer source splitting

Status: formalized. Counts as one structural contribution, not four files or
separate helper lemmas. Direct leaf and axiom audits pass. Repository lint has
two unrelated concurrent umbrella errors, listed below.

## Obstacle removed

The polynomial-module splitting supplied a global complement to the invisible
kernel in actual Meyer cohomology, commuting with its generator and fixing the
finite causal span. Its noncanonical extension did not establish compatibility
with the original Paugam reflection or arithmetic conjugation. Transporting new
abstract involutions through comparison would not establish that compatibility.

There is now a global complement preserved by both original source involutions.
It retains every actual comparison class and every original finite causal chain,
has the exact Xi spectrum, and admits a coherent resolvent family with both
arithmetic symmetry laws. A projected Gaussian proves this is not restricted to
finite spectral packets.

## Frontier inputs

- Meyer causal division and invisible polynomial injectivity supply the existing
  global generator-compatible splitting and exact observable-source spectrum.
- Hedenmalm causal chains supply actual strong-log sources with the identity
  `xi(s) = (s-rho)^k M(g_(rho,k))(s)`, and finite source synthesis.
- Paugam reflection and generalized Mellin-jet descent supply the original
  source involution, its Mellin action, and multiplicity-sensitive jet covariance.
- Arithmetic Xi divisor conjugation, the strong-log real structure, and the
  literal Schwartz endpoint/Poisson definitions supply genuine conjugation.

## Conjecture loop and dependency-closed proof

1. Transferring abstract involutions alone was rejected: it would not identify
   the original source actions. Instead, descend pointwise conjugation through
   the literal Poisson range. Conjugation preserves evenness and evaluation at
   zero. Fourier evaluation at zero equals the integral, so its kernel is also
   preserved. Conjugation commutes with the actual summation operator.

2. Generalized Mellin jets transform under reflection by `(-1)^j` and evaluation
   at `1-rho`; under conjugation they transform by conjugation and evaluation at
   `conj rho`. The all-jets characterization therefore makes the invisible
   kernel invariant under both original involutions.

3. The causal factorization, Xi symmetries, and Mellin injectivity give equalities
   before taking the Poisson quotient:
   `J g_(rho,k) = (-1)^k g_(1-rho,k)` and
   `C g_(rho,k) = g_(conj rho,k)`.
   Cancellation is proved off the relevant singleton and extended by continuity.
   Multiplicity preservation makes these identities preserve the original
   finite causal source span.

4. Let `P0` be the existing global projector, `K` its invisible kernel, and define
   `P1 = (P0 + J P0 J)/2`, `P2 = (P1 + C P1 C)/2`.
   Double conjugation is complex-linear. Averaging arbitrary projections would
   not suffice. Here every term annihilates `K` and differs from the identity by
   a vector in `K`; consequently `P2^2=P2` and `ker P2=K`. All finite causal
   sources remain fixed. The identities `A J = J-J A`, `A C=C A`, and `C J=J C`
   show that `P2` commutes with the generator and both original involutions.

5. The projectors mutually absorb: `P0 P2=P0` and `P2 P0=P2`. Their ranges are
   therefore linearly isomorphic, intertwining the actual generator and
   preserving the original comparison map. Transport of the already proved
   exact spectrum and resolvents gives
   `spectrum(A|range P2) = {rho | xi rho=0}` and, for regular parameters,
   `R_(1-rho) J = -J R_rho`, `R_(conj rho) C = C R_rho`.
   The usual resolvent identity is retained. These are actual source solutions
   of `(A-rho)u=f`, simultaneously on the whole actual comparison image.

6. If the new projected Gaussian belonged to the finite causal span, absorption
   and the fact that both projectors fix that span would put the old projected
   Gaussian there too, contradicting the existing non-finite-source theorem.

## Lean artifacts and validation

All files are in `formal/GaloisForLFunctions/RHTower/`:

- `DeningerMeyerCausalReflectionCovariance.lean`
- `DeningerMeyerCausalConjugation.lean`
- `DeningerMeyerArithmeticSymmetricSplitting.lean`
- `DeningerMeyerArithmeticSourceResolvent.lean`

Each passed a foreground direct audit using
`lake --old env lean -o <module.olean> <module.lean>` from `formal/`.
No full or umbrella build was run. All four imports are wired into
`formal/GaloisForLFunctions/RHTower.lean`.

A separate `/tmp` audit checked 17 principal theorem dependency closures and the
exact spectrum and symmetry-law types. Every axiom report was exactly
`[propext, Classical.choice, Quot.sound]`. Mathlib API names used by the proof
were separately checked against the installed toolchain. No numerical
experiments, additional axioms, proof holes, or heartbeat changes were used.

`scripts/formal_tools.py lint` ran and returned two errors, both outside this
contribution: `XiGaussianHeatBlockInertia` and `XiGaussianHeatBlockJacobiCensus`
were unreachable from the shared RHTower umbrella. Those concurrent files were
left untouched. No lint errors named this contribution. Owned scratch files and
search outputs were removed after inspection; all owned processes terminated.

## Exact frontier after this contribution

Original-source symmetry compatibility is removed as an algebraic obstruction to
global source division and rational spectral constructions. The construction is
noncanonical and algebraic. It does not establish continuity of the projector,
closedness or vanishing of the invisible kernel, a positive metric, trace
convergence, or RH. The model covers the actual comparison image; no assertion
is made that this image equals an arbitrary entire-function recipient.

Follow-up corpus search found `deningerPoissonMeyer_range_isClosed` in
`DeningerMeyerStrictEmbedding.lean`, strong-log Mellin continuity, and strong-log
flow continuity. Their exact source spaces and hypotheses must be read before
using them to propose a topological extension. A broad deep query expired during
reranking with partial results; a lexical query recovered these concrete leads.
