# Positive Meyer degrees and the infinite source tail

- **ID:** positive-meyer-degrees-and-the-infinite-source-tail
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Q-II; exact positive finite-jet degree classification.
- **Statement:** Does positivity on the full actual sharp-convolution algebra force a degree to be determined by its nonnegative critical-value weights, without a continuity premise?
- **Status:** OPEN. The finite-degree, projector, character, and Hermitian-part modules below remain unverified until their direct Lean checks and transitive axiom audits pass. The critical trace and quasi-inverse radical modules are now certified.

## Finite classification candidate

The unverified Lean candidate `PositiveMeyerDegreesSeeReducedCriticalJets.lean`,
described in `positive-degrees-see-only-reduced-critical-jet-blocks.md`,
classifies the restriction to every actual finite jet packet: off-line blocks
and higher critical jets have zero degree; critical value weights are real
and nonnegative. It does not determine an arbitrary degree on infinite
source classes. The real-positive case reduces to the Hermitian part, by
`real-positive-meyer-degrees-are-controlled-by-their-hermitian-part.md`.

## Exact finite-to-global bound candidate

Let d be a positive Hermitian degree and E_d(u)=Re d(u sharp(u)). For a finite
set S of critical Xi points, the existing actual causal projector P_S cuts
out all lower jets at S. Full jet separation gives

    P_S(u) v = P_S(u v),
    sharp(P_S u) = P_S(sharp u),
    P_S² = P_S.

Thus the two parts P_S u and u-P_S u are orthogonal for the degree pairing:

    E_d(u) = E_d(P_S u) + E_d(u-P_S u).

The first term is exactly the finite sum of the critical weights times the
squared zeroth values, by the finite-jet degree classification. The second
is nonnegative. Therefore every such finite weighted sum is bounded above
by E_d(u), for each actual class u. This bound needs no continuity of d.

## Open infinite tail

These bounded finite sums give a well-defined regular square energy. They
do not by themselves show that the remaining nonnegative energy is zero.
A degree might, a priori, vanish on every finite packet while retaining
infinite-class energy. No interchange of an infinite packet expansion with
an arbitrary algebraic functional is authorized.

The canonical full critical-value trace is now certified in
`CriticalMeyerTraceDegree.lean` and
`../3-formalized/the-critical-meyer-trace-is-positive-but-selective.md`.
Its square energy is the summable critical-value norm square, with exact
critical-value kernel. This supplies one infinite positive descended degree;
it does not determine an arbitrary degree or eliminate its possible remainder.

Corpus searches found actual finite causal projectors, trace-class
summability, and source convolution solvability, but no applicable automatic
continuity or source square-root factorization theorem. The Schwartz square
root regularization module uses approximation; approximation alone cannot
be passed through an arbitrary discontinuous degree.

## Candidate mechanisms and obligations

1. Prove an algebraic factorization/order bound on actual sources that forces
   continuity of positive functionals in an existing source topology.
2. Or classify a residual positive form annihilating every finite packet and
   determine whether it can be nonzero on the literal quotient.
3. First formalize the exact finite-projector product law and square-energy
   decomposition above; these are the dependency-closed positive result.

No infinite classification, continuity, or zero tail is assumed. This route
is active and has not been declared false or retired. No numerical experiment.

A distinct multiplicative subproblem has an unverified Lean candidate,
`MeyerAlgebraicCharacters.lean`, described in
`../2-fully-proven/meyer-algebraic-characters-have-no-infinite-tail.md`:
original source-class Fredholm inversion forces every nonzero algebraic
character to detect a finite resonant packet, hence a unique zeroth Xi value.
Its positive/Hermitian characters are exactly the critical evaluations. This
does not yet eliminate residual energy for an arbitrary positive linear degree.

## Quasi-inverse refinement

The actual source quasi-inverse theorem now gives the certified result
`MeyerQuasiInverseRadical.lean`, described in
`../3-formalized/meyer-trace-radical-is-the-quasi-inverse-radical.md`:
a class has all Xi values zero exactly when every one of its products admits
an actual quasi-inverse. This identifies the trace radical by convolution
solvability, without passing through a Hilbert completion.

The remaining candidate mechanism is an exact source order or square-root
factorization, possibly after finite resonant repair. Existing source inversion
alone constructs rational functions of a class; it does not yet construct
positive square roots or justify applying a discontinuous degree to a limit.
Corpus searches for automatic positivity/continuity and Meyer holomorphic
functional calculus have not supplied that missing theorem. No conclusion
about the infinite residual is drawn from quasi-inversion alone.
