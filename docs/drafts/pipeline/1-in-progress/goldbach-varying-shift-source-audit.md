# Varying reflected shift: determinant-source audit

- **ID:** goldbach-varying-shift-source-audit
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Goldbach target](goldbach-unconditional-2026-10-23.md), Cycle 6.
- **Statement:** Audit the varying-target determinant argument before attempting
  polynomial root averaging or prime-detecting roughness.

## New primary lead

Jizhou Guo's [The Möbius function at N−p](https://github.com/aster2024/openai-math-followups/tree/main/mobius-goldbach-shift),
dated 2026-10-22, explicitly assumes the correctness of specified LWW
arguments (`H2′`) and a zero-free input. Its claimed conclusion is
`Σ_{p<N}μ(N−p)=o(π(N))`, uniformly in even `N`, with corresponding
sign densities. A small-radical variant uses classical zero-free results.
These claims are not unconditional dependencies of this project.

The [LaTeX source](https://raw.githubusercontent.com/aster2024/openai-math-followups/main/mobius-goldbach-shift/source/main.tex)
was read through the Goldbach assembly, including its root count,
major-arc energy, Type I reduction, weight removal, and change dictionary.
Its Git blob was `fb5b09cc09a5b9161d7a9cd5a9ea6758b474112b` at inspection.
The small-shift and Liouville extension sections were not audited in this
batch. No ancillary computations were run.

## What changes in the research plan

It is no longer accurate to describe varying-target adaptation as absent
from the external leads. This source supplies an explicit candidate
adaptation. The outstanding task is to check its dependencies and the
additional restrictions needed here. Its stated conclusion still counts
negative-parity composites; it does not assert Goldbach or the cubic
roughness bias in Cycle 2.

## Finite block geometry checked on paper

Write the target as `T`, reserving `M,N` for variable lengths. The raw
equation `b(T−mn)=a(T−rs)` gives
`bmn−ars=T(b−a)`. For endpoints `P=(Dbm,s)`, `Q=(Dar,n)` with
unit coordinates modulo `T`, the determinant congruence is equivalent
to equality of slopes `P₂/P₁=Q₂/Q₁` in `Z/TZ`.

For a unit slope `ρ`, the lattice `v≡ρu (mod T)` has index `T`.
If `P=(u,v)` is primitive, choose `c′∈[0,u)` satisfying
`c′v≡−T (mod u)` and put `P*=(c′,(T+c′v)/u)`.
Both columns lie in the lattice and have determinant `T`, so form a
basis. Writing `Q=P z₁+P* z₂` gives

`det(P,Q)=T z₂`,
`Q₁=u(z₁+(c′/u)z₂)`,
`Q₂=v(z₁+(c′/u)z₂)+T z₂/u`.

Thus the large determinant can be divided by `T` within each lattice
block. These are exact algebraic identities. They do not show that all
moment estimates survive the change of state space. In particular,
normalizing the determinant does not eliminate the conductor from the
major-arc character average.

## Transfer boundaries still requiring proof

The source's root-count lemma keeps the product of prescribed prime
moduli below `exp(C(log T)^0.98)`. Its application uses finitely many
subpower prime pools and later removes their marks through an iterated
limit. Neither statement authorizes polynomial extra moduli or an
arbitrary fixed logarithmic rate after mark removal.

For the Goldbach route, two distinct questions therefore remain:

1. Can root congruences up to a useful polynomial level be retained with
   a sufficiently small **sum of absolute errors**? A per-modulus norm
   contraction does not give this sum. The exact common-cofactor and
   gcd-energy analysis is on the
   [energy card](goldbach-common-cofactor-energy.md).
2. Can prime-detecting roughness be retained? Every nonempty auxiliary
   mark requires a prime factor in its pool. Once the roughness threshold
   exceeds every pool prime, that marked weight is identically zero on
   the desired support. This is an exact support fact; improving the
   marked cancellation rate alone cannot remove this mismatch.

The last observation does not disprove an unmarked estimate, nor the
source's actual conclusion. A new transfer theorem must control the
residual on the desired support. Its size cannot be asserted from an
unsifted `o(π(T))` error, since the expected two-prime count is smaller
by another logarithm.

## Zero-free source located; local closure still open

The upstream [scope note](https://raw.githubusercontent.com/openai/math/main/lean/docs/003.md)
states the fixed half-plane for every positive modulus and character.
The [comparison configuration](https://raw.githubusercontent.com/openai/math/main/lean/ComparatorChallenges/DirichletSevenEighths.json)
maps its specification to `OAI.NumberTheory.DirichletL.Nonvanishing`
and permits only `propext`, `Quot.sound`, and `Classical.choice`.

The actual [solution module](https://raw.githubusercontent.com/openai/math/main/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)
was read. Its theorem
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`
has only the positive-modulus, half-plane, and excluded-pole conditions.
It invokes `SevenEighths.ProbeFinalAssemblyUnconditional.dirichlet_nonzero`.
That [assembly module](https://raw.githubusercontent.com/openai/math/main/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyUnconditional.lean)
was also read; it constructs its internal detector certificate before
applying the final theorem. The comparator's `sorry` is a specification
placeholder and is not evidence of a gap in this separate solution.

The full import closure, source definitions and axiom report have not
been replayed in this project. Neither a genuine seven-eighths theorem
nor maximal Möbius BV was supplied by the present corpus searches.
The zero-free input therefore has a precise external formalization
lead; it is not yet a checked local theorem. No upstream code was
executed or copied, and no analytic hypothesis was added to Lean.
The subsequent H2′ replay is recorded below. Even accepting the
zero-free input does not establish the prime-detecting transfer.

A later read was pinned to upstream commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`. It followed
`Energy.CertifiedExistence.terminal_certificate` through its actual
band induction and `Energy.CappedAnalyticSuccessor.actual_successor`,
and read `Detector.FinalAssemblyCertifiedBands` and
`Moments.DetectorPlainSlotProfile`. These interfaces are constructed
in the displayed assembly; their existence is not an extra premise
of the final nonvanishing theorem. The successor's low, high and
zero analytic stages still require closure checking.

That revision pins Lean v4.34.1; this project's `formal/lean-toolchain`
pins v4.32.2. No toolchain change, package execution, or source import
was made. The GitHub check-runs endpoint returned no checks for that
head; this is not a proof failure and does not establish whether the
upstream comparator was run elsewhere. Its README specifies a separate
comparator/export verification, which has not been replayed here.

## H2′ replay and reflected transfer, 2026-10-23

Read LWW Sections 4.2–4.7 and Appendix A against Guo's current
LaTeX source, whose blob remained
`fb5b09cc09a5b9161d7a9cd5a9ea6758b474112b`. No gap was found in the following chain. This records
paper verification of the specified argument, not a compiled Lean
certificate or an audit of every theorem in either manuscript.

- **Root count.** Appendix A proves its composite-modulus exponential
  sum bound by a fourth moment and the unit scaling orbit; even moduli
  and noncoprime frequencies are included. Its interval smoothing
  gives a rectangle error u^0.99 S². In the reflected version the
  inverse relation is c′v≡−T modulo u; (u,T)=1 preserves the same
  gcd bound. Sieving both coordinates against T gives the density
  ζ(2)^−1∏_(p|T)(p−1)/(p+1), bounded above by one. The divisor
  tail uses the exact cancellation
  Σ_(d|rad T)μ(d)/lcm(ℓ,d), zero when (ℓ,T)>1; it is not bounded
  by a spurious full divisor count. The swapped-coordinate branch
  retains both possible integer parts before clipping its interval.
- **Root replacement.** The relative determinant is integral after
  dividing by T in the index-T lattice. The path expansion retains
  prescribed projective lines, Bonferroni modulus exp(O(L^0.96)),
  and absolute coefficient mass exp(O_K(L^0.73)). Transverse position
  boundaries and the derivative 1/τ(z)² of the complementary ratio
  preserve the cube argument. Intermediate lattice-primitive points
  need not be units; endpoint coefficients vanish there. No false
  parity restriction is imposed on their first relative coordinate.
- **Clean signed operator.** The good-state test forces the shortest
  lattice vector to have length at least Y^−0.8. A reduced basis has
  a coordinate box of area comparable to Y, both sides between
  Y^0.1 and Y^0.9. The determinant exponential matrix is a tensor
  product of rectangular one-dimensional matrices; its minor-arc
  bound is O(L^(0.2−A_0)+Y^−0.1 log Y) after normalization.
  The endpoint weights and restrictions are bounded multipliers.
- **Memory and collisions.** Both absolute weighted Schur bounds for
  the memory operator are O_K(1); bounded symmetric selection phases
  preserve them. Dirty edges use the separate second good-state
  test and the residue-line count. The global distinctness expansion
  retains signed small norms on every unaffected edge; low-rank
  collisions affect at most twice their rank many edges. High-rank
  collisions gain the small mass of a prescribed pool prime. The
  memory truncation and coefficient mass are paid before the moment
  limit. No absolute bound replaces the clean signed cancellation.
- **Pairings and cleanup.** The coefficient-space Gram matrix is
  positive without normalizing the root vectors. Spectral Hölder
  is applied in the ambient space. Each unit-root interval in one
  residue block has O(d_0Y) positions, leaving trace loss
  (d_0Y)^(1/(2R))=O(1). The conjugation convention recovers the
  exact complex coefficient product. In cleanup, the comparison
  product lies in one residue class modulo T and an interval of
  length O(T), hence has O(1) choices. Summing all auxiliary-product
  intervals restores the full harmonic drawing probability.

The major-arc fibre characters are modulo kT, not necessarily k.
Only the quotient of the two fixed twists is induced from modulus
k. Under fixed seven-eighths zero-freeness, Guo's already-recorded
contour shortcut makes the marking polynomial small for every
nonprincipal character. The at most one principal marking character
then leaves a small-modulus Möbius polynomial. Classical maximal
Möbius BV plus partial summation supplies its required polylogarithmic
twists; the full polynomial-frequency version of LWW Proposition 2.2
is unnecessary here.

The [reflected root-average card](goldbach-reflected-marked-root-average.md)
contains the resulting Type I/II assembly, maximal endpoint inequality,
and root-summed error ledger. It reaches each fixed θ<1 for moduli
coprime to every marking prime, conditional only at the present audit
stage on the outstanding external zero-free proof closure. This is
not an analytic premise inserted into Lean. The mark still vanishes
on the prime complements required by Goldbach.

## Dependency and novelty status

- The specified LWW moment/root/memory chain and Guo's reflected
  changes passed the paper replay above; no Lean certificate exists.
- `[OPEN CORE]`: the zero-free input has not been replayed for this chain.
- The fixed-level root-average transfer is assembled on paper for
  moduli coprime to the pools. Its external zero-free closure, the
  shared-prime case, and signed mark removal on cubic rough support
  remain open here.
- The finite lattice identities above are known algebra, paper checked;
  no new Lean module or scientific advance is claimed.
- This is an active audit, not a retired route or a proof of impossibility.

## Log

- 2026-10-23 — Found the October 22 primary source; read its Goldbach
  argument and recorded its exact assumptions and transfer boundaries.
- 2026-10-23 — Located and read the zero-free comparator mapping and
  actual unconditional assembly endpoint. Recorded the distinction
  between a specification stub and its solution; full closure remains
  unaudited here. The reflected Type I part is separately proved on
  [its classical paper card](../2-fully-proven/goldbach-retained-modulus-type-i.md).
- 2026-10-23 — Replayed H2′ through its root count, clean and dirty
  operators, memory/distinctness, pairings, and cleanup, with Guo's
  target-dependent changes. Recorded the conductor distinction and
  the remaining zero-free and mark-removal dependencies.
