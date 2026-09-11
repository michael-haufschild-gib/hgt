# Route L: complete coherent stars and actual row correction

Status: formalized; scratch Lean, all-theorem axiom audit, final single-module build and repository lint passed.
Date: 2026-09-11.

Module: `GaloisForLFunctions.RHTower.XiGammaSixWoldJordanCoherentStar`.

## Target and exact source

The missing RH step remains agreement of the completed Green/BV source with the
fixed physical reader. This test asks whether actual complete coherent
corrections, controlled by marginal variation, are invisible in the existing
one-leg graph completion.

Let `R(a,S)` be the existing complete Frobenius right-leg packet. Its coefficient
at the ordered distinct-prime edge `(r,t)` is `conj(a(r)-a(t))` if both labels
belong to `S`, and zero otherwise. For `p in S`, put `N=|S|` and

`u(p,S) = N^-1 R(1_p,S)`.

This is itself a complete coherent packet, with the scalar absorbed into its
conjugate-linear profile. The formal construction uses
`S_n = {p} union {first n primes}`, independently of `A` or Xi zeros.

## Formal statements

At each finite stage:

- The trace of `u(p,S)` is zero.
- Its left-prime marginal is exactly `delta_p - uniform(S)`.
- Its marginal variation is at most two.
- Its squared ambient Hilbert norm is exactly `2(N-1)/N^2`.

As `n` tends to infinity:

- `u(p,S_n)` tends to zero in both ambient and one-leg graph norms.
- Every marginal coefficient tends to the corresponding coefficient of `delta_p`.
- The existing reciprocal energy reporter tends to `A/p`, for every real `A`.

The theorem `deningerBigWittCoherentStarSequence_spec` supplies the simultaneous
complete-coherent membership, trace, variation, marginal, graph and energy laws.

For the existing genuine trace-normalized fixed-left row `r_(a,n)`, with
`p=nthPrimeSubtype a`, its marginal is exactly `delta_p`. Define

`g_(a,n) = r_(a,n) - u(p,S_n)`.

Lean proves that `g_(a,n)` has trace one and marginal `uniform(S_n)`, whose
variation is exactly one. It converges to the original nonzero singular graph
vector, but every fixed-prime marginal and the reciprocal reporter tend to zero.
No claim of nonnegativity of every corrected edge is made.

## Dependency-closed paper proof

Evaluate the finite sum of single-edge packets at one ordered edge. Only its
matching term survives. Squaring the ambient Hilbert norm therefore gives
`sum_(r,t in S) |a(r)-a(t)|^2`; diagonal terms are zero. For the indicator
profile there are precisely the two orientations connecting `p` to each other
label, so the normalized sum is `2(N-1)/N^2`.

The proved complete coherent marginal formula gives `delta_p-uniform(S)`.
Its variation is at most the sum of the variations of those two terms, namely
two. The uniform coefficients have absolute value at most `1/N`, and
`|S_n|>=n`, so they tend to zero. The exact squared norm tends to zero, and
trace zero supplies the graph convergence.

The earlier signed-marginal continuity theorem applies because the variation
bound is uniform and the target marginal has finite support. It identifies the
energy limit with the existing reporter on `delta_p`, namely `A/p`.

Testing the existing normalized row reporter with each prime indicator proves
that row's exact marginal `delta_p`. Subtraction gives the corrected uniform
marginal. Linearity preserves trace one; subtraction of a graph-null sequence
preserves the singular graph limit. The same controlled-marginal theorem now
gives energy limit zero for the corrected row.

## Failed inference and positive survivor

Complete-coherent membership, graph convergence to zero and uniformly bounded
marginal variation do not imply invisibility to the fixed reader. Even every
individual normalized edge can vanish while the aggregate marginal survives.
The positive survivor identifies all the retained data and the exact effect of
a complete coherent repair on a genuine source row. The signed repair cancels
energy by replacing its retained anchor mass with escaping uniform mass.

The result does not identify the cyclic source reader with the physical reader,
force the coefficient `A` to vanish, or prove RH. It does not retire route L.
A stricter source-domain test now asks whether nonnegative corrected edges force
retention of the original anchor mass; its proposed bound is documented in
[the active attack card](../1-in-progress/route-l-source-selected-completion-attack.md).

## Verification

- Scratch: `lake env lean /tmp/route_l_coherent_star.lean` — passed.
- Final audit: `lake build GaloisForLFunctions.RHTower.XiGammaSixWoldJordanCoherentStar` — passed.
- Umbrella: import wired in `RHTower.lean`; no umbrella build run.
- Axiom audit: `lake env lean /tmp/route_l_coherent_star_axioms.lean` — all 28 theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/formal_tools.py lint` — passed.
- Scoped whitespace checks passed. All owned Lean processes completed; no full or umbrella build ran.
