# Exact k-context frustration bound

Stage: 3-formalized

Status: `[LITERATURE] [PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN PROVED]`

Lean: `formal/GaloisForLFunctions/HTGeometry/ContextFrustrationBound.lean`, declarations
`KLocalCorrelation.contextFrustration_lower` and
`uniformBoundaryCorrelation_contextFrustration`. Proof includes exact incidence multiplicity and
the equality case; closed without added axioms.

Source: Theorem 5.5 of *Locally Quantum, Globally Non-Hilbertizable* (Zenodo 21982163).

## Statement

Let `C` be a finite complex unit-diagonal kernel on `n` contexts. Suppose every principal
restriction to at most `k` contexts is positive semidefinite, with `2 <= k <= n`. Define

`S(C) = (1/2) sum_{i != j} Re C(i,j)`.

Then

`S(C) >= -n(n-1)/(2(k-1))`.

The bound is exact. It is attained by the uniform kernel with diagonal `1` and every off-diagonal
entry `-1/(k-1)`.

## Dependency-closed proof

For every `k`-subset `T`, evaluate its PSD restriction on the all-ones vector. Unit diagonal gives

`k + sum_{i != j in T} Re C(i,j) >= 0`.

Sum over every `k`-subset. Each ordered pair of distinct vertices belongs to exactly

`choose(n-2,k-2)`

such subsets, while there are `choose(n,k)` subsets. Therefore

`choose(n-2,k-2) sum_{i != j} Re C(i,j) >= -k choose(n,k)`.

The exact incidence identity

`choose(n,k) k(k-1) = n(n-1) choose(n-2,k-2)`

and positivity of `choose(n-2,k-2)` yield the claimed bound after division by two.

For sharpness, the uniform kernel on any subset of size `m <= k` has constant-line eigenvalue

`1 - (m-1)/(k-1) >= 0`

and transverse eigenvalue `1 + 1/(k-1) > 0`, so every such restriction is PSD. Its ordered
off-diagonal sum is exactly `-n(n-1)/(k-1)`, hence `S(C)` attains equality.
