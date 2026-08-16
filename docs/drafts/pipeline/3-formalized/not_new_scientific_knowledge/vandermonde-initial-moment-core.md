# Vandermonde initial moment core

- **ID:** vandermonde-initial-moment-core
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** split from `zero-estimate-uniformity.md` part (a), and reused by
  `exponential-sum-order-bound.md`.
- **Statement:** At `n` distinct complex nodes, the first `n` power moments determine the coefficient vector;
  equivalently, a nonzero coefficient vector has a nonzero moment among the first `n` moments.

## Goal

This banks the exact finite Vandermonde algebraic core used by the diagonal zero-estimate card. It does not
claim the analytic exponential-sum derivative wrapper, the Bohr-polynomial support wrapper, determinant size
estimates, or canonical-exhaustion/PNT uniformity.

## Paper Proof

Let the nodes `mu_i` be distinct. If the moments
`sum_j c_j mu_j^k` vanish for `k=0,...,n-1`, fix an index `i` and use the Lagrange complement polynomial
`P_i(X)=prod_{j != i} (X-mu_j)`. This polynomial has degree `< n`, vanishes at every `mu_j` with `j != i`,
and is nonzero at `mu_i`.

Since `P_i` is a linear combination of `1, X, ..., X^{n-1}`, the moment vanishings give
`sum_j c_j P_i(mu_j)=0`. All terms except `j=i` vanish, so `c_i P_i(mu_i)=0`; as `P_i(mu_i) != 0`, we get
`c_i=0`. Since `i` was arbitrary, `c=0`.

The contrapositive gives the initial-moment form: if `c` is nonzero, then some moment with `k<n` is nonzero.

## Gates

- [x] 0 -> 1  in-progress: exact finite Vandermonde algebraic lemma extracted from the zero-estimate card.
- [x] 1 -> 2  fully-proven: paper proof above by Lagrange complement polynomials.
- [x] 2 -> 3  formalized: Lean theorems `vandermonde_moments_eq_zero_of_injective` and
  `vandermonde_initial_moment_nonzero_of_nonzero_coeff` in
  `formal/GaloisForLFunctions/RHTower/ZeroEstimate.lean`; names checked by scratch file; `#print axioms` uses only
  the allowed standard subset `[propext, Classical.choice, Quot.sound]`; `lake build` green;
  `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the Vandermonde algebra lemma inside the G2 zero-estimate note.

## Door Passport

Door-2 strips this to elementary finite-dimensional linear algebra, so it is BRIDGE. Its value is as the
Lean-certified algebraic core behind the zero-estimate order bound.

## Log

- 2026-06-19 - Leaner split this exact Vandermonde moment lemma from `zero-estimate-uniformity`. The parent
  card remains in `2-fully-proven` because its analytic derivative wrapper, Bohr support wrapper, determinant
  size estimate, and canonical-exhaustion/PNT uniformity bookkeeping are not all formalized in one theorem.
