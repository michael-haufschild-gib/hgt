# Loewner Contraction Congruence Normalization

- **ID:** loewner-contraction-congruence-normalization
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / operator-coordinate normalization
- **Source:** `seam-log-hankel-rh-equivalence.md`;
  `positive-source-weights-do-not-bound-loewner-budget.md`;
  `finite-rank-boundary-schur-index.md`;
  `docs/consolidated/revision01/bridge-theorem.md`
- **Statement:** The relative contraction

  `K=M^(-1/2)(-R)M^(-1/2)`

  is exactly a congruence normalization of the Loewner inequality

  `M+R>=0`.

  Therefore the proposed bridge inequality

  `-R^P_d <= M_triv,d`

  and the finite-section contraction condition

  `K_d <= I`

  have the same mathematical content unless `K_d` is constructed and bounded by
  an independent source theorem.

## Setup

Let `E` be a finite-dimensional real or complex vector space. Let `M` be a
positive definite Hermitian form on `E`, and let `R` be a Hermitian form on `E`.

Set

`Q=M+R`

and define the relative operator

`K=M^(-1/2)(-R)M^(-1/2)`.

Here `M^(1/2)` denotes any positive square root in coordinates; equivalently,
choose a Cholesky factor `M=LL*` and write

`K=L^(-1)(-R)L^(-*)`.

## Theorem

The following are equivalent:

1. `Q>=0`.
2. `-R<=M` in the Loewner order.
3. `K<=I`.
4. `I-K>=0`.

Moreover,

`kappa_-(Q)=kappa_-(I-K)`,

and, in the positive definite case,

`Q>0 <=> lambda_max(K)<1`.

Thus the spectral margin

`1-lambda_max(K)`

is the generalized eigenvalue margin of the pencil `(Q,M)`.

## Proof

The Loewner inequality `-R<=M` is just `M+R>=0`, so `1` and `2` are the same
statement.

Using a Cholesky factor `M=LL*`,

`Q=M+R=L(I-K)L*`.

Since congruence by the invertible map `L` preserves inertia, Sylvester inertia
gives

`inertia(Q)=inertia(I-K)`.

In particular,

`Q>=0 <=> I-K>=0`,

which is the same as `K<=I`. This proves the equivalence of all four
conditions and the negative-index identity.

When `Q>0`, the congruent form `I-K` is positive definite. Since `K` is
Hermitian in the `M`-orthonormal coordinate, this is equivalent to every
eigenvalue of `K` being less than `1`, i.e.

`lambda_max(K)<1`.

The smallest eigenvalue of `I-K` is `1-lambda_max(K)`, which is exactly the
smallest generalized eigenvalue of `Q v = lambda M v`.

## Application To The Reciprocal Seam Route

In the bridge notation, finite sections of the shifted reciprocal form are

`Q_0,d = M_triv,d + R^P_d`,

where `M_triv,d` is the positive trivial-zero budget and `R^P_d` is the
prime-source residual.

For each finite degree `d`, the trivial-zero budget is positive definite: a
nonzero polynomial of degree at most `d` cannot vanish on all of the infinitely
many distinct trivial reciprocal points, and the weights are positive. Hence the
relative contraction

`K_d=M_triv,d^(-1/2)(-R^P_d)M_triv,d^(-1/2)`

is defined, and

`Q_0,d>=0 <=> K_d<=I`.

Thus the operator face and the moment face are the same finite-dimensional gate
after a positive congruence.

## Consequence for the RH Route

This theorem does not prove `K_d<=I`. It says what kind of proof would be
non-mirror.

The contraction language is useful only if the operator `K` is built from
Euler/Gamma/functional-equation source data and the bound `K<=I` is proved
before reciprocal zero positivity is used. If `K_d<=I` is checked only after
forming the shifted zero moment form, then the argument has merely rewritten
`Q_0,d>=0`.

Therefore the live theorem is not:

`Q_0,d>=0 <=> K_d<=I`.

That is the congruence above. The live theorem is:

`source data => K<=I`

or equivalently

`source data => -R^P <= M_triv`

with the source construction occurring before the zero divisor is read.

## Theatre Test

For any proof using the relative contraction:

1. Was `M_triv` constructed from the Gamma/trivial-zero source only?
2. Was `R^P` constructed from Euler/local-factor data before using reciprocal
   zeros?
3. Is `K<=I` proved by a source theorem, or only inferred from `Q_0>=0`?
4. Is the proof uniform in degree and channel scale?

If the answer to `3` is the second option, the contraction is a coordinate
change, not a proof mechanism.

## Source Boundary

This is finite-dimensional linear algebra. Its significance is route control:
it prevents the operator contraction from being counted as an additional RH
target beyond the all-order shifted Stieltjes cone.

## Gates

- [x] 0 -> 1 in-progress: relative contraction route isolated.
- [x] 1 -> 2 fully-proven: congruence and inertia equivalence proved.
- [ ] 2 -> 3 formalized: optional Hermitian congruence theorem.

## Log

- 2026-06-24 -- Codex: created under the private anti-theatre pass. The card
  records that `K_d<=I` is the positive-congruence form of `Q_0,d>=0`; a proof
  must source-build and bound `K`, not count the congruence as progress.

## 2026-06-24 Completion Requirement

`relative-contraction-compression-exhaustion.md` records the Hilbert-space
version of this finite-dimensional congruence. If a bounded self-adjoint source
operator `K` is constructed on the `M_triv` completion, then `K<=I` is
equivalent to all polynomial compression inequalities by density.

Thus the finite congruence here is only the coordinate normalization. The proof
route still owes the completed operator or closed-form construction before the
finite compression family can be counted as an operator theorem.

## 2026-06-24 One-Sided Bounds Need Operator Construction

`one-sided-compression-bound-not-bounded-operator.md` complements the completion
requirement. The inequality `K<=I` on a dense polynomial domain is only an upper
form bound. It does not imply that `K` is a bounded operator or a contraction in
operator norm.

Therefore a source proof must specify whether the completed object is a bounded
self-adjoint contraction, or a closed semibounded form `I-K`. The finite
Loewner congruence does not decide this domain question.
