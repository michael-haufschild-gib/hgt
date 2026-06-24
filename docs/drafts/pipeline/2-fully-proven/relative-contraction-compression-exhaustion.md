# Relative Contraction Compression Exhaustion

- **ID:** relative-contraction-compression-exhaustion
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / operator-route target
- **Source:** `loewner-contraction-congruence-normalization.md`;
  `finite-degree-reciprocal-tests-height-limited.md`;
  `docs/consolidated/revision01/bridge-theorem.md`
- **Statement:** A source-built relative contraction is proved by a bounded
  operator inequality on the Hilbert completion. Its finite polynomial
  compressions are equivalent to that inequality only after boundedness and
  dense-domain exhaustion have been supplied.

## Setup

Let `H` be a Hilbert space, and let

`E_0 subset E_1 subset ...`

be finite-dimensional subspaces whose union `E` is dense in `H`. Let `K` be a
bounded self-adjoint operator on `H`, and let `P_d` denote the orthogonal
projection onto `E_d`.

In the reciprocal route, `H` is the completion in the positive budget metric
`M_triv`, the spaces `E_d` are polynomial subspaces of degree at most `d`, and
`K` is the proposed completed relative operator

`K=M_triv^(-1/2)(-R^P)M_triv^(-1/2)`.

## Theorem

The following are equivalent:

1. `K<=I` on `H`.
2. `P_d K P_d <= P_d` on `E_d` for every `d`.
3. `<Kv,v> <= ||v||^2` for every `v` in the algebraic union `E`.

Thus all finite compression inequalities are exactly the dense-domain quadratic
form version of the completed contraction, provided the bounded self-adjoint
operator `K` has already been constructed.

## Proof

`1 -> 2` is immediate by restriction to `E_d`. The implication `2 -> 3` follows
because every `v in E` lies in some `E_d`.

For `3 -> 1`, define

`Q(v)=||v||^2-<Kv,v>`.

Since `K` is bounded, `Q` is continuous on `H`. The dense subspace `E` satisfies
`Q(v)>=0` by `3`. For any `h in H`, choose `v_n in E` with `v_n -> h`. Then

`Q(h)=lim_n Q(v_n)>=0`.

Therefore `<Kh,h><=||h||^2` for every `h`, i.e. `K<=I`.

## Finite-Depth Blindness

For any fixed `D`, finite compression positivity up to `E_D` does not imply
`K<=I`. If `u` is a unit vector orthogonal to `E_D`, then

`K=(1+epsilon) u tensor u`

has `P_d K P_d=0<=P_d` for every `d<=D`, but `K<=I` fails. Therefore a proof
that checks only finitely many sections has not entered the operator theorem.

## Consequence For The RH Route

This theorem separates the legitimate operator proof from its mirrors.

A noncircular boundary-Weyl proof must supply all three items:

1. construct `K` from Euler/Gamma/functional-equation source data before using
   reciprocal zero positivity;
2. prove that `K` is a bounded self-adjoint operator on the `M_triv`
   completion, or state the correct closed quadratic-form replacement;
3. prove `K<=I` on the completion.

Finite matrices `K_d<=I` are useful only as compressions of this completed
source operator. Without the source construction and the completion theorem,
they are just the finite shifted-Hankel/RH gate in normalized coordinates.

## Gates

- [x] 0 -> 1 in-progress: compression-exhaustion target isolated.
- [x] 1 -> 2 fully-proven: bounded self-adjoint compression theorem proved.
- [ ] 2 -> 3 formalized: Hilbert-space bounded self-adjoint form theorem.

## Log

- 2026-06-24 -- Codex: created to pin the operator route after finite-height
  and monomial-tail guardrails. The bridge must now source-build a completed
  contraction, not accumulate finite compression checks.

## 2026-06-24 One-Sided Form Bound Caveat

`one-sided-compression-bound-not-bounded-operator.md` records the lower-bound
completion issue. A dense-domain inequality `k[v]<=||v||^2`, even on every
finite compression, does not by itself construct a bounded self-adjoint
operator. A diagonal form with entries `-n` passes the one-sided upper bound but
is unbounded below.

Thus the operator route must either prove a bounded self-adjoint `K`, or replace
`K` by a closed semibounded form with the correct source-built domain. Finite
one-sided compression inequalities alone are not a completed boundary operator.
