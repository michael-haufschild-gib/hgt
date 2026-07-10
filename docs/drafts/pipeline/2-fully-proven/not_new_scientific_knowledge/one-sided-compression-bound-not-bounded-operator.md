# One-Sided Compression Bound Does Not Give A Bounded Operator

- **ID:** one-sided-compression-bound-not-bounded-operator
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / operator-route guardrail
- **Source:** `relative-contraction-compression-exhaustion.md`;
  `loewner-contraction-congruence-normalization.md`
- **Statement:** A dense-domain one-sided inequality `k[v]<=||v||^2` does not
  by itself construct a bounded self-adjoint contraction. A lower form bound,
  boundedness proof, or closed-form replacement is a separate obligation.

## Setup

Let `H=ell^2(N)` with standard basis `(e_n)_{n>=1}`. Let `E` be the dense
subspace of finitely supported vectors, and let `E_d=span(e_1,...,e_d)`.

Define a symmetric quadratic form on `E` by

`k[v]= - sum_{n>=1} n |v_n|^2`,

where the sum is finite because `v in E`.

## Theorem

For every `v in E`,

`k[v] <= ||v||^2`.

Equivalently, every finite compression satisfies the one-sided inequality
`K_d<=I` in quadratic-form notation. Nevertheless, there is no bounded
self-adjoint operator `K` on `ell^2` whose quadratic form on `E` is `k`.

## Proof

The inequality is immediate because `k[v]<=0<=||v||^2`.

Suppose a bounded operator `K` represented `k` on `E`. Then for every basis
vector,

`<K e_n,e_n> = -n`.

But boundedness would give

`|<K e_n,e_n>| <= ||K||`,

for all `n`, contradiction as `n -> infinity`. Thus no bounded operator
represents the form.

Equivalently, the diagonal operator with eigenvalues `-n` is self-adjoint on
its natural domain and is bounded above by `I`, but unbounded below. It is not a
bounded contraction and has no finite operator norm.

## Consequence For The RH Route

Finite compression inequalities of the form

`P_d K P_d <= P_d`

or dense-domain inequalities

`k[p] <= ||p||^2`

do not, by themselves, construct the completed boundary operator promised in
the bridge route. They may define only a semibounded quadratic form, and even
that form still needs a closedness/domain theorem.

Therefore the boundary-Weyl route must state which of the following it proves:

1. a bounded self-adjoint source operator `K` with `K<=I`;
2. a closed semibounded form `q=I-K` that is the actual proof object, with its
   domain and source construction specified;
3. a two-sided bound or other structure that upgrades the dense-domain form to
   a bounded operator.

Calling `K_d<=I` a "contraction" before this step is a coordinate slogan, not
an operator theorem.

## Gates

- [x] 0 -> 1 in-progress: one-sided completion loophole isolated.
- [x] 1 -> 2 fully-proven: diagonal counterexample written.
- [ ] 2 -> 3 formalized: bounded-operator contradiction on `ell^2`.

## Log

- 2026-06-24 -- Codex: created after the compression-exhaustion card. It
  separates finite one-sided form positivity from construction of a bounded
  completed contraction.
