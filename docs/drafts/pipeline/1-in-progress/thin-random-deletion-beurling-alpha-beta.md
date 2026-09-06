# Thin prime deletion: source and obstruction audit

- **ID:** `THIN-DELETION-ALPHA-BETA-001`
- **Stage:** 1-in-progress
- **Status:** `[PUBLISHED STRATEGY] [RANDOM BOUNDS UNPROVED] [NARROW LEAN SURVIVORS]`
- **RH used in local Lean results:** no

The finite sieve identity and exponential-versus-power inequality below are proved. They do not
prove the proposed random-deletion bounds or a universal obstruction to prime perturbations.
The earlier strategy-novelty claim and universal rejection are withdrawn.

## Literal proposal

Delete ordinary primes independently with probabilities comparable to `p^(gamma-1)`, where
`1/2<gamma<1`. Write B for the deleted set, D for its squarefree products, and P for retained
primes. The proposed count is `pi_B(x)` comparable to `x^gamma/log x`.

Finite inclusion-exclusion gives exactly
`N_P(x)=sum_(S subset B) (-1)^|S| floor(x/product S)`.
For infinite B with a convergent reciprocal sum, the intended error decomposition uses
`c_B=product_(p in B)(1-1/p)` and these signed sums:

```
x sum_(d in D, d>x) mu(d)/d,
sum_(d in D, d<=x) mu(d) {x/d}.
```

Bounds of order `x^(gamma/2+epsilon)` for both were conjectured, not proved. Independent prime
inclusions do not make products sharing a prime independent. Cardinality of D alone supplies
no cancellation estimate. Deleting p also removes every prime power p^k: the exact correction
to psi is `sum_(p in B, k>=1, p^k<=x) log p`, not just the prime-only contribution.

## Published ancestry

Broucke–Debruyne–Révész already use random deletion of a sparse subsequence of ordinary primes,
with count asymptotic to `Li(x^alpha)`. Section 5 compares its logarithmic zeta with
`log zeta(s+1-alpha)` and uses RH for reciprocal-zeta control. Theorem 1.3 gives, under RH,
systems with `1/2<alpha<2/3` and `2alpha/(alpha+2)<=beta<1/2`.
[Primary source](https://arxiv.org/html/2309.01567v2#S5).

The Bernoulli rule above is not asserted to be identical to their sampling algorithm. The
architecture of thinning ordinary primes, reducing the random error scale, and estimating
the sieve count is already published. Removing the RH input is a substantive missing estimate,
not a new architecture. This proposal fails the user's novelty and source restrictions.

## Why the recorded rejection did not cover the proposal

The rejected argument silently replaced `x^gamma/log x` by `x^gamma`. Partial summation gives

```
sum_(p in B) p^(-sigma) = sigma integral_1^infinity pi_B(x) x^(-sigma-1) dx.
```

Put `sigma=gamma+delta`. Under the stronger count comparison its singular scale is
`1/delta`. Under the original comparison, the large-x integral is comparable to
`integral_(log X)^infinity exp(-delta*u)/u du`, which diverges logarithmically in
`1/delta`. These are paper estimates, not formal arithmetic theorems in the modules below.
Higher prime powers require their own remainder estimate.

The bound `Phi(gamma+t)<=exp(-c/t)` contradicts every positive lower bound `K*t^m`.
Logarithmic divergence alone is compatible with an analytic zero: for every natural m and t>0,

```
exp(-m*log(1/t)) = t^m.
```

This identity passed a symbolic Lean check. It is a scalar counterexample to the proposed
inference, not a constructed deletion set. The exact leading coefficient and analytic
remainder still matter for any particular Euler product.

Three further inferences in the previous rejection were unsupported:

- A positive term of order `x^gamma` plus an uncontrolled error of that order does not give
  a lower bound on the sum.
- Failure to extend through a boundary point does not classify an isolated essential
  singularity without an isolated punctured neighborhood.
- Euler-product nonvanishing inside its convergence region does not forbid boundary zeros
  or zeros after continuation, and gives no general `beta>=gamma` inequality.

Thus the asserted equivalence with failure of RH, the extension to every insertion/deletion/
rescaling, and the claimed exhaustive classification are not proved and cannot serve as no-go
results. Neither is the stronger universal uncertainty conjecture supported by this audit.

## Exact positive survivors

| Statement proved | Lean module and declarations |
|---|---|
| Finite pairwise-coprime inclusion-exclusion | `ThinDeletionSieveIdentity`: `freeCount_insert`, `freeCount_eq_sum` |
| Exponential deficit eventually beats every positive polynomial lower bound | `ThinDeletionEssentialSingularity`: `exp_neg_div_lt_pow`, `no_finite_order_zero_absorbs_exponential_deficit` |
| Modification product nonzero in its specified convergence region | `BeurlingLatticeAndModificationBarriers`: `modification_factor_ne_zero` |

These are existing elementary results. Their proofs and declarations are unchanged. They
supply no probability theorem, infinite sieve error estimate, RH implication, or arithmetic
essential-singularity theorem.

`/tmp/hgt-thin-deletion-scope-tOIrDU/Audit.lean` checked the scalar identity and existing axioms
with `lake env lean`; all used only `propext`, `Classical.choice`, and `Quot.sound`.
Source-comment checks and narrow builds are recorded in the current corpus architecture audit.
No numerical computation was needed.
