# Complete multiplicativity as an arithmetic closure gate

**Stage:** 5-failed. **Type:** FALSIFIED finite sign constraint. **RH implication:** none.
**Novelty:** not certified. This is not a qualifying RH architecture yet.

## Place in the proposed proof chain

Literal deletion coefficients give scalar endpoints `(1-p^(1-s))*zeta(s)`. Their joint ordered
product and its sharp one-fifth admission boundary are now constructed in Lean. The missing link
is a further relation forced by an actual zeta zero. The factorization curvature has a known
strict sign at a hypothetical strict-right zero, but no opposite inequality or vanishing theorem.

The existing finite positive-weight countermodels do not require complete multiplicativity.
The actual weights `n^(-s)` do satisfy it. Test whether this additional arithmetic property
changes the finite closure-to-curvature inference before proposing it as a mechanism.

## Exact test

Write `a_d(n)=1-d[d divides n]`, and let `k(n)` be the literal `2,3,5` curvature coefficient
from `EulerDeletionBalancedPeriodFreedom`:

`k(n)=2*(a_6(n)-a_3(n)+5*(a_15(n)-a_30(n)))`.

For `N` divisible by 30, seek strictly positive completely multiplicative weights `w` with

`sum_(n=1..N) a_d(n)w(n)=0` for every `d divides 30`.

**Falsified candidate constraint:** these hypotheses force
`sum_(n=1..N) k(n)w(n)^2 >= 0`.

A negative exact example kills this finite proposed constraint. A positive result at a few
cutoffs does not establish the conjecture, transfer it to complex Mellin weights, or prove RH.
Even the universal finite inequality would still need a justified infinite limiting argument.

## First analytic audit at the uniform weight

Parameterize completely multiplicative positive weights by prime values
`w_t(p)=exp(t*x_p+O(t^2))`. Their first variation is
`phi(n)=sum_p v_p(n)*x_p`. The linearized endpoint constraints are the exact finite matrix

`A_(d,p)=sum_(n=1..N) a_d(n)*v_p(n)`, with `A*x=0`.

Because `k` is already a linear combination of the endpoint coefficient rows, exact endpoint
closure gives the identity

`sum k(n)w(n)^2 = sum k(n)(w(n)-1)^2`.

Its second-order coefficient is therefore the explicit quadratic form
`sum k(n)*phi(n)^2`, restricted to `ker A`. A negative direction is only a local diagnostic:
it still requires proof that the tangent integrates to exact closed completely multiplicative
weights. No sampled or floating-point matrix signature can establish the final assertion.

## Source and validation boundary

Corpus search used `research "multiplicative closure"` and `research "deletion multiplicative"`,
then `rg` and exact source reads of `EulerDeletionBalancedPeriodFreedom`. The existing general
curvature linearization and opposite-perturbation theorem are proved; the completely
multiplicative constraint is additional and is not covered by those countermodels.

Exploratory exact finite linear algebra ran on the user-authorized Runpod, with six independent
workers. Negative tangents at cutoffs 180 and 210 prompted a separate symbolic prime-pair
construction. The tangent vectors and matrices are not Lean proof certificates.

## No-go closure

**Exact killing theorem:** at cutoff 930, the global positive completely multiplicative
weight with prime values `w(59)=3/2`, `w(61)=1/2`, all other prime values one, has every
divisor-of-thirty deletion endpoint zero but quadratic curvature `-72`. Another prime pair,
251 and 257, gives curvature `3` with the same endpoints and cutoff.

**Strongest positive survivor:** matched large-prime perturbations classify every scalar
observation `F`, without regularity assumptions. If `S` is the full coefficient sum and `T`
the shorter cofactor-prefix sum, the exact observation is
`F(1)*S + (F(1+t)+F(1-t)-2F(1))*T`. Thus complete multiplicativity leaves explicit nonlinear
freedom even after all the stated endpoint constraints are met.

**Proof status:** dependency-closed paper proof and Lean formalization, including the general
observation formula and premise-free countermodel capstone. Source module
`EulerDeletionPairedPrimeFreedom`; namespace `RHTower.DeletionPairedPrimes`.
[Paper](../2-fully-proven/euler-deletion-paired-prime-freedom.md),
[Lean certificate](../3-formalized/euler-deletion-paired-prime-freedom.md),
[computation report](../2-fully-proven/computations/deletion-multiplicativity-tangent/REPORT.md).

**Research consequence:** complete multiplicativity alone does not supply the missing finite
curvature sign. This does not rule out a law derived from the exact infinite values `n^(-s)`
or an actual zeta zero. Those remain additional obligations, not consequences of this test.
