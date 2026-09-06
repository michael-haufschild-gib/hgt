# Exact freedom from paired large primes

**Paper status:** dependency-closed elementary proof below. **Lean:** closed; see [certificate](../3-formalized/euler-deletion-paired-prime-freedom.md).
**RH implication:** none. **Novelty:** not certified; do not present elementary prime
perturbations as a new RH architecture.

## General identity

Let `p,q` be distinct primes, `N < p^2,q^2,p*q`, and `floor(N/p)=floor(N/q)=M`.
For `|t|<1`, define `w(0)=0` and, for positive `n`,

`w(n)=(1+t)^(v_p(n))*(1-t)^(v_q(n))`.

Unique factorization gives `w(ab)=w(a)w(b)` for all natural `a,b`, `w(1)=1`, and
`w(n)>0` for every positive `n`. Below `N`, neither prime square nor their product
divides `n`; consequently

`w(n)=1+t[p|n]-t[q|n]`.

For any real coefficient function `f` satisfying `f(p*j)=f(q*j)=f(j)` for `1<=j<=M`,
write `S=sum_(n=1..N) f(n)` and `T=sum_(j=1..M) f(j)`. Reindex the two disjoint
sets of multiples. Opposite linear perturbations cancel and squared perturbations add:

`sum_(n=1..N) f(n)w(n)=S`,

`sum_(n=1..N) f(n)w(n)^2=S+2*t^2*T`.

The same disjoint decomposition gives a stronger statement for **every** function
`F: R -> R`, with no regularity assumption:

`sum_(n=1..N) f(n)F(w(n)) = F(1)*S + (F(1+t)+F(1-t)-2F(1))*T`.

This is the positive survivor: complete multiplicativity permits exact endpoint-preserving
deformations, and every scalar observation on these deformations is classified by the
shorter literal coefficient sum and the observation's three values. Linear and quadratic
responses are its immediate specializations. This strengthening uses the same pointwise
three-case decomposition and requires no new mathematical premise.

## Literal deletion coefficients and opposite signs

Set `N=930` and `a_d(n)=1-d[d|n]`. Whenever `d|30` and `p,q` are coprime to 30,
divisibility cancellation gives `a_d(p*j)=a_d(q*j)=a_d(j)`. Because `d|930`, the
baseline sum of `a_d` is zero. Thus every such endpoint remains zero.

The literal `2,3,5` curvature coefficient is already proved in the corpus to equal
`k=2(a_6-a_3+5a_15-5a_30)`. Its full-period sum is zero. More generally its prefix is

`sum_(n=1..M) k(n)=6*floor(M/3)-12*floor(M/6)-150*floor(M/15)+300*floor(M/30)`.

For `p=59,q=61`, both cofactor cutoffs are 15, the relevant prime squares/products exceed
930, and the shorter sum is `-144`. Hence quadratic curvature is `-288*t^2`.
For `p=251,q=257`, both cofactor cutoffs are 3 and the shorter sum is `6`; curvature
is `12*t^2`. Taking `t=1/2` gives strictly positive completely multiplicative weights
with identical zero endpoints but curvature `-72` and `3`, respectively.

The prime-value definition, divisibility reindexing and symbolic square expansion prove
these identities independently of exploratory computation. Formalization must reproduce
that proof, not import finite calculation outputs.

## Scope and search audit

This refutes the finite proposed inequality in
[the gate card](../5-failed/euler-deletion-complete-multiplicativity-gate.md).
It does not refute a theorem imposing the literal values `n^(-s)`, nor does it model
an actual zeta zero. A new zero-forced identity remains missing.

Corpus queries `"completely multiplicative"`, `prime multiplicative perturbation`,
`multiplicative closure`, and `deletion multiplicative` were paired with `rg` of
factorization, divisor reindexing and prior countermodels. Current source parents:
`Nat.factorization_mul`, `sum_Icc_filter_dvd_reindex`, and
`DeletionBalancedPeriods.curvature_coefficient_linear`.
Web searches for complete multiplicativity, finite perturbations and deletion curvature
did not certify novelty; a potentially related informal source failed to open. No claim
of absence from literature follows.
