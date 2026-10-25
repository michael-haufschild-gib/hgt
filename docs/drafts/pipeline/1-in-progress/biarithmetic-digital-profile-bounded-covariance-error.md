# Uniform digit refinement gives bounded covariance errors

- **ID:** biarithmetic-digital-profile-bounded-covariance-error
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (Lean formalization incomplete)
- **Proof status:** Only statements with completed Lean checks and axiom audits are proved. Paper arguments below are proof plans; every significant claim remains a formalization obligation.
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** The scaled geometric digit rows converge uniformly to their positive profile with an explicit geometric error. In the strict escape range, every unnormalized cofactor covariance differs from its profile integral by a bounded amount. At criticality, every covariance is its annular coefficient times the number of complete blocks, plus a bounded error. The same conclusions transfer to the actual positively damped golden source.

## Uniform refinement

Fix `1<a<5`, put `C=a/(5-a)`, and let `D_a` be the exact base-five digit row.
For `x>=0`, set

`H_M(x)=C a^(-M) D_a(floor(5^M x))`.

Euclidean division gives an integer `0<=r<=4` with
`floor(5^(M+1)x)=5 floor(5^M x)+r`. The checked digit recurrence therefore gives

`H_(M+1)(x)-H_M(x)=C a^(-M-1) r`.

Consequently these functions increase pointwise, and their differences form a uniformly
convergent geometric series on the entire nonnegative half-line. Their limit `F` satisfies

`0<=F(x)-H_M(x)<=B a^(-M)`, where `B=4C/(a-1)`.

Every `H_M` is right continuous and regulated on compact intervals, so the uniform limit
has those properties. Scaling the defining sequence gives `F(5x)=aF(x)` and `F(0)=0`.
At `x=n/5^M`, all later refinements append zero digits, so
`F(n/5^M)=C a^(-M) D_a(n)` exactly.
On `[1,5)`, the zeroth approximation lies between `C` and `4C`; the uniform error bounds
`F` above and below there. Scaling yields `c x^gamma<=F(x)<=A x^gamma`, with
`gamma=log(a)/log(5)`. This limit is the bilateral fractional-part profile: both are right
continuous and have the same values at the dense set of nonnegative base-five rationals.
Thus this construction also supplies a direct quantitative substitute for the earlier
qualitative compactness and Riemann-sum argument.

The unscaled statement is slightly stronger and is audited separately here. Set
`J_M(x)=a^(-M)D_a(floor(5^M x))` without the factor `C`. Its increment is
`a^(-M-1)r`, so the same geometric proof gives
`0<=sup_N J_N(x)-J_M(x)<=4*a^(-M)/(a-1)` for every `a>1`, with no upper bound on `a`.
For negative `x`, natural-number floor makes every row zero, so the estimate extends
to all real `x`. This is the exact statement of the current refinement draft.
Only the range `1<a<5` is identified above with the convergent fractional-part receiver;
the larger parameter range is a digit-conversion theorem, not an assertion of source
mean convergence. Its proof uses no additional analytic input or novelty claim.

## Strict escape: a bounded unnormalized error

Suppose `sqrt(5)<a<5`, hence `1/2<gamma<1`, and write `q=5^M`.
For fixed positive cofactors `j,k`, let `F_j(x)=F(x/j)` and `H_(M,j)(x)=H_M(x/j)`.
Both are nonnegative, and

`0<=F_j-H_(M,j)<=min(A j^(-gamma)x^gamma, B q^(-gamma))`.

The product difference is bounded above by
`(F_j-H_(M,j))*F_k + F_j*(F_k-H_(M,k))`.
Integrate against `dx/x^2`, splitting at `x=1/q`. The first part is bounded by a
constant times `q^(1-2gamma)/(2gamma-1)`. The second is bounded by a constant times
`q^(-gamma) integral_(1/q)^infinity x^(gamma-2)dx`, hence by a constant times
`q^(1-2gamma)/(1-gamma)`. All constants depend only on `a,j,k`.

The exact cell identity
`integral_(n/q)^((n+1)/q) dx/x^2=q/[n(n+1)]`, including the zero row below `1/q`, gives

`G_T(j,k)=(a^2/5)^M integral_0^tau H_(M,j)(x)H_(M,k)(x) dx/x^2`,

where `G_T` is the ordinary pronic covariance of `V_a=C D_a` and
`tau=(T+1)/q`. Since `(a^2/5)^M=q^(2gamma-1)`, the preceding error estimate proves

`0<=(a^2/5)^M integral_0^tau F_j(x)F_k(x)dx/x^2-G_T(j,k)<=C_(a,j,k)`.

This is uniform in both `M` and `T`; for the phase interpretation take
`5^M<=T<5^(M+1)`, so `1<=tau<=5`. The diagonal profile integral is bounded below
away from zero on this phase interval. Therefore the normalized Gram table differs from
its phase kernel by `O((5/a^2)^M)` at each fixed cofactor pair. No assertion about uniform
summation over arbitrary infinite kernels is made from this entrywise error bound.

## Critical boundary: logarithmic growth with bounded error

The same bounded-error statement has a direct annular formalization route
which avoids a global power-envelope estimate. On the fixed annulus
`1<=x<=5`, the profiles `F(x/j)` are bounded by one common compact bound
for all positive integer cofactors `j`. Uniform refinement gives
`0<=F_j F_k-H_(M,j)H_(M,k)<=C*a^(-M)`, with `C` depending only on `a`.
The exact step-cell embedding multiplies this annular error by
`q^M=(a^2/5)^M`; its unnormalized block cost is therefore at most
`C*(a/5)^M`. Since `a<5`, the sum of all block costs is finite, uniformly
in the final partial block and in the two positive cofactors.

For `5^M<=T<5^(M+1)` and `tau=(T+1)/5^M`, the exact main term is
`J(j,k)*sum_(m<M)q^m+q^M*A_tau(j,k)`. At criticality this is
`M*J(j,k)+A_tau(j,k)`. In the strict regime it equals
`q^M*(J(j,k)/(q-1)+A_tau(j,k))-J(j,k)/(q-1)`.
Thus the same summable annular error proves both advertised asymptotics.
Identifying the strict expression with the integral from zero still needs
the separate geometric-annulus integral identity. This derivation is a
proof plan, not a proved result; each comparison remains a Lean obligation.
The cofactor-uniform additive error cannot itself be summed against
arbitrary critical Wiener coefficients, whose unweighted absolute sum
need not converge.

The current compact-bound formalization draft is
`/tmp/BiarithmeticDigitProfileCompactBounds.lean`. It proves the proposed
pointwise bounds directly from the finite zeroth grid and its refinement
tail; no spatial monotonicity of weighted digits is assumed. The five
declared audits and all subsequent integral comparisons remain unchecked.

`/tmp/BiarithmeticDigitProfileAnnularIntegrals.lean` drafts measurable
profile convergence, finite mixed annular integrals, the base diagonal
lower bound `4/25`, and the cofactor-uniform partial-annulus error with
ratio `a/5`. It uses the compact-bound draft and the inspected bounded
integration/pointwise-limit interfaces. Four audits are drafted; unchecked.

`/tmp/BiarithmeticFinitePronicIntervalEmbedding.lean` drafts the finite
interval bridge using the corpus's frozen-cell integrability theorem and
exact pronic cell integral. It identifies arbitrary signed finite prefixes
and differences of prefixes with their real-interval integrals, without a
source growth assumption. Three audits drafted; unchecked. The scaled
digit specialization still requires its own equality.

`/tmp/BiarithmeticDigitAnnularStepComparison.lean` drafts that specialization:
floor cofactors commute exactly with the grid, and changing variables
identifies each scaled partial-annulus grid integral with the actual
finite covariance block. Two audits drafted; unchecked. The sum of the
annular error bounds and the resulting full-horizon asymptotics remain.

`/tmp/BiarithmeticDigitCovarianceBoundedError.lean` drafts the complete
finite error decomposition and geometric bound, uniformly in both
positive cofactors. It includes empty partial blocks through the exact
range `5^M<=N+1<=5^(M+1)`. The proposed bound is
`fiveDigitAnnularErrorBound(a)/(1-a/5)` for `1<a<5`. Three audits
drafted; unchecked. This is the quantitative finite source theorem;
strict/critical limits and actual golden transfer remain to be checked.

At `a=sqrt(5)`, work on the fixed annulus `1<=x<=5`. The same uniform refinement estimate
bounds each mixed annular covariance error by `C_(j,k) a^(-M)`. These errors are summable
in `M`. Since the scale factor `a^2/5` is one, every complete block contributes its fixed
annular integral plus that summable error. The final partial block is uniformly bounded.
Thus, with `M=floor(log_5 T)`,

`G_T(j,k)=M integral_1^5 F_j(x)F_k(x)dx/x^2+O_(j,k)(1)`.

The diagonal coefficient is positive. Hence the critical normalized Gram table has a
unique limit and error `O(1/M)`. This strengthens a mere Cesaro-limit argument while
keeping the exact ordinary-floor source normalization.

## Bounded cross terms in the positively damped golden source

For actual golden damping `0<t<1`, put `a=alpha*t`, `b=beta*t`, so
`ab=5t^2<5`. In the escape range `a>=sqrt(5)`, one has `1<a<5` and `0<b<sqrt(5)`.
On the block `5^M<=n<5^(M+1)`, for every positive cofactor the digit bounds give

`V_a(floor(n/j))<=C_a a^M`,
`V_b(floor(n/k))<=C_b sum_(r=0)^M b^r`.

The pronic block mass is `4/(5*5^M)`. Hence the absolute mixed energy is bounded by a
constant times

`sum_(M>=0) (a/5)^M sum_(r=0)^M b^r
 = 1/[(1-a/5)(1-ab/5)]`.

This uses nonnegative summation and two convergent geometric series; it also covers
`b=1` without a separate logarithmic estimate. The secondary-square contribution is
bounded because its source is critical Wiener. As the actual golden centered row is
`(V_a-V_b)/sqrt(5)`, every cofactor covariance differs from `G_T(j,k)/5` by a bounded
amount. Therefore the strict and critical estimates above hold for the actual source,
with the leading factor `1/5` cancelling in normalized kernels.

At `t=1`, the cross-term geometric ratio is one, so this bounded-error transfer is not
asserted. Equality of normalized tangent families there still follows from paid-perturbation
stability. The intrinsic generalized-integer counting model remains a separate construction.

## Verification and novelty scope

The uniform geometric refinement is classical digit-function machinery; no originality
claim is made. The programme use is the exact ordinary-pronic covariance error and its
transfer to the actual golden inverse-zeta coefficients.

- [x] Dependency-closed paper refinement, strict and critical errors, and golden cross-term bound.
- [ ] Lean refinement limit and quantitative profile comparison.
- [ ] Lean exact step embedding and covariance estimates.
- [ ] Lean actual-source transfer, direct checks, axiom audits, and umbrella imports.

The `DigitRefinement` scratch check and all nine transitive axiom audits
passed. Its production source is wired; the direct repository check is
queued. Subsequent compact bounds and annular comparisons remain unchecked.
