# Positive averages with a growing frozen Möbius prefix

Original [R] and arithmetic power candidate [G] remain unchanged and open.
The target here is the actual full L² norm of a positive average of raw
residuals R_j=q+Σ_(k≤j)μ(k)h(kt), not cancellation of finitely many zero phases.

**Hard source statement.** Produce probabilities α_(j,N)≥0, Σ_j α_(j,N)=1,
with ||Σ_j α_(j,N)R_j||₂→0. The resulting coefficients
a_(k,N)=μ(k)Σ_(j≥k)α_(j,N) lie in the unit box. A support restriction j≥M
freezes every coefficient through M exactly to μ; it addresses chronological
repair without imposing coordinatewise convergence as an unproved theorem.

**Frozen finite diagnostic [H-test].** At N=512,2048,8192, optimize over every
integer cutoff j∈[M,N], for M=1,N/64,N/16,N/4,N/2 (integer floors).
Compare retained actual full residual norms and positive cutoff distributions.
All searches retain nonnegative simplex vectors and report optimizer failure
without interpreting it as infeasibility. Use independent shifted quadrature,
both endpoint tails and 80-digit residual checks. Compare the nested feasible
sets: narrowing the cutoff interval cannot improve the true minimum. Correct
solver failures by retaining valid candidates from narrower windows. All
numerical mathematics runs on the authorized Runpod, with multicore Python;
no computation enters Lean.

This probes whether the previous tiny averages rely on retaining a fixed
early portion of the arithmetic history. It does not settle whether bounded
multiplicative window width can ever support asymptotic convergence, nor
whether a growing width suffices. No such theorem is presumed.

## Analytic attacks and exact gaps

1. Arithmetic power weights have positive full divisor sums
   b_ε(n)=Σ_(d|n)μ(d)d^(−ε)=∏_(p|n)(1−p^(−ε)) for n≥1.
   For ε>0 the pointwise infinite residual is
   [ζ(1+ε)t]⁻¹−Σ_(n≥2)b_ε(n)exp(−nt).
   Positivity of b does not control its discrepancy from the continuous
   density. Direct absolute divisor estimates lose the required half exponent.
   Mellin continuation introduces ζ(s)/ζ(s+ε); treating its boundary expression
   as the transform of an actual L² function already needs justification.

2. The reflected quotient ζ(1/2−ε+iτ)/ζ(1/2+ε+iτ) has an unconditional
   functional-equation bound. This does not prove that the corresponding
   arithmetic truncations converge in L². In
   [Báez-Duarte's proof](https://arxiv.org/pdf/math/0205003), RH supplies that
   membership step before the reflected quotient is used. The current heat
   argument has the same unresolved order-of-limits issue.

3. A positive distribution in log cutoff can annihilate finitely many scalar
   zero phases. The actual Mellin remainder depends on ρ−s for an entire
   vertical line, so annihilation at ρ−1/2 alone supplies no full norm bound.
   Averaging after a cutoff-dependent rescaling changes the target and the
   allowed integer dilations; it is not a construction for [R].

4. Local convergence and slow variation of the raw sequence are insufficient
   compactness inputs. A concentration profile can escape toward t=0 while
   remaining separated from zero in the closed convex hull. A source estimate
   must rule out that concentration quantitatively. No new general compactness
   theorem is claimed; the literal arithmetic covariance remains the problem.

No RH proof, new asymptotic estimate, or route retirement is claimed.

## Independently frozen follow-up [J-test]

At N=8192 with M=4096 frozen coefficients, compare the positive-average family
with (i) arbitrary sign-preserving unit weights on squarefree tail indices,
(ii) signed unit weights on those indices, and (iii) the full unit box.
Prediction frozen before running: removing monotonicity while preserving
Möbius signs permits error ≤1e−8 at this finite cutoff. Keep this numerical
prediction separate from [H-test], [G] and [R]; a failure does not change it.
Retain feasible incumbents across the nested families, independently validate
the actual full norm, and do not interpret an optimizer failure as a lower bound.
