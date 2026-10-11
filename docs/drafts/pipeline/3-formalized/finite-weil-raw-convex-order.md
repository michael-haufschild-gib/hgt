# Finite Weil raw convex order

Status: dependency-closed paper argument; Lean verification in progress.

Only local Lean corpus and installed Lean dependencies. No external sources or numerics.
Prior raw-transport metadata is fresh. Local convex-order and convex-coupling searches
provide no applicable theorem for these finite laws. Mathlib supplies one-sided
derivatives of arbitrary real convex functions, their monotonicity and secant bounds.

Put A=k+2,n=r+1,X_i=i-E,Y_i=n(T_i-Q), and F(x)=A(1-A(log(A+x+1)-log(A+x)))-x.
For nonnegative x, F'(x)=A^2/((A+x)(A+x+1))-1 lies in [-1,0]. Thus F is decreasing
and G(x)=F(x)+x is increasing. On canonical indices, Y is increasing and X-Y is
increasing. Both X and Y have weighted mean zero, hence E[X-Y]=0.

For a globally convex real function phi, let d(y) be its right derivative. Local
Lean secant lemmas imply d is increasing and
phi(x)-phi(y) >= d(y)(x-y), including nondifferentiable phi.
The sequences d(Y_i) and X_i-Y_i are both increasing. Weighted Chebyshev gives
E[d(Y)(X-Y)] >= E[d(Y)] E[X-Y] = 0. Summing the supporting inequalities yields
E[phi(Y)] <= E[phi(X)]. This is finite convex order for every r,k, not merely a limit.

Weighted Chebyshev follows from the exact pairwise covariance identity:
sum_ij p_i p_j (a_i-a_j)(b_i-b_j) = 2(E[ab]-E[a]E[b]).
Every summand is nonnegative for two ordered sequences and nonnegative probabilities.

Planned closure: ordered raw variables and zero means; weighted covariance identity;
global convex right-derivative support; finite-sum and actual-integral convex-order roots;
unconditional even-moment, variance and exponential-moment consequences; native leaf
checks, native axiom audit, umbrella wiring, local index and lint.

Final roots have only structural parameters and typed observables. Coupling optimality
and equality of primal/dual transport values are separate, unproved questions here.


## Verified closure — 2026-10-11

Status: FORMALIZED. This closes the finite convex-order increment; the overarching research goal remains active.

For every natural rank r and shift k, put n = r + 1, X_i = i - E[i], and
Y_i = n(T_i - E[T]), with the existing canonical edge probability masses.
The actual probability law of Y lies below that of X in convex order:
E[phi(Y)] <= E[phi(X)] for every real convex phi, including nonsmooth phi.
No quadratic-width or asymptotic premise is required.

Dependency-closed paper proof: the existing residual profile F satisfies
F(i) = n T_i - i and F'(x) = A^2 / ((A+x)(A+x+1)) - 1 for A = k+2 and x >= 0.
Thus F is decreasing and F+x is increasing. Both Y and X-Y are increasing
in the index, and both X and Y have mean zero. The right derivative of a
globally convex real function is increasing and supplies a supporting
slope. Weighted Chebyshev gives E[phi'_+(Y)(X-Y)] >= 0. Summing the
supporting inequalities proves the asserted comparison. The covariance
step follows from the exact two-copy identity
sum_ij p_i p_j (f_i-f_j)(g_i-g_j) = 2(E[fg]-E[f]E[g]).

Lean roots:

- `WeilLogShiftRawConvexOrder.finiteWeilCanonicalRaw_convex_sum_le` and
  `finiteWeilCanonicalRaw_convex_integral_le` (namespace `RHTower`).
- `WeilLogShiftRawConvexMoments.finiteWeilCanonicalRaw_even_moment_le`:
  every even moment of Y is bounded by that of X.
- `finiteWeilCanonicalRaw_variance_le`: n^2 Var(T) <= Var(i), every r,k.
- `finiteWeilCanonicalRaw_exponential_moment_le`: E exp(aY) <= E exp(aX)
  for every real a, every r,k.

The module prefixes above identify source files, not extra Lean namespaces.
Support is in `WeilLogShiftRawOrder`, `WeilLogShiftLawCovariance`, and
`WeilLogShiftConvexRightSupport`. All five leaves are imported once by the
RHTower umbrella. Native leaf builds exited 0 with empty logs; native final
scratch audit checked all 17 public theorems and 21 API witnesses.
Every theorem uses only propext, Classical.choice, and Quot.sound.
Metadata found no issues: 10 direct imports, 9 incoming import edges,
fresh objects, unique declarations, and clean source whitespace.
Scoped git diff --check passed. Local lexical indexing returned all three
requested principal roots and both companion roots, all from Lean files.

Global lint at this checkpoint: 11 errors and 367 warnings,
all outside the five new leaves. Exact diagnostics remain in
`/tmp/hgt-raw-convex-lint.log`; the global gate is not clean.

Artifacts: `/tmp/hgt-raw-convex-{api.lean,api.log,metadata.py,metadata.json,
declarations.json,incoming-imports.txt,final-audit.lean,final-audit.log,
roots-search.json,lint.log,close.py}` and one native log per leaf.
Only the local Lean corpus and installed Lean dependencies supplied
mathematical evidence. No web searches, external papers, or numerics.
Transport optimality and equality of the raw gap with Wasserstein distance
remain separate questions; no such equality is claimed here.
