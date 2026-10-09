# Exact open and closed potential domains

Status: [FORMALIZED; GLOBAL LINT HAS ONE UNRELATED UMBRELLA ERROR]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Objective and plan

Classify the geometry forced on a real-shift convergence domain and realize
arbitrary finite open or closed symmetric intervals with nonnegative weights.
Use a polynomially damped reciprocal kernel to settle the constructed boundary
exactly, without claiming an endpoint result for pure exponential weights.

1. Audit prior domain/rate results and reciprocal constructions. Done: the
   existing reciprocal construction is a diagonal all-sample divergence device;
   it does not give the interval domains sought here.
2. Prove paired-kernel evenness and convergence transfer for |y|<=|c|, then
   interval closure for arbitrary signed weights.
3. Define P_c(n)=K(c+log n)+K(c-log n)>0 and
   v_{p,c}(n)=1/((n+1)^p*P_c(n)), p a natural number.
4. Prove exact domain:
   sum v_{p,c}(n)P_y(n) converges iff |y|<|c|, or |y|=|c| and p>1.
   Extract nonnegative realizations of (-R,R) and [-R,R], including empty
   domain at R=0,p=0 and singleton domain at R=0,p=2.
5. Compile/export, audit all public declarations, wire/index/lint, promote,
   save memory, clean owned scratch.

## Dependency-closed paper proof

P_{-c}=P_c by evenness of K. Equal absolute shifts therefore give identical
terms. The already formalized strict inward transfer extends to weak absolute
inequality. If two shifts converge, every intervening shift has absolute value
at most the larger endpoint's absolute value and converges too. Thus every
convergence domain is symmetric and an interval (possibly empty/unbounded).

The critical rate r(c)=2*pi*exp(-|c|) strictly decreases with |c|. If |y|<|c|,
choose r(c)<b<a<r(y). Existing envelopes give eventually

 P_y(n)<=C exp(-a*n),   P_c(n)>=D exp(-b*n),   C,D>0.

Their ratio is bounded by (C/D)exp(-(a-b)*n), hence summable. Since
1/(n+1)^p<=1, every polynomially damped reciprocal weight converges inside.

At |y|=|c| the weighted kernel is exactly 1/(n+1)^p, whose series converges
exactly when p>1 by the installed p-series theorem.

If |c|<|y| and the weighted potential were summable at y, choose b strictly
between r(y) and r(c). The necessary local growth theorem gives v_{p,c}(n)
<=M exp(b*n). Choose a with b<a<r(c); the kernel upper bound at c gives
P_c(n)<=C exp(-a*n). Multiplying these inequalities and the defining identity
(n+1)^p*v_{p,c}(n)*P_c(n)=1 yields

 1 <= M*C*(n+1)^p*exp(-(a-b)*n)

for all n>=1. The right side tends to zero by the existing polynomial versus
exponential limit theorem, a contradiction. This handles every p, including
p=0 and the singleton-domain construction.

No pure-exponential critical endpoint, RH statement, or new analytic premise
is asserted. The precise boundary behavior is created by the reciprocal weight.

## Corpus audit

Direct lexical search in Weil modules: 2946 declarations, 628 modules, 1038
eligible entries; cached output has no partial/coverage fields. Relevant hits:
strict inward transfer, local upper/lower exponential rates, necessary growth,
and whole-line subexponential equivalence. The existing reciprocal construction
in WeilLogShiftConvergenceNoGo builds all-sample divergence, not interval domains.
The p-series shift proof is already used in SparseUnboundedMultiplicityCanonicalProduct.
All new library names were checked in a scratch import of this toolchain.

## Verification

- Required library names were checked in a scratch import.
- `WeilLogShiftDomainBoundary.lean` compiled/exported directly with
  `lake --old env lean <leaf> -o <local olean>`; final exit 0, no diagnostics.
- Eleven public declarations cover the paired kernel, interval closure, the
  reciprocal weights, their exact domain, and both endpoint realizations.
- All eleven public declarations passed scratch `#print axioms`; only
  `propext`, `Classical.choice`, and `Quot.sound` occur.
- Umbrella import added. Index refresh succeeded and all eleven public API rows
  were inspected. Scoped `git diff --check` passed.
- Global formal lint exited 1 on one unrelated module unreachable from its
  umbrella: `RHTower.CCMRiemannKernelBartaLayerBounds`. Its source/import were
  not modified. The three preceding umbrella errors no longer occur.
- All owned jobs exited. Owned `/tmp/hgt-weil-potential-domain-*` scratch files
  were removed after recording evidence. No numerical experiments, new axioms,
  unproved analytic inputs, heartbeat increases, full/umbrella builds, commits,
  or subagents.

All scoped proof steps are formalized. The exact new insight is that reciprocal
normalization fixes any convergence radius while a polynomial factor independently
controls inclusion of the boundary. Domain symmetry and interval closure hold
for arbitrary signed coefficients; both endpoint behaviors already occur for
nonnegative coefficients. Radius zero shows that convergence only at the origin
is possible and does not force convergence at any nonzero shift.

## Follow-up: shrinking-window endpoint proof

The proposed refinement is now formalized in `WeilLogShiftCriticalEndpoint.lean`.
A full-autocorrelation central interval of radius d=exp(-z), with no cutoff
factor, and the chord bound exp(2d)<=1+(exp(2)-1)*d give
K(z)>=D*exp(-z)*exp(-2*pi*exp(z)) for z>=0. At log n-|y|, critical exponential
weighting leaves a harmonic lower bound. Thus pure exponential weights converge
exactly below the critical rate and diverge at equality as well as above it.
See `weil-logshift-critical-endpoint.md` for that proof and its audit evidence.
