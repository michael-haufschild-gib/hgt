# Actual factorial Müntz completion: boundary pole and repair

- **Stage:** 1-in-progress.
- **Mission:** unconditional RH in Lean through the actual WL/RW source framework.
- **Parent:** [actual ramp diagonal margin](factorial-ramp-diagonal-margin-2026-10-18.md).
- **Previous turn:** progress: exact actual polar-loss coefficient `1/4` and Gram-error separation were formalized in four leaves; all 27 public declarations passed standard-axiom audits. The coupled diagonal margin remains open.
- **Scope:** audit the actual completion's polar endpoint; prove its exact boundary behavior and, if obstructed, construct and prove the canonical nontrivial repair. Existing Müntz completion/tail sources remain read-only. The readout dependency required a narrow proof-only repair after its direct check failed; the exact exception is recorded below.

## Plan

1. Read actual source definitions and search the whole corpus for summation, boundary and full-Weil mechanisms.
2. Prove an exact clamped-ramp summation formula with a bounded fractional-part remainder; derive the actual completion's boundary coefficient.
3. Test polar integrability. If the null-completion shortcut fails, prove the positive survivor: an explicit repaired source with genuine weighted integrability and an exact residual readout.
4. Formalize dependency-closed paper statements, audit every public declaration, wire finished leaves, run index/lint and remove owned temporary caches.

## Current evidence and conjectures

The current source proves `factorialMuntzCompletion n x = exp(x/2) * factorialMuntzSum n (exp x) / sqrt(N)`, `N=n+1`. The completion agrees exactly with the ramp for `x>=0`; its negative tail has squared mass at most `100/N`. Its Mellin readout vanishes at every zeta zero with positive real part. These statements alone do not establish a full-Weil null-source identity.

The concrete seed is the `(1,-4,4)` combination of positive clamped ramps at scales `4N,2N,N`. Its integral is zero, but its value immediately to the right of zero is one.

Candidate finite summation mechanism: for `R(y)=sum_{k>=1} max(y-k,0)` and `y>=0`, put `r=y-floor(y)`. Then

`R(y)=(y^2-y)/2 + r*(1-r)/2`, with `0<=r*(1-r)/2<=1/8`.

For `a,epsilon,t>0`, the infinite clamped-ramp sum is

`S(a,epsilon,t)=t/(a*epsilon) * [R(a*(1+epsilon)/t)-R(a/t)]`.

Consequently its deviation from `a*(1+epsilon/2)/t-1/2` is at most `t/(8*a*epsilon)`. The actual dyadic combination cancels the entire `1/t` term and retains the constant `-1/2`; the resulting proposed bound is

`|factorialMuntzSum n t + 1/2| <= 25*t/(32*N*sourceFactorialCollar N)`.

This would imply `exp(-x/2)*factorialMuntzCompletion n x -> -1/(2*sqrt(N))` as `x->-infinity`, so the uncorrected negative pole moment cannot be absolutely integrable. The candidate correction is `1_{x<=0}*exp(x/2)/(2*sqrt(N))`. The proposed error bound makes the corrected negative weighted tail integrable, with an explicit exponential envelope.

The dependency-closed paper proof follows. Lean verification remains pending. No full-Weil sign or RH claim follows from this boundary audit.

## Dependency-closed paper proof

For `y>=0`, let `m=floor(y)` and `r=y-m`. All terms of `R(y)` with `k>m` vanish, while terms `1<=k<=m` equal `y-k`. Hence `R(y)=m*y-m*(m+1)/2`. Substituting `m=y-r` proves the displayed quadratic identity. Since `0<=r<1`, `0<=r*(1-r)/2<=1/8`; the upper bound follows from `(r-1/2)^2>=0`.

The clamp identity is pointwise:

`clampedRamp(epsilon,v)=[max(1+epsilon-v,0)-max(1-v,0)]/epsilon`.

Its three cases are `v<=1`, `1<=v<=1+epsilon`, and `1+epsilon<=v`. For `a,t>0`, factor `t/a` out of each positive part and sum. Each sum has finite support, so subtraction and multiplication commute with the sums without convergence assumptions. The two quadratic terms simplify to `a*(1+epsilon/2)/t-1/2`; the residual is

`t/(a*epsilon) * [delta(a*(1+epsilon)/t)-delta(a/t)]`,

where `delta(y)=(y-floor(y))*(1-(y-floor(y)))/2`. Its absolute value is at most `t/(8*a*epsilon)`.

At every positive sampling point the actual seed is the exact `(1,-4,4)` clamp combination. Its component sums are finite. The three main terms cancel by `4N-4*(2N)+4*N=0`, while their constants sum to `-1/2`. The sum of the absolute error bounds is

`t/(8*epsilon) * [1/(4N)+4/(2N)+4/N] = 25*t/(32*N*epsilon)`.

Thus the proposed bound for the actual `factorialMuntzSum` is proved on paper. Multiplying the completion by `exp(-x/2)` and setting `t=exp(x)` gives

`|exp(-x/2)*F_n(x)+c_N| <= K_N*exp(x)`,

with `c_N=1/(2*sqrt(N))>0` and `K_N=25/(32*N*epsilon*sqrt(N))`. Since `exp(x)->0` at negative infinity, the exact boundary coefficient is `-c_N`.

For real `c`, define `F_(n,c)(x)=F_n(x)+1_{x<=0}*c*exp(x/2)`. On the negative half-line the negative weighted moment at `c=c_N` is bounded in absolute value by `K_N*exp(x)`, an integrable function. On the positive half-line it equals the weighted compact ramp. Thus the whole negative weighted moment is integrable at this coefficient. The positive weighted moment is also integrable: use the existing completion readout integrability at real `s=1` and the elementary exponential counterterm integral.

Uniqueness is exact. The difference of the negative weighted sources at coefficients `c` and `c_N` is `(c-c_N)*1_{x<=0}`. A constant on a Lebesgue half-line is integrable exactly when it is zero. Subtracting the already integrable corrected source proves

`Integrable(exp(-x/2)*F_(n,c)(x)) iff c=c_N`.

In particular the uncorrected completion (`c=0`) is not polar-integrable. This rules out treating its zeta-zero readout vanishing and small L2 tail as a full-Weil null-source certificate.

For every complex `s` with `Re(s)>0`, both the existing completion readout and counterterm readout are absolutely integrable. The latter is

`integral_{x<=0} c*exp(s*x) dx = c/s`.

Therefore the exact corrected readout is the existing completion Mellin readout plus `c/s`. At every right-half-plane zeta zero `rho`, it equals `c/rho`. The unique coefficient admitting the negative polar moment is `c_N>0`, so its residual `c_N/rho` is nonzero. This is the positive survivor: a unique explicit polar correction, genuine weighted integrability, and an exact universal residual readout. Full-Weil regularity and the coupled diagonal estimate remain separate open obligations.

## Lean implementation scope

Planned new leaves: `ClampedRampLatticeSum.lean`, `FactorialMuntzBoundaryPole.lean`, and `FactorialMuntzBoundaryRepair.lean` under `formal/GaloisForLFunctions/BiScaleUncertainty/`. Existing completion/tail/readout and unrelated research files remain unchanged. The area umbrella and this task's pipeline cards may be updated after verification.

All three new leaves are written. `ClampedRampLatticeSum.lean` and `FactorialMuntzBoundaryPole.lean` passed their direct checks. The boundary log has only one tactic-style warning. Three scratch API probes passed. A normal-cache boundary check was blocked by a missing transitive object being rebuilt by another session. An owned snapshot at `/tmp/bsu-muntz-boundary-cache` pins existing dependencies; its manifest records six fallback objects and pre-existing objects older than their source timestamps. The generated axiom audit covers all 23 new public declarations (18 theorems, five definitions) plus the existing dependency theorem repaired below; repair and audit passes remain pending. Logs and setup maps use the `/tmp/bsu-muntz-` and `/tmp/bsu-FactorialMuntz` prefixes. Other sessions' builds remain untouched; the sole existing-source edit is the necessary two-annotation readout repair below.

The [positive-survivor card](../2-fully-proven/factorial-muntz-boundary-repair-2026-10-18.md) now carries a self-contained paper proof and explicit verification status. It stays at paper-proven stage until the repair and complete axiom audit pass.

The unchanged tail dependency passed with no diagnostics. The readout dependency failed at `factorialRamp_zeta_readout` because `integral_sub` received integrability facts with an expanded kernel while the goal used the private kernel definition. Its source hash was unchanged since the precheck, and no other Lean process was checking that file. Two type annotations on those facts fix the mismatch; the before/after diff contains no statement or other proof change. `/tmp/bsu-check-muntz-readout-repair.zsh` rechecks this dependency and then the new repair leaf. The final audit now includes this repaired existing theorem, for 24 declarations total (23 new plus one repaired).

The second clamp check exposed an explicit natural-order conversion (`k<m` to `k+1<=m`), now discharged by `omega` before casting. `FactorialMuntzBoundaryRepair.lean` is also written, with the exact coefficient classification and rational readout. Its extra API probes are prepared in `/tmp/bsu-muntz-repair-api.lean` but not yet run. The normal-cache object for the existing `FactorialMuntzReadout.lean` dependency is absent; necessary dependency checks will be sequential and will not edit the concurrent source files.

## Corpus status

- `/tmp/bsu-coupled-diagonal-search-20261018.json`: partial reranking result (deadline expired). All 20 candidate lemmas and 20 source-argument hits were inspected. Current exact diagonal, Gram estimates and Müntz-tail results are applicable; generic archimedean producers and other literal source families do not supply the missing coupled estimate.
- Direct source search found the arithmetic-summation Mellin identities in `RHTower/CCMBVMuntzSummation.lean`, but no existing arithmetic-sum endpoint limit under the searched names.
- `/tmp/bsu-muntz-boundary-search-20261018.json` also returned partial reranking results. All 20 candidate and 20 source-argument hits were inspected. Generic Euler–Maclaurin results require differentiable towers not satisfied at the literal clamp corners; their summation ideas support the direct finite positive-part calculation above. Neither search measured semantic coverage; both background refreshes were incomplete. No exhaustive-search or external-novelty claim.
