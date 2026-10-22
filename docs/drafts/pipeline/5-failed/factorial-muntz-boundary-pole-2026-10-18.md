# Naïve factorial Müntz null completion: polar obstruction

- **Stage:** 5-failed: only the naïve null-completion shortcut is retired; its positive survivor is formalized.
- **Mission:** unconditional RH in Lean through the actual WL/RW source framework.
- **Parent:** [actual ramp diagonal margin](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md).
- **Previous turn:** progress: exact actual polar-loss coefficient `1/4` and Gram-error separation were formalized in four leaves; all 27 public declarations passed standard-axiom audits. The coupled diagonal margin remains open.
- **Scope:** exact polar obstruction for the literal completion and its unique exponential repair. Existing Müntz seed/completion/tail sources are unchanged. The readout dependency required a narrow proof-only repair, recorded below. WL/RW and the parent diagonal-margin problem are not retired.

## Completed work

1. Read actual source definitions and search the whole corpus for summation, boundary and full-Weil mechanisms.
2. Prove an exact clamped-ramp summation formula with a bounded fractional-part remainder; derive the actual completion's boundary coefficient.
3. Classify polar integrability and prove the positive survivor: an explicit repaired source with genuine weighted integrability and an exact residual readout.
4. Formalize dependency-closed paper statements, audit every public declaration, wire finished leaves, run index/lint and remove owned temporary caches.

## Verified obstruction and positive survivor

The current source proves `factorialMuntzCompletion n x = exp(x/2) * factorialMuntzSum n (exp x) / sqrt(N)`, `N=n+1`. The completion agrees exactly with the ramp for `x>=0`; its negative tail has squared mass at most `100/N`. Its Mellin readout vanishes at every zeta zero with positive real part. These statements alone do not establish a full-Weil null-source identity.

The concrete seed is the `(1,-4,4)` combination of positive clamped ramps at scales `4N,2N,N`. Its integral is zero, but its value immediately to the right of zero is one.

Exact finite summation mechanism: for `R(y)=sum_{k>=1} max(y-k,0)` and `y>=0`, put `r=y-floor(y)`. Then

`R(y)=(y^2-y)/2 + r*(1-r)/2`, with `0<=r*(1-r)/2<=1/8`.

For `a,epsilon,t>0`, the infinite clamped-ramp sum is

`S(a,epsilon,t)=t/(a*epsilon) * [R(a*(1+epsilon)/t)-R(a/t)]`.

Consequently its deviation from `a*(1+epsilon/2)/t-1/2` is at most `t/(8*a*epsilon)`. The actual dyadic combination cancels the entire `1/t` term and retains the constant `-1/2`; the proved bound is

`|factorialMuntzSum n t + 1/2| <= 25*t/(32*N*sourceFactorialCollar N)`.

Therefore `exp(-x/2)*factorialMuntzCompletion n x -> -1/(2*sqrt(N))` as `x->-infinity`, and the uncorrected negative pole moment is not integrable. The unique correction within the exponential coefficient family is `1_{x<=0}*exp(x/2)/(2*sqrt(N))`. The proved error bound makes the corrected negative weighted tail integrable, with an explicit exponential envelope. Both weighted moments exist for this correction, and its readout at every right-half-plane zeta zero is exactly the nonzero value `1/(2*sqrt(N)*rho)`.

The dependency-closed paper proof below is formalized in Lean. All 24 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. No full-Weil sign or RH claim follows from this boundary audit.

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

## Lean verification and no-go closure

The [positive-survivor card](../3-formalized/factorial-muntz-boundary-repair-2026-10-18.md) contains the exact theorem family and a self-contained paper proof. Its three leaves, `ClampedRampLatticeSum.lean`, `FactorialMuntzBoundaryPole.lean`, and `FactorialMuntzBoundaryRepair.lean`, passed direct checks with `lake --old env lean -j 1` and are wired into the area umbrella. They contain 18 new public theorems and five definitions. The complete axiom audit passed for all 23 new declarations plus the repaired existing theorem, using only the three standard axioms above.

The necessary tail dependency passed unchanged. The readout dependency passed after two type annotations in `factorialRamp_zeta_readout` aligned its integrability facts with the private kernel used by `integral_sub`. An exact before/after comparison confirms no statement or other proof changed. Four scratch API/analytic probes passed. The new-leaf logs retain only tactic-style warnings.

`scripts/formal_tools.py index` passed. `lint --check-generated` returned 1 because two unrelated modules are unreachable from their umbrellas: `BiScaleUncertainty.StationaryResolventMarkovPositivityAndNodalDefectProducer` and `BezoutValuationIncidence.PrimeTailCalibrationAndMobiusDefect`. No error concerns these changes. The log also contains 381 large-file warnings. No unrelated module was edited to silence this gate.

Verification record: `/tmp/bsu-muntz-boundary-verification.json`; audit log: `/tmp/bsu-muntz-boundary-axioms.log`; gate logs: `/tmp/bsu-muntz-index.log` and `/tmp/bsu-muntz-lint.log`. Checks used a pinned snapshot of 8,670 existing dependency objects, including six fallback objects and 133 pre-existing objects older than their source timestamps. No dependency source changed during verification. This is not a fresh whole-tree build. All owned source hashes and object freshness checks passed; all three import counts equal one. The owned snapshot was removed after verification. Its saved setup maps are archival and must not be reused without rebuilding the cache.

The negative conclusion is closed together with its nontrivial positive survivor: exact boundary coefficient, unique polar-integrable exponential correction, and exact nonzero rational zero readout. Full-Weil admissibility, passage back to the compact ramp, the coupled diagonal margin, and RH remain open.

## Corpus status

- `/tmp/bsu-coupled-diagonal-search-20261018.json`: partial reranking result (deadline expired). All 20 candidate lemmas and 20 source-argument hits were inspected. Current exact diagonal, Gram estimates and Müntz-tail results are applicable; generic archimedean producers and other literal source families do not supply the missing coupled estimate.
- Direct source search found the arithmetic-summation Mellin identities in `RHTower/CCM/CCMBVMuntzSummation.lean`, but no existing arithmetic-sum endpoint limit under the searched names.
- `/tmp/bsu-muntz-boundary-search-20261018.json` also returned partial reranking results. All 20 candidate and 20 source-argument hits were inspected. Generic Euler–Maclaurin results require differentiable towers not satisfied at the literal clamp corners; their summation ideas support the direct finite positive-part calculation above. Neither search measured semantic coverage; both background refreshes were incomplete. No exhaustive-search or external-novelty claim.
