# SZ: closed two-leg Gamma synthesis and its exact finite-row boundary domain

Status: formalized. Paper proof, four direct Lean audits, and dependency audits complete. Repository-wide lint has unrelated wiring failures, listed below.

## Structural contribution

The literal two-leg deattenuated causal-depth Gamma source has a canonical **closed, densely defined, necessarily unbounded synthesis operator**. Every finite source column and every polarized finite Gamma energy pairing is preserved exactly. No source-admissibility premise is inserted.

The obstruction on finite Gamma tests is classified exactly. Put

`d(0)=1`, `d(k+1)=k+3`, `c_k=JacobiNormalization(d(k))`.

For a finite complex family `alpha_k`, the row

`pe ↦ sum_k alpha_k * twoLegColumn(pe)(k)`

has a Hilbert source representative **if and only if**

`sum_k alpha_k * c_k = 0`.

Equivalently, the finite Gamma polynomial `P(r)=sum_k alpha_k*c_k*r^d(k)` must vanish at `r=1`. This is an exact domain theorem for the actual prime-depth coefficients, together with an unconditional closed realization of their synthesis.

## What obstruction is removed

`SuzukiCausalDepthGammaTwoLegSourceNormalGraphDomainNoGo` proves that the canonical multiplier is exactly `p`, and that the resulting amplitude family cannot satisfy the old square-summable graph-admission predicate. Bounded and trace-class realizations cannot recover the present column family either.

Adjacent Gamma-row cancellation supplies a non-diagonal closed graph for those unchanged columns. Its zero vertical kernel is proved. This resolves the closed-realization obstruction without requiring the forbidden amplitude vector to become square-summable. The old amplitude-admission predicate remains false.

The theorem concerns the causal-depth Gamma sector. The completed signed Robin/Ward comparison, moving-source Wronskian law, and passage to unshifted Xi remain open. No RH equivalence, RH proof, or full signed-source positivity claim is made.

## Dependency-closed paper proof

Write `pe=(p,e)`, `r_pe=tanh(log(p^(e+1))/2)`, and `phi_pe=cosh(log(p^(e+1))/2)^(-1/2)`. The actual column is

`b_k(pe)=p * weight(h,a,pe) * phi_pe * c_k * r_pe^d(k)`.

The original weights have square-summable squares over every prime and depth.

### 1. Adjacent cancellation

Define `R_k=c_(k+1)*b_k-c_k*b_(k+1)`. Its exact factorization contains

`p * (1-r_pe)`,

with one additional factor `1+r_pe` when `k=0`. Since `p*(1-r_pe) <= 2`, every `R_k` is a square-summable source row. This summability is used to build continuous graph equations; the estimate is not the contribution.

### 2. Closed synthesis without a domain premise

On source/output pairs impose zero output in the unused arithmetic sector and

`c_(k+1)*output(k)-c_k*output(k+1)=inner(R_k,input)`.

Each equation is continuous, so their common solution relation is closed. A vertical solution has coordinates `output(k)=z*c_k`. But `c_k^2` is a surviving normalized central binomial coefficient, and these squares are not summable. Therefore `z=0`: the relation has no vertical ambiguity.

Take the closure of the linear span of all literal basis/column pairs. It lies in that relation, so it is the graph of a closed linear partial map. Every coordinate input belongs to its domain; the domain is dense. Finite packets form its graph core by construction.

The exact kernel is retained:

`inner(twoLegColumn(pe),twoLegColumn(qe)) = p*q*GammaSchurKernel(h,a,pe,qe)`.

Bilinearity gives the corresponding exact double-sum identity for every pair of finite complex packets, including every mixed term.

### 3. The realization must be unbounded

For `C_h=(h*sqrt(h))^-1`, the first surviving coordinate at depth zero satisfies

`|b_0(p,0)|^2 = C_h^2*log(p)*[p/(p+1)]^2*[(p-1)/(p+1)]^2*[1-disk((h/2)*a,p)]^4/(p+1)`.

The disk factor tends to zero before subtraction. Consequently this square dominates a positive multiple of `1/p` eventually. Prime-harmonic divergence excludes a Hilbert representative of the first row. A bounded realization would supply such a representative through its adjoint applied to the first Gamma coordinate. Hence no bounded extension exists.

### 4. Exact finite-row boundary classification

Set `W_0=0` and

`W_(k+1)=(c_(k+1)/c_k)*W_k-(c_0/c_k)*R_k`.

Every `W_k` is a Hilbert vector and has exact coordinates

`W_k=c_0*b_k-c_k*b_0`.

For a finite family, set `B=sum_k alpha_k*c_k`. Then

`c_0*sum_k alpha_k*b_k - B*b_0 = sum_k alpha_k*W_k`.

If `B=0`, the right side divided by `c_0` is the required Hilbert representative. If `B` is nonzero, any such representative would produce a Hilbert representative of `b_0`, contradicting step 3. This proves both directions, with no missing source premise.

## Lean artifacts

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalDepthGammaBoundaryCancellation.lean`: actual columns, boundary coefficients, nonsummable homogeneous mode, square-summable adjacent rows.
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalDepthGammaClosedSource.lean`: canonical graph closure, single-valuedness, closedness, dense domain, exact finite packets and Gram kernel.
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalDepthGammaUnboundedSource.lean`: actual inverse-Wold source-normal coordinate identity, first-row divergence, no bounded extension, and fixed premise-free theorem `suzukiGammaCanonicalTwoLegSource_closed_dense_unbounded` at `h=a=1`.
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalDepthGammaFiniteRowBoundary.lean`: exact Hilbert-row criterion `suzukiGammaFiniteRow_hilbert_iff_boundary_zero` and fully polarized finite-packet identity.

All four modules are wired into `formal/GaloisForLFunctions/RHTower.lean`.

## Conjecture–failure–learning record

1. Eventual positivity of actual critical correlations: **false in the corpus** (`MobiusDivisorCriticalCorrelationTailSign`, `MobiusDivisorCriticalFiniteCorrelationSign`). Signed products must be retained.
2. Completion from exhaustive checkpoints plus terminal insertion order: **circular**. The completed source square remains an unpaid endpoint (`MobiusDivisorExhaustiveClockCheckpoints`, `MobiusDivisorTerminalClockOrder`).
3. Retained-prime linear-cone or fixed finite-field inward selection: **already present**, so it does not advance this task. Existing `RetainedPrimeLandauSeparation`, `RetainedPrimeFiniteSourceMargin`, `RetainedPrimeBoundedBatches`, and positive-debt constructions were not repackaged.
4. Normalized unitary orbit lifts: **insufficient for the requested obstacle**. Finite covariance limits alone do not resolve original-cutoff source cancellation. No Lean module was written for this candidate.
5. Literal two-leg Gamma synthesis may be closable despite amplitude non-summability: **proved**, using adjacent-row cancellation and the nonsummable homogeneous Jacobi mode.
6. That realization may still be bounded: **disproved** by the actual first Gamma row. Positive survivor: a concrete closed, dense, necessarily unbounded source.
7. Finite source-row admissibility is exactly one Jacobi boundary condition: **proved**, through the explicit correction recurrence. This sharp classification strengthens the original closability construction.

## Verification and limits

Each of the four modules passed a foreground, direct `lake --old env lean -j 1 -o <build-artifact> <module>.lean` audit. No full or umbrella build was run. No heartbeat limit was raised. No numerical experiment, web search, or external novelty audit was used.

Corpus searches used names, statements, proof bodies, and source arguments. Some hybrid searches returned partial results or source-only compiler coverage; candidate facts were checked against Lean source and the final toolchain. Search coverage is not represented as an exhaustive novelty claim.

`#print axioms` for the canonical theorem, exact boundary classification, and polarized pairing returned only `propext`, `Classical.choice`, and `Quot.sound`. No additional axioms or open mathematical premises occur. All four local build artifacts are newer than their source files.

The repository-wide `scripts/formal_tools.py lint --check-generated` run found four unrelated modules unreachable from the umbrella: `MobiusDivisorExhaustionPrimeCapacity`, `MobiusDivisorMandatoryScalarBlock`, `OddSectorExactFibreRecovery`, and `PaperThetaNativeQuantileComparison`. It also detected generated reports invalidated by concurrent source changes. After regeneration, the repeat check still found those four modules and a newly stale `LEAN_API.md`; the overview freshness issue cleared. The SZ imports pass the reachability check. Reports were refreshed once more at handoff. No unrelated source or import was changed to mask the global lint failures, and no repository-wide green lint result is claimed.
