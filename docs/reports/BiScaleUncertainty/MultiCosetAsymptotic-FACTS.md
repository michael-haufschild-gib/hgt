# Multi-coset asymptotic constants: facts and unresolved claims

Scope: independent BiScaleUncertainty. Active objective comes from attachment
`14cea3d2-a6f6-463f-bcd2-5d8a6947ba60/pasted-text-1.txt`; 100 significant contributions,
without counting helper lemmas or previous work again. No RH objective or hgtl7.
Plan and complete current paper arguments:
`docs/drafts/pipeline/1-in-progress/multi-coset-asymptotic-constants-2026-10-17.md`.

## Exact source transfer

For N=n+2, every `PhysicalCollarPartition n` has actual source bound

    ofReal(Cρ h_f(0)) ≤ ∫⁻_(0,log N) ofReal((h_f(0)−h_f(x))w(x)) dx.

The source is any `LogarithmicGridSource n`: compact continuous real function with
literal grid zeros. Infinite energy and zero source are included. Share conditions
are only measurability, nonnegativity, support, and exact physical partition.
No extra transport, integrability, or optimizer condition is supplied by the caller.

Mechanism: exact two-branch ENNReal transport of an arbitrary nonnegative density;
signed-coset sphere law; one shared-origin support function; integrable coefficient.
This closes the previous gap between arbitrary-partition convex optimization and
actual source energy. It is one contribution package, not one per lemma.

Status: final direct `lake --old env lean` check passed, with no diagnostics, for
the entire `PhysicalCollarSourceEnergy.lean` module. It includes the supremum,
normalized smooth-source bound, and monotone finite-limit certificate. All 19 public
theorem axiom audits pass: only `propext`, `Classical.choice`, `Quot.sound`.
Principal signatures and the source subtype were printed and inspected. Own import
is present, indexes are refreshed, and scoped whitespace checks pass. Current global
lint status is recorded below.

The original certificate L_N=max_(2≤K≤N) P_K now equals P_N by the verified
partition-extension theorem. It satisfies

    J_arch(f)/h_f(0) ≥ L_N,       0<L_N ↑ L_∞≤∫_(δ,∞)w<∞.

The ratio theorem uses the actual compact C² nonzero grid-source subtype. The more
general extended-energy theorem needs only compact continuity and the prescribed
grid zeros. Smoothness, nonzero radius, and grid data are defining domain conditions;
no desired energy inequality or analytic transfer is a source field.

## Quantitative saturation of the allocation optimum

Let P_N be the supremum over physical partitions, δ=log(2)/2. Lean proves

    0 ≤ P_∞−P_N ≤ ∫_(log N−δ)^∞w
      ≤ 4·2^(1/4)/(sqrt(N)·(1−2/N²)),   N≥2.

The first comparison rests on extending old partitions and truncating any larger
partition below log N−δ. New nodes have no support below that cutoff. Zero-padding
preserves old block norms; nonnegative coordinate addition changes the coefficient
by between zero and the added mass. The existing finite-array capacity theorem is
the analytic input. Full proof, including endpoints and N=2, is in the card.

Status: both `PhysicalCollarCutoffMonotonicity.lean` and
`PhysicalCollarCutoffStability.lean` compiled without diagnostics. All 35 public
theorems passed scratch axiom audits, using only `propext`, `Classical.choice`, and
`Quot.sound`. Printed signatures confirm unconditional cutoff statements. The
required final direct leaf recheck passed, exit 0, no diagnostics. The error rate is an upper bound,
not a proved optimal rate.

For every finite trial partition ρ, the verified dual-gap corollary gives

    0 ≤ P_∞−Cρ ≤ Gρ + 4·2^(1/4)/(sqrt(N)·(1−2/N²)).

This encloses the allocation limit without assuming an attained optimizer. The
finite dual gap Gρ and the cutoff error have distinct roles; neither bounds the
gap to the true source infimum.

## Candidate leading asymptotic

A further paper argument in the card gives

    P_∞−P_N = 4/sqrt(N)+O(1/N).

It compares the deficit to T_N=∫_(log N,∞)w from both sides. Extending old partitions
by right-node cell assignments adds all tail mass but only O(1/N) radial penalty.
Conversely, remove future-node shares and fill their holes below log N using the next
old grid node; these holes occur only above log(N+1)−δ and their new offsets are
O(1/N), so the repair penalty is O(1/N). The explicit constants and endpoint
assignments are in the card. T_N=4/sqrt(N)+O(N^(−5/2)) follows by integrating the
exponential remainder of w.

Status: paper argument requiring formal audit; uncounted. The exact tail-law corpus
query returned finite-array capacity comparison and existing duality, but no matching
earlier asymptotic theorem. Semantic coverage was unmeasured, so this is not evidence
of exhaustive absence or literature-wide novelty. Log: `/tmp/bsu-allocation-tail-search.log`.

Mechanism worth retaining: high-node physical mass costs order N^(−1/2), while
its optimized origin penalty costs only order N^(−1) because it can be concentrated
on a short offset interval. This is specific to the present independent-block
allocation family; the Schur-coupled and true-source asymptotics remain open.

## Signed product coupling

Opposite signed nodes log j and −log k have cross entry h(log(jk)). Thus cutoff
growth can activate constraints between old nodes: the −log2/+log3 entry is first
pinned at N=6. Allocation tail locality does not imply full signed Gram locality.

For a source pinned through N and a collar grid through K with K²≤N, every pair
of opposite-sign odd cosets, together with the origin, forms an orthogonal clique.
Their paired Bessel spheres imply the finite support function

    R sqrt(W²+A_+²+A_-²),

where A_± are sums of within-sign block Euclidean weight norms. Proof: maximize
the correlation block norm on each sign, apply the paired constraint to the two
maximizers, then apply three-dimensional Cauchy–Schwarz. This support is attained
in the paired-sphere finite-vector model; no source realizability follows.

For a fixed physical partition, the improvement over the independent-sign kernel is

    2 A_+A_- / [sqrt(W²+(A_++A_-)²)+sqrt(W²+A_+²+A_-²)].

`PairedCosetSphereDuality.lean` now passes direct Lean verification of this support,
attainment, domination, and exact gain. `SignedCosetProductCoupling.lean` passes
direct verification of actual product-zero orthogonality, measurable integrable
physical kernels, exact gain, and extended/normalized source-energy transfer.
Only defining grid zeros and the arithmetic cutoff K²≤N are required.

The optimized hierarchy is

    C_N = max(P_N, max_{2≤K, K²≤N} Q_K),

where Q_K is the supremum of coupled physical coefficients through K; an empty
inner maximum is zero. `ProductCoupledCollarHierarchy.lean` proves positivity,
monotonicity, source-energy control, and finite convergence, with upper bound
∫_(δ,∞)w. All three direct compilation checks pass without diagnostics, and all
41 public theorem axiom audits pass using only `propext`, `Classical.choice`, and
`Quot.sound`. Printed signatures and definitions confirm the actual source domain
and arithmetic product-admission condition. Final direct recheck passed, exit 0,
without diagnostics.

No strict improvement of C_N over P_N, rate for C_∞−C_N, or equality with the true
source infimum is asserted. Sharpness applies only to the paired-sphere support.
The card records a next full-grid capped-support construction that retains high
nodes without the loss caused by separately summing low/high block norms.

Next quantitative candidate: prove paired capacity monotonicity and the same physical
retraction tail bound for Q_K. This would identify C_∞=sup_K Q_K and give
O(N^(−1/4)) cutoff control by admitting K=floor(sqrt N). No such rate has yet passed
Lean. A sharper leading-law comparison would depend on whether sup Q_K>sup P_K;
strict improvement of the limiting optimum remains unproved.

## Limits that must remain visible

- P_N optimizes the independent signed-coset sphere relaxation. It is not identified
  with the sharp constant over actual autocorrelations.
- Opposite-sign product-zero coupling is now connected to physical source transport.
  General nonzero Schur residuals and all full-grid cross-coset constraints remain open.
- Fixed narrow smooth sources imply the true finite-grid constants are bounded above
  uniformly in N. Unbounded growth is impossible on this unrestricted-support domain.
- A finite maximum over earlier cutoffs certifies monotonicity immediately. It does
  not by itself prove monotonicity of P_N; use the extension proof for that claim.
- A coefficient sharp in a finite convex relaxation need not have a realizable
  autocorrelation extremizer. Optimizer attainment is not needed for the bounds.
- Tail control of this allocation optimum does not automatically control the error
  to the true source infimum, or the error of a stronger Schur-coupled hierarchy.

## Research accounting

Lean-verified significant packages: **3/100**: (1) general source transfer and
optimized certificates; (2) actual cutoff monotonicity, retraction stability, and
explicit quantitative saturation; (3) attained paired-sphere support, actual signed
product-zero source transfer, and its optimized monotone finite-limit hierarchy.
Count each package once, not its leaves or helper lemmas.
Previously certified shared-origin and dual-allocation results are dependencies.
The full research objective remains active.

Current global lint exits 1 solely on six concurrent missing umbrella imports:
`RHTower.NonTemperedShiftedZetaPairCountermodel`, `RHTower.WeilConeMismatchWitnesses`,
`RHTower.ZeroCountRemainderNotIntegrable`, `BiScaleUncertainty.InfiniteGridDistanceClassification`,
`BiScaleUncertainty.LogarithmicGridDistance`, `BiScaleUncertainty.OddMultiplierLeakageFamily`.
All six owned leaves are reachable; no own-leaf lint error is reported. Index refresh passed.

Final source SHA-256: `423ca0e7d1957c5898bac5ff228e6989d255c98e2fe24ec621775f76d3574792`.
Evidence: `/tmp/bsu-physical-source-{final,axioms,index,lint}.log` and
`/tmp/bsu_physical_source_axioms.lean`.

Cutoff SHA-256 values:

- Monotonicity: `e9ebaca82b8d817c28826c64ac54fb77e81dc5823f71b3329fea4110e0eb6586`.
- Stability: `b3d464f73df171bc2e7f8a062697c15518a63df9a8c9b3bdc2ff3ed940264246`.

Cutoff evidence: `/tmp/bsu-cutoff-check.log`, `/tmp/bsu-cutoff-stability-check.log`,
`/tmp/bsu-cutoff-{axioms,final,index,lint}.log`, `/tmp/bsu_cutoff_axioms.lean`.
All owned processes exited; there is no live job to poll. Temporary API probes are removed.

Product-coupling SHA-256 values:

- Paired geometry: `377bf1eef09bb7190e186f533bc5e8c80cc0bd25e426648e219a103c0ff19d9f`.
- Source transport: `c26fc3d7f4f1d4e4ad123135d733a59fae96c940ddc9c5821a27c4b0eff029dc`.
- Coupled hierarchy: `e78c3e45cc9bcd200840dbfcb40d1a41fa3ff49396b875f98a05850eca6b3156`.

Evidence: `/tmp/bsu-paired-geometry.log`, `/tmp/bsu-signed-coupling.log`,
`/tmp/bsu-product-hierarchy.log`, `/tmp/bsu-product-coupling-{axioms,final,index,lint}.log`,
`/tmp/bsu_product_coupling_axioms.lean`. All 41 public theorems are included in the audit.

Reusable proof repairs: `Finset.sup'_mem` is a closure-under-sup lemma, not finite
maximum attainment; use `Finset.exists_mem_eq_sup'`. Unfold `LogarithmicGridSource.restrict`
when simplifying the source kernel on the right side of a restricted-grid bound.
Expose Ioi membership as an inequality before arithmetic tactics. Import checks can
spend minutes in `lean_mark_persistent` under shared memory pressure; inspect the live
owned process and keep polling its handle instead of restarting after an observation timeout.
