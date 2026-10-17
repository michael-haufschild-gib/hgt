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

No strict improvement of C_N over P_N, sharp convergence rate, or equality with the
true source infimum is asserted. Sharpness applies only to the paired-sphere support.
The full-grid capped-support construction below retains high nodes without the
loss caused by separately summing low/high block norms.

## Quantitative product-coupled saturation

Paired capacity has its own proved comparison: nonnegative coordinate addition
increases the kernel by between zero and added mass, for every real origin weight.
An unordered nonnegative array differs from a trial array by at most the supplied
added capacity. Padding preserves both sign norms. Exact physical extension and
retraction therefore prove

    Q_K ↑ C_∞ = sup_K Q_K ≥ P_∞,
    0≤C_∞−Q_K≤∫_(log K−δ)^∞w≤4·2^(1/4)/(sqrt(K)(1−2/K²)).

For N≥4, let s=floor(sqrt N). The finite envelope reduces exactly to

    C_N=max(P_N,Q_s),
    0≤C_∞−C_N≤4·2^(1/4)/(sqrt(s)(1−2/s²))≤16·2^(1/4)/N^(1/4).

Thus every actual nonzero compact C² N-grid source has
J_arch(f)/h_f(0)≥C_∞−16·2^(1/4)/N^(1/4). There is no optimizer or extra analytic
premise. The bound is for the product-coupled subhierarchy, not the full Gram cone.

`PairedCollarCapacity.lean` and `PairedCollarCutoffStability.lean` pass direct Lean
compilation without diagnostics. All 30 theorem axiom/signature audits pass using
only `propext`, `Classical.choice`, and `Quot.sound`. Final direct recheck passed,
exit 0, no diagnostics.
The error exponent is an upper bound, not a proved sharp rate. Matching leading laws
and strict improvement C_∞>P_∞ remain open.

## Exact full-grid capped support

For K²≤N, split each signed odd-coset weight vector into low nodes j≤K and high
nodes j>K, with Euclidean norms L and H. Preserve each whole-coset sphere and add
the opposite-sign low-block pair spheres supplied by literal product-grid zeros.
Their exact finite-vector support is R sqrt(W²+Z²), where

    Z = max_(0≤t≤1) Σ_m [F_(L_false,m,H_false,m)(t)
                       +F_(L_true,m,H_true,m)(sqrt(1−t²))],
    F_(L,H)(t) = sqrt(L²+H²)                  if L≤t sqrt(L²+H²),
                Lt+H sqrt(1−t²)             otherwise.

Lean proves the formula including zero weights, compact attainment, continuity,
the exact finite-amplitude/vector support, and Z≤Σ_(σ,m)sqrt(L²+H²). Thus the
physical capped coefficient B_(N,K)(ρ) satisfies, for every physical partition,

    oldCoefficient_N(ρ) ≤ B_(N,K)(ρ) ≤ J_arch(f)/h_f(0).

The source is the actual nonzero compact C² N-grid source. The ENNReal version
holds for every compact continuous grid source, including zero source and infinite
energy, and uses the full interval (0,log N). No analytic transfer or optimizer
premise is imposed. `fullGrid_capped_energy` supplies K=floor(sqrt N) for N≥4.
Finite support sharpness does not assert autocorrelation realization.

All three leaves and final direct source-leaf check pass without diagnostics.
All 41 public theorem axiom/signature audits use only `propext`, `Classical.choice`,
and `Quot.sound`. This is one contribution package.

Paper-only activation criterion: let α_σ=max_m L_(σ,m)/sqrt(L_(σ,m)²+H_(σ,m)²),
with zero fraction for zero blocks. The angular support equals the independent
whole-block support iff α_false²+α_true²≤1; otherwise improvement is strict.
Proof: equality in each nonzero block's Cauchy bound requires its normalized weight
direction; simultaneous feasibility is exactly the displayed condition. Compact
attainment turns failure of feasibility into a strict support gap. Integrated
strictness requires activation on a positive-measure set. Not yet Lean-verified.

Still open for this new coefficient: cutoff monotonicity and quantitative limit,
formal all-low reduction to paired support, unequal-size product-zero pairs, and
general nonzero Schur residual coupling. Do not transfer the preceding C_N rate
to B_(N,K) without proving the comparison/limit statements.

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

Lean-verified significant packages: **5/100**: (1) general source transfer and
optimized certificates; (2) actual cutoff monotonicity, retraction stability, and
explicit quantitative saturation; (3) attained paired-sphere support, actual signed
product-zero source transfer, and its optimized monotone finite-limit hierarchy;
(4) paired capacity and cutoff stability, exact limit identification and frame
selection, and quantitative fourth-root source-cutoff control; (5) exact capped
support and finite-vector attainment, followed by full-grid physical source transfer.
Count each package once, not its leaves or helper lemmas.
Previously certified shared-origin and dual-allocation results are dependencies.
The full research objective remains active.

Current global lint exits 1 solely on two concurrent missing umbrella imports:
`FiniteTrainUniformEnergy` and `LocalCorrelationEnergyStability`, both in
BiScaleUncertainty. Earlier four-import failure is obsolete. All eleven owned leaves are
reachable; no own-leaf lint error is reported. Index refresh passed.

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

Paired-cutoff SHA-256 values:

- Capacity: `215adfa612eb4e9eef6d1025d51de02109b3d2b0a157828441b4068c83030863`.
- Stability: `e2f4d2b569d6df1efd3e4e65444f9e025408ee34d1c9fe83973e273334eec19c`.

Evidence: `/tmp/bsu-paired-capacity.log`, `/tmp/bsu-paired-stability.log`,
`/tmp/bsu-paired-cutoff-{axioms,final,index,lint}.log`, `/tmp/bsu_paired_cutoff_axioms.lean`.
All 30 public theorems are included in the audit; principal signatures and cutoff
definitions were printed and inspected.
All owned jobs exited; the paired-cutoff API probe was removed. Successful audit
scripts and logs remain available; no full or umbrella build was run.

Full-grid SHA-256 values:

- Block support: `3004dced418ed93f074aa177cd75cf7bd841200f6af3328538e5cd2863355406`.
- Coset support: `b6e3bd890950ae1874e4c4ef87a30d383d1d4360768ffdad607e2b8505d811c5`.
- Source transfer: `6a8bcfaba9f2647cdeadc59abc68a5cf7724c4a3c58e049120c7922553503b0d`.

Evidence: `/tmp/bsu-capped-block.log`, `/tmp/bsu-capped-cosets.log`,
`/tmp/bsu-fullgrid-capped.log`, `/tmp/bsu-fullgrid-capped-{axioms,final,index,lint}.log`,
`/tmp/bsu_fullgrid_capped_axioms.lean`. All eight earlier hashes rechecked unchanged.
Final direct command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/FullGridCappedCollarEnergy.lean`.
Exit 0, no diagnostics; all 41 public theorem audits pass.

Reusable proof repairs: expose the explicit function composition before applying
measurability of the compact support map to low/high array maps; leaving it implicit
causes a default-heartbeat definitional-equality timeout. Name the array measurable
maps and keep the compact-map proof separate. Prefer an explicit `change` and
`simp only` over `unfold` plus `simp_rw` across actual-source subtype coercions.
`Finset.sup'_mem` is a closure-under-sup lemma, not finite
maximum attainment; use `Finset.exists_mem_eq_sup'`. Unfold `LogarithmicGridSource.restrict`
when simplifying the source kernel on the right side of a restricted-grid bound.
Expose Ioi membership as an inequality before arithmetic tactics. Import checks can
spend minutes in `lean_mark_persistent` under shared memory pressure; inspect the live
owned process and keep polling its handle instead of restarting after an observation timeout.
