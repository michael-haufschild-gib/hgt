# Origin-to-collar transport: working facts and failures

This is a research-state ledger, not a chronological log. Update entries in place when evidence changes.

## Scope and evidence rules

- Independent Bi-Scale Uncertainty, finite interval `(0, log N)`, archimedean density `w(x)=exp(x/2)/sinh x`.
- Research evidence: local Lean corpus and direct proofs. No numerical experiments or external novelty claims.
- User goal remains 100 significant contributions. Supporting lemmas and independently rediscovered adjacent results do not count separately.
- Main paper proof: `OriginCollarTransport.md` in this directory.
- Physical-allocation dual certificate and exact remainder: `CollarAllocationDuality.md` in this directory.
- Task card: `docs/drafts/pipeline/1-in-progress/optimal-origin-collar-transport-2026-10-17.md`.

## Established mathematical facts

| Fact | Exact content | Evidence/status |
|---|---|---|
| Signed-chain sphere constraints | `h(y)^2 + sum_(n in C_m) h(log n ± y)^2 ≤ h(0)^2`. Each sign is a separate constraint sharing the same origin coordinate. | Existing chain-sphere Lean theorems; source inspected. |
| Optimal origin allocation | For `q_j≥0`, `sum α_j=W>0`, minimum of `sum sqrt(α_j²+q_j²)` is `sqrt(W²+(sum q_j)²)`. If `A=sum q_j>0`, unique optimum `α_j=Wq_j/A`. If `A=0`, every nonnegative allocation is optimal. | Paper proof complete. `origin_allocation_exact_minimum` in `OptimalOriginAllocation.lean` passes direct leaf audit, including all-zero blocks. Uniqueness is paper-only. |
| Physical capacity constraint | At each physical x, collar shares must satisfy `sum_n ρ_n(x)≤1`. This is independent of the origin allocation constraint. | `collarPhysicalShare_partition`, `collarPhysicalShare_nonneg`, and `collarPhysicalShare_capacity` verified in `OverlapSafeCollarMeasureTransport.lean`. |
| Exact collar pullback | `sum_(n,σ) ∫₀^δ a_(n,σ)(y)D(log n+σy)dy = ∫_(union E_n) w(x)D(x)sum_n ρ_n(x)dx`. | Paper-proven for general shares. `archimedean_collar_measure_transport` verifies the equal-multiplicity specialization for every continuous real kernel, using an extended nonnegative density; no integrability premise. |
| Complete coverage | For `δ=log 2/2`, `N≥2`, truncated collars `E_n=(log n−δ,log n+δ)∩(0,log N)` have union `(δ,log N)`. | `truncated_logarithmic_collar_union` passes direct leaf audit. Successive gaps `<2δ`; first left endpoint δ. |
| Explicit feasible partition | `M(x)=sum_n 1_(E_n)(x)`, `ρ_n=1_(E_n)/M`, with zero at `M=0`. Shares sum to 1 on the union. | `lintegral_collarPhysicalShare_partition` and `archimedean_collar_measure_transport` verified. Global optimality of this partition is NOT claimed. |
| Integrated coefficient | `K=W+B−sqrt(W²+A²)`, `A=sum_j ||a_j||₂`, `B=sum a`, gives `∫₀^L D w ≥ R∫₀^δ K`. | `integrated_logarithmic_origin_collar_real_bound` passes direct source and axiom audits for the explicit equal-multiplicity partition and compactly supported continuous scalar sources. General physical shares and continuous positive-definite kernels remain paper-only. |
| Measurable optimal shares | `θ_j(y)=q_j(y)/A(y)` is measurable; on `0<y<δ`, its entries are nonnegative, sum to 1, and attain the exact minimum aggregate sphere penalty. | `measurable_logarithmicOptimalCosetShare`, `logarithmicOptimalCosetShare_optimal`, direct source and axiom audits pass. |
| Singular cancellation | `K=B−A²/(sqrt(W²+A²)+W)` and `0≤K≤B`; the coefficient has a finite real integral. | `logarithmicCollarKernel_rationalized`, `logarithmicCollarKernel_bounds`, `integrableOn_logarithmicCollarKernel` verified. The sharper estimate `B−K≤A²/(2W)=O(y)` remains paper-only, using bounded collar weights and `yw(y)→1`. |
| Strict positivity | Equal-multiplicity partition has a positive left weight at n=2 for every `0<y<δ`; hence `A,B>0`, `K>0`, and `∫K>0`. | `logarithmicCollarRealConstant_pos` verified. No uniform numerical lower bound claimed. |
| Capacity saturation | Every physical subpartition deficient on a positive-measure set admits a strict improvement of `∫K`. Fibre improvement obeys `(1−Ab/Sb)Δmass≤ΔK≤Δmass`. | Full physical statement paper-proven. `collarAllocationKernel_monotone_bounds` and `collarAllocationKernel_strict_mono` prove the quantitative finite-fibre law in Lean. No optimizer-existence claim. |
| Global dual certificate | `Cρ+Gρ−Cη=Hρ(η)+∫Eρ,η`, with both terms on the right nonnegative. Therefore `0≤C*−Cρ≤Gρ`, and `Gρ=0` proves global physical optimality. | Complete paper proof in `CollarAllocationDuality.md`; full continuous Lean assembly pending. Prices compare different offsets at a common physical point. |
| Remainder geometry | `E=r_rad+(A/S)Σr_j`, where `r_rad=W²(Ab−A)²/[S(S Sb+W²+A Ab)]` and every `r_j≥0`. Thus `E=0` forces `Ab=A`. | `collarDualRemainder_decomposition`, `collarRadialRemainder_rationalized`, `collarDualRemainder_zero_forces_blockNorm` pass direct source audit in `CollarAllocationDuality.lean`. |
| Bounded marginal prices | Canonical prices `p=(A/S)a_j/||a_j||₂`, zero on zero blocks, are measurable and in `[0,1)`; actual-grid prices are integrable through the origin. Also `0≤E≤A+Ab`. | Exact supporting inequality, remainder bound, and actual-grid measurability/bounds/integrability pass direct source audit. |

## Failed or invalid approaches

**Consistency check, N=2.** Only the left collar survives the cutoff. Then `A=B=w(log 2−y)` and `K=w(y)+w(log 2−y)−sqrt(w(y)²+w(log 2−y)²)`, exactly the existing reflected-pair kernel, now with the singular endpoint handled through the bounded combined coefficient. No extra factor of two appears.

1. **Spend full w(y) on every coset.** Invalid: repeats origin energy. Repair: a single probability allocation over all signed chains.
2. **Spend a coset share independently on left and right.** Invalid: repeats that coset's origin budget. Repair: include sign in the allocation index, or split a coset's share conditionally between signs.
3. **Assign full w(x) to every overlapping collar.** Invalid: counts physical energy with multiplicity. Repair: physical partition or subpartition before pullback to y.
4. **Replace the sum of block norms by one global Euclidean norm.** Unsupported: assumes cross-coset orthogonality absent from finite-grid zeros. Gram-coupled work can improve the bound using actual cross information, not by deleting it.
5. **Integrate W and sqrt(W²+A²) separately near zero.** Invalid: each diverges. Repair: rationalize their difference or integrate the bounded K as a whole.
6. **Use real Bochner energy for arbitrary continuous correlations without proving integrability.** Invalid: a nonintegrable Bochner integral is totalized to zero in Lean. Repair: extended nonnegative integral, or prove finite energy for the chosen admissible class.
7. **Claim global autocorrelation sharpness from fibre sharpness.** Unsupported: different y-extremizers need not assemble into a positive-definite function.
8. **Claim physical-allocation optimality from optimal θ.** Unsupported: θ optimization fixes ρ. Physical overlap allocation couples different offsets `|x−log n|`.
9. **Treat a positive canonical dual gap as proof of suboptimality.** Invalid in general: zero blocks allow other subgradient choices. A zero gap is sufficient; a positive gap bounds possible improvement. Necessity needs a separate argument.
10. **Differentiate the block norm at a zero block.** Invalid without a subgradient convention. The canonical zero vector gives a valid supporting plane, and all comparison formulas include that case.

## Adjacent work and ownership

- `bi-scale-multichain-gram-coupling-2026-10-17.md` proves the shared-origin optimizer on paper and develops the exact Gram-resolved improvement.
- `bi-scale-quantitative-constant-2026-10-17.md` independently studies the same shared-origin support function and polar escape.
- Therefore count this task's substantive contribution as overlap-safe finite-interval transport, not discovery of the shared-origin formula alone. Preserve their files and use disjoint filenames.

## Open dependencies and next attacks

1. Formalize the complete physical dual gap identity: admissible general partitions, measurable finite minimum over active collars, affine linear-cost pullback, and integration of the already verified bounded remainder. Do not assume these as bridge hypotheses.
2. Establish existence or construct a zero-gap optimizer over physical shares ρ. A sufficient global certificate is now proved on paper; existence and a complete characterization remain open.
3. Decide whether fractional physical splitting can strictly improve every single-node assignment; distinguish this from the already solved origin-budget split.
4. Extend the formal domain from scalar compact-continuous autocorrelations to arbitrary continuous positive-definite real kernels if that serves the next result.
5. Formalize uniqueness/stability of optimal θ only if it materially serves physical optimization; do not count routine algebra as new contributions.

## Verification boundary

- Direct leaf audits pass for all six task modules: `OptimalOriginAllocation.lean`, `OverlapSafeCollarMeasureTransport.lean`, `LogarithmicCollarCoverage.lean`, `SignedDyadicCollarPartition.lean`, `IntegratedOriginCollarLeverage.lean`, `CollarAllocationDuality.lean`. Commands use `lake --old env lean <leaf> -o <leaf.olean>` from `formal`; exit 0, no diagnostics. All six are wired into the area umbrella. No full or umbrella build was run.
- `/tmp/bsu_integrated_final_axioms.lean` audits the signed spheres, compact-source continuity, measurable optimal shares, exact optimizer, rationalization, integrability, coefficient finiteness/positivity, and real integrated bound. Exit 0; only `propext`, `Classical.choice`, `Quot.sound`. Earlier allocation/transport/coverage capstones have the same standard-axiom audit.
- `/tmp/bsu_collar_duality_axioms.lean` audits nine duality endpoints and inspects both quantitative-capacity theorem signatures. Exit 0; only the same three standard axioms, with no unintended implicit indices. Log: `/tmp/bsu-collar-duality-axioms.log`.
- **Repository lint currently fails, exit 1:** two concurrent modules are unreachable from the area umbrella: `CosecantSecantDualDecomposition`, `DisjointCollarCliqueDivergenceAndTuransProblem`. The previously listed four modules are now wired. No task-module error was reported. Preserve their source ownership; do not report a green global gate until this is resolved. Full log: `/tmp/bsu-collar-duality-lint.log`.
- `scripts/formal_tools.py index`: exit 0; generated the three formal indexes and refreshed the source database.

Formal transport uses `ENNReal.ofReal` of the archimedean increment. It is unconditional for continuous kernels and includes infinite energy. For autocorrelations, increment nonnegativity identifies this with the actual nonnegative energy density. The integrated theorem imposes literal grid zeros through the source type; it does not assume a sphere bound or an integrability bridge.

## Formal domain and reusable interfaces

- `PhysicalCollarPartition.lean` now passes its direct source audit. The admissible class has only share measurability, nonnegativity, collar support, and exact physical mass conservation. It has an explicit equal-multiplicity inhabitant. `integral_signed_cost_transport` proves real affine transport for every bounded measurable collar-dependent price; `integral_mass` proves independence of total physical mass. Density bounds and kernel integrability are derived, not class fields.
- Current continuation is checking `/tmp/bsu_physical_prices.lean`; `/tmp/bsu_physical_certificate.lean` contains the prepared continuous gap assembly. These are unfinished scratch artifacts until their own final source audits pass.
- `SignedDyadicCollarPartition.lean` passes its direct leaf audit. `sum_logarithmicSignedCosets` proves exact signed coverage of every node, using `Nat.exists_eq_two_pow_mul_odd`; no assumed chain-cover interface remains.
- `continuous_autocorr_compact` proves continuity for every compactly supported continuous real source by convolution. The older C² continuity lemma imposed unnecessary regularity for this problem.
- `arch_logarithmic_origin_collar_decomposition` supplies the exact physical energy decomposition. Reuse it instead of repeating affine substitutions or coverage.
- `SharedOriginMultiCosetLeverage.lean` supplies the shared-origin support function; the integrated theorem derives its sphere hypotheses from the actual signed odd-coset partition.
- `CollarAllocationDuality.lean` supplies explicit marginal prices and the exact nonnegative comparison remainder. It supports the continuous dual theorem but does not yet prove its general physical pullback or integrated minimum-price gap.
- Formal source parameter is `LogarithmicGridSource n`: a compactly supported continuous source with the literal zeros at log 2 through log(n+2). These are the defining admissibility conditions, not assumed sphere estimates or integrability bridges. In this API `N=n+2`.
- The complete paper statement for arbitrary continuous real positive-definite correlations remains broader than this scalar-source Lean domain. Do not silently identify the two formal domains.

## Next variational reduction

For any full physical partition, `∫₀^δ Bρ(y)dy = ∫δ^L w(x)dx` is independent of ρ. Hence maximizing the coefficient equals minimizing

`∫₀^δ [sqrt(W(y)²+Aρ(y)²)−W(y)]dy`.

This follows on paper from the already proved affine transport identity with increment D=1. The defect is a convex, increasing, 1-Lipschitz function of the nonnegative block norm A. This identifies a convex variational problem; existence and exact optimizer conditions still need a corpus-backed proof. Do not infer monotonicity in N or global sharpness of the particular equal-multiplicity certificate.

Corpus search `research 'weak compact convex integral minimizer Lp' --json` returned no directly applicable attainment theorem (`partial=false`, no errors; semantic coverage unavailable). A weak lower-semicontinuity result for quadratic integral functionals is not by itself a proof for this nonlinear defect. Broaden the query or inspect the convex functional APIs before asserting existence.

The dual-certificate search used `research 'physical collar allocation convex dual optimality' --module BiScaleUncertainty --json`; it returned the existing transport ingredients, not a global physical gap theorem. A broader block-subgradient query supplied no directly applicable theorem. Both reported `partial=false`, no errors, semantic coverage not measured; source-only metadata is not a compile certificate.

## Lean implementation guardrails

- Parenthesize each subtraction inside nested finite sums: `∑ m∈M, ∑ k∈s m, (b m k−a m k)`. Without parentheses, notation precedence can leave free indices and silently synthesize unintended implicit parameters. `CollarAllocationDuality.lean` disables `autoImplicit`, and the final audit inspects the quantitative theorem signatures.
- Supply the actual finite index sets and density arrays explicitly when specializing the generic measurable-slope theorem. Unconstrained placeholders caused an elaboration timeout; explicit arguments resolved it without increasing heartbeats.
