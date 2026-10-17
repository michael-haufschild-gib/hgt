# Origin-to-collar transport: working facts and failures

This is a research-state ledger, not a chronological log. Update entries in place when evidence changes.

## Scope and evidence rules

- Independent Bi-Scale Uncertainty, finite interval `(0, log N)`, archimedean density `w(x)=exp(x/2)/sinh x`.
- Research evidence: local Lean corpus and direct proofs. No numerical experiments or external novelty claims.
- User goal remains 100 significant contributions. Supporting lemmas and independently rediscovered adjacent results do not count separately.
- Main paper proof: `OriginCollarTransport.md` in this directory.
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
| Integrated coefficient | `K=W+B−sqrt(W²+A²)`, `A=sum_j ||a_j||₂`, `B=sum a`, gives `∫₀^L D w ≥ R∫₀^δ K`. | Complete paper proof. Full Lean scratch endpoint passes for the explicit equal-multiplicity partition and compactly supported continuous scalar sources; final source audit pending. |
| Singular cancellation | `K=B−A²/(sqrt(W²+A²)+W)` and `0≤K≤B`; the coefficient has a finite real integral. | Lean scratch proofs pass. The sharper estimate `B−K≤A²/(2W)=O(y)` remains paper-only, using bounded collar weights and `yw(y)→1`. |
| Strict positivity | Equal-multiplicity partition has a positive left weight at n=2 for every `0<y<δ`; hence `A,B>0`, `K>0`, and `∫K>0`. | Lean scratch proof passes. No uniform numerical lower bound claimed. |
| Capacity saturation | Every physical subpartition deficient on a positive-measure set admits a strict improvement of `∫K`. Hence the supremum over subpartitions equals that over partitions, and any maximizer saturates physical mass a.e. | Complete paper proof in the transport note; Lean proof pending. No existence claim. |

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

## Adjacent work and ownership

- `bi-scale-multichain-gram-coupling-2026-10-17.md` proves the shared-origin optimizer on paper and develops the exact Gram-resolved improvement.
- `bi-scale-quantitative-constant-2026-10-17.md` independently studies the same shared-origin support function and polar escape.
- Therefore count this task's substantive contribution as overlap-safe finite-interval transport, not discovery of the shared-origin formula alone. Preserve their files and use disjoint filenames.

## Open dependencies and next attacks

1. Finish the direct source and axiom audits of the integrated bound, explicit measurable optimal shares, and positive real constant. Its analytic assembly already passes scratch audit.
2. Characterize the optimizer over physical shares ρ. The exact objective is concave in the pulled-back nonnegative weights, but physical points couple multiple offset fibres.
3. Decide whether fractional physical splitting can strictly improve every single-node assignment; distinguish this from the already solved origin-budget split.
4. Extend the formal domain from scalar compact-continuous autocorrelations to arbitrary continuous positive-definite real kernels if that serves the next result.
5. Formalize uniqueness/stability of optimal θ only if it materially serves physical optimization; do not count routine algebra as new contributions.

## Verification boundary

- Verified directly: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/OverlapSafeCollarMeasureTransport.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/OverlapSafeCollarMeasureTransport.olean`, exit 0, no diagnostics.
- Direct leaf audits of `OptimalOriginAllocation.lean` and `LogarithmicCollarCoverage.lean` also passed, exit 0 with no diagnostics. Scratch axiom audit passed for all three capstones: only `propext`, `Classical.choice`, `Quot.sound`; no added axioms or computation-backed axiom.
- `scripts/formal_tools.py lint`: exit 0, `formal lint passed`; existing large-file warnings occur outside these modules.
- `scripts/formal_tools.py index`: exit 0; generated the three formal indexes.
- The integrated bound has a successful scratch audit; the source module, final optimizer API, and real-constant capstones still require direct final audits.

Formal transport uses `ENNReal.ofReal` of the archimedean increment. It is unconditional for continuous kernels and includes infinite energy. For autocorrelations, increment nonnegativity identifies this with the actual nonnegative energy density. The integrated theorem imposes literal grid zeros through the source type; it does not assume a sphere bound or an integrability bridge.

## Formal domain and reusable interfaces

- `SignedDyadicCollarPartition.lean` passes its direct leaf audit. `sum_logarithmicSignedCosets` proves exact signed coverage of every node, using `Nat.exists_eq_two_pow_mul_odd`; no assumed chain-cover interface remains.
- `continuous_autocorr_compact` proves continuity for every compactly supported continuous real source by convolution. The older C² continuity lemma imposed unnecessary regularity for this problem.
- `arch_logarithmic_origin_collar_decomposition` supplies the exact physical energy decomposition. Reuse it instead of repeating affine substitutions or coverage.
- `SharedOriginMultiCosetLeverage.lean` supplies the shared-origin support function; the integrated theorem derives its sphere hypotheses from the actual signed odd-coset partition.
- Formal source parameter is `LogarithmicGridSource n`: a compactly supported continuous source with the literal zeros at log 2 through log(n+2). These are the defining admissibility conditions, not assumed sphere estimates or integrability bridges. In this API `N=n+2`.
- The complete paper statement for arbitrary continuous real positive-definite correlations remains broader than this scalar-source Lean domain. Do not silently identify the two formal domains.

## Next variational reduction

For any full physical partition, `∫₀^δ Bρ(y)dy = ∫δ^L w(x)dx` is independent of ρ. Hence maximizing the coefficient equals minimizing

`∫₀^δ [sqrt(W(y)²+Aρ(y)²)−W(y)]dy`.

This follows on paper from the already proved affine transport identity with increment D=1. The defect is a convex, increasing, 1-Lipschitz function of the nonnegative block norm A. This identifies a convex variational problem; existence and exact optimizer conditions still need a corpus-backed proof. Do not infer monotonicity in N or global sharpness of the particular equal-multiplicity certificate.
