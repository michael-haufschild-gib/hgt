# Optimal origin-to-collar measure transport

- **ID:** BSU-OT
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for the explicit physical partition; broader optimization program open
- **Scope:** Bi-Scale Uncertainty; no RH claims or work.
- **Objective:** Integrate the origin-sphere leverage law on `(0, log 2 / 2)` with optimal coset origin allocations and overlap-safe transport of `exp(x/2)/sinh(x)` on `(0, log N)`. Continue toward the supplied requirement of 100 significant contributions; do not count routine supporting lemmas as separate contributions.

## Current evidence

Read the supplied attachment and all 207 lines of `docs/reports/BiScaleUncertainty/README.md`.
The complete singular-endpoint lower bound is now verified in `IntegratedOriginCollarLeverage.lean`, together with measurable optimal origin shares and a finite positive real coefficient. It uses the literal signed odd-coset partition in `SignedDyadicCollarPartition.lean`, the existing shared-origin support function, and the three allocation/transport/coverage modules.
Search `research 'integrated shared origin collar leverage' --module BiScaleUncertainty --json` completed, `partial=false`, no errors; semantic coverage not measured and coverage snapshot older than current generation. Inspect and compile actual sources before relying on source-only metadata.
The explicit-partition contribution is complete in Lean. A second contribution now has a complete paper proof: the global physical-allocation dual certificate and exact comparison remainder, with its finite geometry and actual-grid price regularity verified in Lean. General physical pullback and integration remain open for that second theorem. Neither optimizer existence nor the 100-contribution program is complete.
Task-relevant memories restrict research evidence to the local corpus and prohibit numerical experiments. No external novelty claim is made.

## Plan

1. [x] Prove exact optimal origin allocation across signed coset chains, including zero-weight cases.
2. [x] Construct physical overlap partitions and prove the finite-interval transport inequality on paper, accounting for both collar signs and the upper cutoff. Formalize the exact finite-interval measure decomposition.
3. [x] Complete Lean assembly of the integrated lower bound, measurable optimal shares, and finite positive real coefficient. All five modules for this bound are wired and individually audited; standard-axiom audits pass.
4. [ ] Resolve the repository lint blocker from two concurrent, unwired modules; see the ledger. The earlier four modules are now wired. No task-module lint error was reported.
5. [ ] Formalize the complete continuous dual certificate for general physical partitions; its paper proof and finite geometry are complete.
6. [ ] Keep the facts/failures ledger current and continue conjecture/proof cycles toward 100 significant contributions.

`update_plan` and `multi_tool_use.parallel` are unavailable in this session. This card records the plan; independent reads use parallel promises.

## First candidate

For signed chains `j=(m,sign)`, let `q_j(y)` be the Euclidean norm of the transported collar densities in that chain and `A(y)=sum_j q_j(y)`. With total origin density `W(y)`, the optimal share is `theta_j=q_j/A` whenever `A>0`. The exact fibre coefficient is `W+B-sqrt(W^2+A^2)`, not the coefficient obtained by treating all collar nodes as one orthogonal chain. A physical overlap partition is required before computing `q_j`.

## Contribution ledger

Two substantive contributions have complete paper proofs:

1. Overlap-safe finite-interval transport with exact measurable origin allocations and a finite, strictly positive coefficient despite the origin singularity. The explicit equal-multiplicity specialization for compact-continuous scalar sources is verified in Lean.
2. A global physical-allocation dual certificate with an exact nonnegative radial/directional comparison remainder, quantitative capacity improvement, and rigidity under a sharp certificate. Finite geometry and actual-grid price regularity are verified in Lean; the continuous gap identity is paper-only. Card: `docs/drafts/pipeline/2-fully-proven/collar-allocation-dual-certificate-2026-10-17.md`.

Do not count supporting algebra separately or claim an external novelty audit. The 100-contribution goal remains active.

Working facts/failures ledger: `docs/reports/BiScaleUncertainty/OriginCollarTransport-FACTS.md`.
Complete paper proof: `docs/reports/BiScaleUncertainty/OriginCollarTransport.md`.

Concurrent adjacent cards already derive shared-origin optimization. This task's distinct endpoint is physical overlap accounting and integration. Preserve disjoint write scopes.

## Audit

- Paper proof: complete in the linked transport note, including capacity saturation for any physical optimizer.
- Lean: six leaf modules pass direct `lake --old env lean` audit without diagnostics: `OptimalOriginAllocation.lean`, `OverlapSafeCollarMeasureTransport.lean`, `LogarithmicCollarCoverage.lean`, `SignedDyadicCollarPartition.lean`, `IntegratedOriginCollarLeverage.lean`, and `CollarAllocationDuality.lean`. All six are wired into the BiScaleUncertainty umbrella. No full or umbrella build was run.
- Physical overlap change of variables, full `(0, log N)` measure decomposition, and integration of the optimized sphere coefficient across the singular endpoint: formalized for the explicit partition and compact-continuous scalar sources.
- Repository lint is blocked by two concurrent modules missing umbrella imports, listed in the facts ledger. Do not report the global gate as green.
- Global optimization over overlap partitions: not implied by optimality of `theta` for a fixed partition.


## Verified endpoints

All names lie in `GaloisForLFunctions.BiScaleUncertainty`.

- `origin_allocation_exact_minimum`: attained optimal origin splitting for every finite nonempty block vector, including zero blocks.
- `archimedean_collar_measure_transport`: exact transport through a finite family of normalized truncated collars, with measurability discharged for continuous kernels and no finite-energy assumption.
- `arch_logarithmic_origin_collar_decomposition`: origin interval plus normalized signed collars equals the full finite-interval extended energy for every N=n+2.
- `autocorr_logarithmicCoset_sphere`: actual signed odd-coset spheres from literal finite-grid zeros.
- `measurable_logarithmicOptimalCosetShare`, `logarithmicOptimalCosetShare_optimal`: measurable, normalized, nonnegative shares attaining the exact origin-budget optimum.
- `integrableOn_logarithmicCollarKernel`, `logarithmicCollarRealConstant_pos`: the combined coefficient has a finite, strictly positive ordinary real integral.
- `integrated_logarithmic_origin_collar_real_bound`: this real coefficient times `h(0)` bounds the full extended nonnegative finite-interval energy, including infinite-energy sources.
- `collarDualRemainder_decomposition`, `collarRadialRemainder_rationalized`, `collarDualRemainder_zero_forces_blockNorm`: exact comparison geometry and aggregate-norm rigidity.
- `collarAllocationKernel_monotone_bounds`, `collarAllocationKernel_strict_mono`: quantitative strict gain from added physical capacity at each fibre.
- `measurable_logarithmicCollarDualSlope`, `integrableOn_logarithmicCollarDualSlope`: actual-grid prices are measurable and integrable across the origin.
- `scripts/formal_tools.py lint`: exit 1, only two concurrent umbrella-reachability errors; see the ledger.
- `scripts/formal_tools.py index`: completed, exit 0.
- Axiom audit: prior capstones pass `/tmp/bsu_origin_collar_axioms.lean`; nine integrated-package endpoints pass `/tmp/bsu_integrated_final_axioms.lean`; nine duality endpoints pass `/tmp/bsu_collar_duality_axioms.lean`. Only standard `propext`, `Classical.choice`, `Quot.sound`. No added axioms, `sorry`, `admit`, `opaque`, `unsafe`, `native_decide`, or heartbeat overrides in the task modules.

## Completion boundary

Do not mark the thread goal complete: 100 significant contributions are not established. The exact physical-allocation optimizer and subsequent research cycles remain open. Do not count each helper theorem or the independently developed shared-origin support function as a separate contribution.


## Reuse and next proof obligation

- Reuse the verified odd-dyadic partition, signed-chain spheres, exact sum identities, compact-source autocorrelation continuity, and extended measure decomposition. No bridge remains to assume for the explicit-partition endpoint.
- For full physical partitions, total collar mass has a fixed integral. Maximizing the coefficient therefore minimizes the convex defect `∫(sqrt(W²+Aρ²)−W)`.
- Establish attainment and exact optimality conditions for this physical-share problem. The first corpus query found a quadratic weak lower-semicontinuity result, which does not settle this nonlinear functional. Do not claim a global physical optimizer until a complete proof exists.

## Active dual-certificate attack

- Prior goal turn: progress, closing the complete explicit-partition Lean lower bound.
- Completed on paper: a quantitative global comparison certificate, including zero blocks and all integrability obligations. The supporting inequality, exact remainder, and marginal-price regularity now pass Lean.
- Next: define general measurable physical partitions by nonnegative shares, collar support, and the exact physical probability identity. Prove their affine cost transport and finite-minimum regularity; integrate the verified bounded remainder without assuming these bridges.
- A zero certificate proves global physical optimality. A positive certificate is only an upper bound on possible improvement unless a separate descent theorem is proved. Optimizer existence remains a distinct obligation.

## Current continuous formalization

Previous goal turn was progress: complete paper dual theorem and verified finite geometry.
Current proof order is general physical partitions with exact support/probability, bounded
measurable pulled-back densities, real affine transport for linear costs, measurable minimum
active price, then the exact integrated gap. Structural partition conditions define the
admissible class; no transport, integrability, or optimality estimate may be a class field.
Reuse the already verified finite duality rather than introducing a new support-function proof.
