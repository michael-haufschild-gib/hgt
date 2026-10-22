# Optimal origin-to-collar measure transport

- **ID:** BSU-OT
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for the explicit-partition energy bound and general physical dual certificate; broader optimization program open
- **Execution status:** User cleared the goal; no autonomous research pending.
- **Scope:** Bi-Scale Uncertainty; no RH claims or work.
- **Objective:** Integrate the origin-sphere leverage law on `(0, log 2 / 2)` with optimal coset origin allocations and overlap-safe transport of `exp(x/2)/sinh(x)` on `(0, log N)`. The former 100-contribution goal was cleared before completion; two substantive packages are established.

## Current evidence

Read the supplied attachment and all 207 lines of `docs/reports/BiScaleUncertainty/README.md`.
The complete singular-endpoint lower bound is now verified in `IntegratedOriginCollarLeverage.lean`, together with measurable optimal origin shares and a finite positive real coefficient. It uses the literal signed odd-coset partition in `SignedDyadicCollarPartition.lean`, the existing shared-origin support function, and the three allocation/transport/coverage modules.
Search `research 'integrated shared origin collar leverage' --module BiScaleUncertainty --json` completed, `partial=false`, no errors; semantic coverage not measured and coverage snapshot older than current generation. Inspect and compile actual sources before relying on source-only metadata.
The explicit-partition contribution is complete in Lean. The second contribution, the global physical-allocation dual certificate and exact comparison remainder, is also formalized, including general physical pullback, minimum-price regularity, and integration. General optimizer existence for `N>2` remains open. The first-grid optimum is verified.
Task-relevant memories restrict research evidence to the local corpus and prohibit numerical experiments. No external novelty claim is made.

## Plan

1. [x] Prove exact optimal origin allocation across signed coset chains, including zero-weight cases.
2. [x] Construct physical overlap partitions and prove the finite-interval transport inequality on paper, accounting for both collar signs and the upper cutoff. Formalize the exact finite-interval measure decomposition.
3. [x] Complete Lean assembly of the integrated lower bound, measurable optimal shares, and finite positive real coefficient. All five modules for this bound are wired and individually audited; standard-axiom audits pass.
4. [x] Repository lint passes; earlier concurrent umbrella-reachability failures are resolved.
5. [x] Formalize the complete continuous dual certificate for general physical partitions.
6. [x] Preserve verified facts, failures, and open boundaries in the working ledger after the user cleared the goal. Further research requires a new instruction.

`update_plan` and `multi_tool_use.parallel` are unavailable in this session. This card records the plan; independent reads use parallel promises.

## First candidate

For signed chains `j=(m,sign)`, let `q_j(y)` be the Euclidean norm of the transported collar densities in that chain and `A(y)=sum_j q_j(y)`. With total origin density `W(y)`, the optimal share is `theta_j=q_j/A` whenever `A>0`. The exact fibre coefficient is `W+B-sqrt(W^2+A^2)`, not the coefficient obtained by treating all collar nodes as one orthogonal chain. A physical overlap partition is required before computing `q_j`.

## Contribution ledger

Two substantive contributions have complete paper proofs:

1. Overlap-safe finite-interval transport with exact measurable origin allocations and a finite, strictly positive coefficient despite the origin singularity. The explicit equal-multiplicity specialization for compact-continuous scalar sources is verified in Lean.
2. A global physical-allocation dual certificate with an exact nonnegative radial/directional comparison remainder, quantitative capacity improvement, and rigidity under a sharp certificate. The continuous gap identity, optimal-supremum bounds, complementary allocation, and `N=2` optimum are verified in Lean. Card: `docs/drafts/pipeline/3-formalized/collar-allocation-dual-certificate-2026-10-17.md`.

Do not count supporting algebra separately or claim an external novelty audit. The 100-contribution goal was cleared, not achieved.

Working facts/failures ledger: `docs/reports/BiScaleUncertainty/OriginCollarTransport-FACTS.md`.
Complete paper proof: `docs/reports/BiScaleUncertainty/OriginCollarTransport.md`.

Concurrent adjacent cards already derive shared-origin optimization. This task's distinct endpoint is physical overlap accounting and integration. Preserve disjoint write scopes.

## Audit

- Paper proof: complete in the linked transport note, including capacity saturation for any physical optimizer.
- Lean: all nine task leaves pass direct `lake --old env lean` audits without diagnostics and are wired into the umbrella; the complete list is in the working ledger. No full or umbrella build was run.
- Physical overlap change of variables, full `(0, log N)` measure decomposition, and integration of the optimized sphere coefficient across the singular endpoint: formalized for the explicit partition and compact-continuous scalar sources.
- Latest repository lint passes. Log: `/tmp/bsu-physical-duality-lint.log`.
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
- `PhysicalCollarPartition.exact_dual_gap`, `optimalCoefficient_gap_bounds`, `gap_eq_zero_iff_complementary`, `aggregate_rigidity_of_gap_zero`, `optimalCoefficient_first_grid`: complete continuous certificate and first-grid optimum.
- `scripts/formal_tools.py lint`: passed; see the ledger.
- `scripts/formal_tools.py index`: completed, exit 0.
- Axiom audit: prior capstones pass `/tmp/bsu_origin_collar_axioms.lean`; nine integrated-package endpoints pass `/tmp/bsu_integrated_final_axioms.lean`; nine finite-duality endpoints pass `/tmp/bsu_collar_duality_axioms.lean`; twelve physical-duality endpoints pass `/tmp/bsu_physical_duality_axioms.lean`. Only standard `propext`, `Classical.choice`, `Quot.sound`. No added axioms, `sorry`, `admit`, `opaque`, `unsafe`, `native_decide`, or heartbeat overrides in the task modules.

## Completion boundary

The user cleared the goal. Do not resume autonomous research or mark the former target achieved: 100 significant contributions are not established. General physical-allocation optimizer existence remains open. Do not count helper theorems or the independently developed shared-origin support function separately.


## Reuse and next proof obligation

- Reuse the verified odd-dyadic partition, signed-chain spheres, exact sum identities, compact-source autocorrelation continuity, and extended measure decomposition. No bridge remains to assume for the explicit-partition endpoint.
- For full physical partitions, total collar mass has a fixed integral. Maximizing the coefficient therefore minimizes the convex defect `∫(sqrt(W²+Aρ²)−W)`.
- Establish attainment and exact optimality conditions for this physical-share problem. The first corpus query found a quadratic weak lower-semicontinuity result, which does not settle this nonlinear functional. Do not claim a global physical optimizer until a complete proof exists.

## Continuous formalization boundary

The `PhysicalCollar*` modules prove general measurable partition transport, active-price minima,
and the integrated gap from structural share conditions alone. No transport, integrability,
or optimality estimate is a class field. A zero gap certifies global physical optimality;
a positive gap only bounds possible improvement. Optimizer existence for `N>2`, necessity
of a zero canonical gap, full block-ray classification, and the source-energy theorem for
arbitrary physical partitions remain outside the verified result.
