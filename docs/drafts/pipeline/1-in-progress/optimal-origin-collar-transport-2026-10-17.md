# Optimal origin-to-collar measure transport

- **ID:** BSU-OT
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); exact allocation and measure decomposition verified in Lean
- **Scope:** Bi-Scale Uncertainty; no RH claims or work.
- **Objective:** Integrate the origin-sphere leverage law on `(0, log 2 / 2)` with optimal coset origin allocations and overlap-safe transport of `exp(x/2)/sinh(x)` on `(0, log N)`. Continue toward the supplied requirement of 100 significant contributions; do not count routine supporting lemmas as separate contributions.

## Current evidence

Read the supplied attachment and all 207 lines of `docs/reports/BiScaleUncertainty/README.md`.
Current corpus includes the original chain sphere law, shared-origin multi-coset leverage, and the three verified allocation/transport/coverage modules. The complete singular-endpoint lower-bound assembly remains absent from the inspected sources.
Search `research 'integrated shared origin collar leverage' --module BiScaleUncertainty --json` completed, `partial=false`, no errors; semantic coverage not measured and coverage snapshot older than current generation. Inspect and compile actual sources before relying on source-only metadata.
Previous goal turn classified as progress: new verified modules and complete paper transport proof. Current action is the exact signed-coset-to-integral bridge, not another derivation of the shared-origin support function.
Task-relevant memories restrict research evidence to the local corpus and prohibit numerical experiments. No external novelty claim is made.

## Plan

1. [x] Prove exact optimal origin allocation across signed coset chains, including zero-weight cases.
2. [x] Construct physical overlap partitions and prove the finite-interval transport inequality on paper, accounting for both collar signs and the upper cutoff. Formalize the exact finite-interval measure decomposition.
3. [ ] Complete Lean assembly of the integrated lower bound. The three allocation/transport/coverage modules are wired and individually audited; formal lint and standard-axiom audits pass.
4. [ ] Keep the facts/failures ledger current and continue conjecture/proof cycles toward 100 significant contributions.

`update_plan` and `multi_tool_use.parallel` are unavailable in this session. This card records the plan; independent reads use parallel promises.

## First candidate

For signed chains `j=(m,sign)`, let `q_j(y)` be the Euclidean norm of the transported collar densities in that chain and `A(y)=sum_j q_j(y)`. With total origin density `W(y)`, the optimal share is `theta_j=q_j/A` whenever `A>0`. The exact fibre coefficient is `W+B-sqrt(W^2+A^2)`, not the coefficient obtained by treating all collar nodes as one orthogonal chain. A physical overlap partition is required before computing `q_j`.

## Contribution ledger

One substantive contribution has a complete paper proof: overlap-safe finite-interval transport with exact origin allocations and a finite, strictly positive coefficient despite the origin singularity. Full Lean transport verification remains open; do not count supporting algebra separately. The 100-contribution goal remains active.

Working facts/failures ledger: `docs/reports/BiScaleUncertainty/OriginCollarTransport-FACTS.md`.
Complete paper proof: `docs/reports/BiScaleUncertainty/OriginCollarTransport.md`.

Concurrent adjacent cards already derive shared-origin optimization. This task's distinct endpoint is physical overlap accounting and integration. Preserve disjoint write scopes.

## Audit

- Paper proof: complete in the linked transport note, including capacity saturation for any physical optimizer.
- Lean: three new leaf modules pass direct `lake --old env lean` audit without diagnostics: `OptimalOriginAllocation.lean`, `OverlapSafeCollarMeasureTransport.lean`, and `LogarithmicCollarCoverage.lean`. All three are wired into the BiScaleUncertainty umbrella. No full or umbrella build was run.
- Physical overlap change of variables and full `(0, log N)` measure decomposition: formalized. Integration of the optimized sphere coefficient across the singular endpoint: paper-proven, not yet formalized.
- Global optimization over overlap partitions: not implied by optimality of `theta` for a fixed partition.


## Verified endpoints

All names lie in `GaloisForLFunctions.BiScaleUncertainty`.

- `origin_allocation_exact_minimum`: attained optimal origin splitting for every finite nonempty block vector, including zero blocks.
- `archimedean_collar_measure_transport`: exact transport through a finite family of normalized truncated collars, with measurability discharged for continuous kernels and no finite-energy assumption.
- `arch_logarithmic_origin_collar_decomposition`: origin interval plus normalized signed collars equals the full finite-interval extended energy for every N=n+2.
- `scripts/formal_tools.py lint`: passed, exit 0; existing large-file warnings outside the task modules.
- `scripts/formal_tools.py index`: completed, exit 0.
- Axiom audit: all three capstones pass `/tmp/bsu_origin_collar_axioms.lean`; only standard `propext`, `Classical.choice`, `Quot.sound`. No added axioms, `sorry`, `admit`, `opaque`, `unsafe`, `native_decide`, or heartbeat overrides in the new modules.

## Completion boundary

Do not mark the thread goal complete: 100 significant contributions are not established. The exact physical-allocation optimizer, the complete Lean lower-bound assembly, and the subsequent research cycles remain open. Do not count each helper theorem or the independently developed shared-origin support function as a separate contribution.


## Active proof decomposition

- Construct the odd-dyadic fibre partition of all nodes from the corpus theorem `Nat.exists_eq_two_pow_mul_odd`, rather than assuming a covering family of chains.
- Derive the signed-chain spheres and sum identities for that literal partition.
- Establish autocorrelation continuity for compactly supported continuous sources by the existing convolution theorem, avoiding an unnecessary differentiability assumption.
- Combine the fibre inequality with the verified extended measure decomposition; then prove finiteness of the explicit coefficient without separating divergent origin terms.
