# Physical collar allocation: dual certificate and exact gap

- **ID:** BSU-OT-DUAL
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); finite geometry formalized, continuous assembly pending
- **Source:** `docs/reports/BiScaleUncertainty/OriginCollarTransport.md`
- **Statement:** Every feasible physical partition ρ has an explicit nonnegative finite certificate Gρ with `Cρ+Gρ−Cη=Hρ(η)+∫Eρ,η` for every competing partition η; a zero certificate attains the physical optimum.

## Goal

Separate optimal origin splitting from the remaining physical-overlap allocation problem.
The certificate gives a global upper bound on any possible improvement without presupposing
an optimizer. Its exact remainder separates radial curvature from block-direction mismatch.

## Gates

- [x] Well-posed continuous physical-partition problem; local corpus searched.
- [x] Complete dependency-closed paper proof in `docs/reports/BiScaleUncertainty/CollarAllocationDuality.md`.
- [ ] Complete Lean proof of the continuous physical gap identity. Current leaf formalizes
  the finite geometry and actual-grid price regularity; final leaf and nine-endpoint axiom audits pass.
- [ ] Publication-ready external novelty and presentation audit.

## Proof and positive content

1. Normalize each signed-coset density block; multiply by `A/sqrt(W²+A²)` to obtain measurable supporting prices p, including zero blocks.
2. The nonlinear comparison remainder is nonnegative and at most `A+Ab`.
3. Its radial term is exactly `W²(Ab−A)²/[S(S Sb+W²+A Ab)]`; the remainder is this term plus `(A/S)` times the sum of directional block discrepancies.
4. Pull prices back along the actual affine collar branches. At each physical point subtract the minimum active price. Fixed total physical mass then gives the exact integrated gap identity.
5. Zero gap proves global optimality and complementary allocation. Equal optimizers under a sharp certificate have equal aggregate block norms almost everywhere.
6. Added nonnegative capacity satisfies `(1−Ab/Sb)Δmass≤ΔK≤Δmass`; positive mass gives strict improvement.

## Boundaries

- Full physical shares are admissibility data, not assumed estimates or optimality conditions.
- No derivative or finite-source-energy assumption is used.
- A positive canonical gap does not prove suboptimality when zero blocks allow other subgradients.
- Existence of an optimal physical partition remains open.
- Fibre optimality does not imply realization by one positive-definite correlation.
- No numerical experiments, external novelty claims, or RH work.
- Count the complete dual-certificate package once. The parent program remains far below its 100-contribution requirement.

## Next formal obligation

Implement admissible measurable physical partitions and prove the finite-minimum and affine
linear-cost transport identities. Then integrate the verified bounded remainder. Do not assume
these identities as bridge hypotheses in the final endpoint.

## Verification

- `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/CollarAllocationDuality.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/CollarAllocationDuality.olean`: exit 0, no diagnostics.
- `/tmp/bsu_collar_duality_axioms.lean`: exit 0; nine endpoints use only `propext`, `Classical.choice`, `Quot.sound`. Quantitative theorem signatures contain exactly the intended binders.
- Umbrella import added; source index refreshed, exit 0. No full or umbrella build.
- Latest global lint exits 1 on two concurrent unwired modules, listed in the working ledger; no task-module error. This card stays at the paper-proof stage because the continuous Lean assembly remains open.
