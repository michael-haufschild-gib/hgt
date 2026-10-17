# Physical collar allocation: dual certificate and exact gap

- **ID:** BSU-OT-DUAL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); continuous dual certificate verified
- **Execution status:** Parent research goal cleared by user; no further autonomous work pending.
- **Source:** `docs/reports/BiScaleUncertainty/OriginCollarTransport.md`
- **Statement:** Every feasible physical partition ρ has an explicit nonnegative finite certificate Gρ with `Cρ+Gρ−Cη=Hρ(η)+∫Eρ,η` for every competing partition η; a zero certificate attains the physical optimum.

## Goal

Separate optimal origin splitting from the remaining physical-overlap allocation problem.
The certificate gives a global upper bound on any possible improvement without presupposing
an optimizer. Its exact remainder separates radial curvature from block-direction mismatch.

## Gates

- [x] Well-posed continuous physical-partition problem; local corpus searched.
- [x] Complete dependency-closed paper proof in `docs/reports/BiScaleUncertainty/CollarAllocationDuality.md`.
- [x] Complete Lean proof of the continuous physical gap identity, supremum bounds,
  complementary allocation, aggregate-norm rigidity, and first-grid optimum.
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
- Existence of an optimal physical partition for `N>2` remains open; the `N=2` optimum is verified.
- Full block-ray classification and the source-energy theorem for arbitrary physical partitions remain paper-only.
- Fibre optimality does not imply realization by one positive-definite correlation.
- No numerical experiments, external novelty claims, or RH work.
- Count the complete dual-certificate package once. The former 100-contribution goal was cleared, not achieved.

## Formal construction

`PhysicalCollarPartition.lean` defines shares by measurability, nonnegativity, collar support,
and exact physical mass conservation, then derives integrability and affine cost transport.
`PhysicalCollarDualPrices.lean` proves minimum-price regularity and exact dual pairing.
`PhysicalCollarDualCertificate.lean` integrates the bounded remainder and proves the endpoints.
No transport or optimality estimate is assumed as an admissibility field.

## Verification

- `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/CollarAllocationDuality.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/CollarAllocationDuality.olean`: exit 0, no diagnostics.
- `/tmp/bsu_collar_duality_axioms.lean`: exit 0; nine endpoints use only `propext`, `Classical.choice`, `Quot.sound`. Quantitative theorem signatures contain exactly the intended binders.
- All three `PhysicalCollar*` leaves pass direct source audits, exit 0 without diagnostics.
- `/tmp/bsu_physical_duality_axioms.lean` audits twelve endpoints and prints the partition fields and main signatures; only the same three standard axioms, no errors.
- All task modules are wired; source index refreshed. No full or umbrella build.
- Latest global lint passes. Logs: `/tmp/bsu-physical-duality-{axioms,lint,index}.log`.
