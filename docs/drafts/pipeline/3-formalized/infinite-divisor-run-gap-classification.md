# Arbitrary divisor families: run length, coercivity and closed range

- **ID:** infinite-divisor-run-gap-classification
- **Stage:** 3-formalized
- **Type:** PROVED
- **Statement:** For an arbitrary nonempty divisor family, uniform boundedness
  of consecutive active runs exactly characterizes positive interpolation
  coercivity and closed physical L² range.

Use actual spacings {d+2}∪{e+2:e∈D}, with d:ℕ and D:Set ℕ, so the family
may be infinite and has no nonemptiness or minimum-spacing admission premise.
Construct its closed masked ℓ² data space and E(v)=S(v−Rv) using the certified
unit-cell synthesis and shifts. Every positive integer trace and exact adjacent
energy are proved without periodicity.

Proved unconditional classification on d,D:

    range(E) is closed
      iff there exists c>0 with c‖v‖²≤‖Ev‖² for every actual datum v
      iff active consecutive runs have a uniform finite length bound.

In the bounded case, the least exclusion length r is the attained maximum run,
with sharp attained factors 2±2cos(π/(r+1)). In the unbounded case, actual
normalized finite sine packets v_n satisfy ‖E(v_n)‖²→0. The exact energy
infimum is zero and unattained on unit data, by actual trace injectivity.
The closed-range equivalence is discharged through the Banach open mapping
theorem. No bounded inverse or spectral gap is assumed.

The positive survivor is the exact classification and the explicit near-null
producer sequence. A negative no-gap statement alone does not close this card.
The full integer union supplies a concrete infinite-family example.
No RH, numerical experiment, or unproved analytic receiver premise is proposed.

The new finite-family theorem exposes this question: periodic missing nodes
were used only to bound run length, whereas the sharp packets and global
interpolation already live in unrestricted ℓ². Reuse those actual constructions.
Primary closed-range/continuous-inverse theory was checked before paper proof.

Corpus check: `bounded consecutive runs closed range discrete derivative`,
BiScaleUncertainty filter, `--any`, 60-second request. All 20 candidate entries
and all 5 source arguments inspected. Hits include the newly proved finite-grid
run invariant and closed range, older two-grid closed sums, and unrelated
dyadic packet/transport results; no arbitrary-family classification found.
Search partial=true, text/source retrieval interrupted, coverage generation
1445834 pending, semantic coverage unmeasured, background refresh incomplete.
Returned compiler metadata is source-only; actual applicability remains to be
checked in Lean. These limitations do not establish external novelty.

Status: paper proof, all five direct leaf checks and exact all-declaration
axiom audit complete. Count once: **14/100**. The overall goal remains active.

Plan: construct arbitrary-family data; prove least-run geometry and sharp bounds;
construct normalized sine packets; discharge closed-range equivalence; audit,
wire imports and update the ledger. Paper: `InfiniteDivisorRunGap.md`.

## Verification gates

- [x] Dependency-closed paper proof, including explicit positive survivor:
  complete classification, sharp bounded factors and actual near-null packets.
- [x] Five direct serial leaf checks with normal compiled outputs, exit0 and
  empty diagnostic logs: DivisorGridTraceData, DivisorGridRunGeometry,
  DivisorGridTraceStability, DivisorGridSinePackets, DivisorGridClosedRange.
- [x] Five umbrella imports and 75 catalog-supported entries at exact locations.
- [x] All76 public declarations axiom-audited; 19 principal signatures inspected;
  only propext/Classical.choice/Quot.sound. Thirty mathlib API probes passed.
- [x] Final lint classified: 15 unrelated unreachable modules plus generated
  drift; no own/proof-debt error. Index refreshed and scoped entries reverified.
- [x] Scoped whitespace verified, count and ledger updated.

Evidence: `/tmp/divisor-grid-{data,geometry,stability,packets,closed}-build.log`,
`/tmp/divisor_grid_axioms.lean`, `/tmp/divisor-grid-audit-names.json`,
`/tmp/divisor-grid-api-entries.txt`. No full/umbrella build or heartbeat increase.

The positive survivor is fully certified: exact closed-range/coercivity/run
classification and normalized producers, not merely a negative no-gap result.
Next unproved candidate: `../0-backlog/divisor-trace-energy-completion.md`.
