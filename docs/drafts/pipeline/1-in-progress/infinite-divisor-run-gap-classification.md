# Arbitrary divisor families: run length, coercivity and closed range

- **ID:** infinite-divisor-run-gap-classification
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For an arbitrary nonempty divisor family, uniform boundedness
  of consecutive active runs exactly characterizes positive interpolation
  coercivity and closed physical L² range.

Use actual spacings {d+2}∪{e+2:e∈D}, with d:ℕ and D:Set ℕ, so the family
may be infinite and has no nonemptiness or minimum-spacing admission premise.
Construct its closed masked ℓ² data space and E(v)=S(v−Rv) using the certified
unit-cell synthesis and shifts. Every positive integer trace and exact adjacent
energy should remain valid without periodicity.

Conjectured unconditional classification on d,D:

    range(E) is closed
      iff there exists c>0 with c‖v‖²≤‖Ev‖² for every actual datum v
      iff active consecutive runs have a uniform finite length bound.

In the bounded case, construct the least exclusion length r and recover the
attained sharp constants 2±2cos(π/(r+1)). In the unbounded case, construct
actual normalized finite sine packets v_n with ‖E(v_n)‖²→0. Prove that the
infimum zero is unattained on unit data, using the actual trace injectivity.
Discharge the closed-range equivalence through applicable complete-space
operator results, rather than assuming a bounded inverse or spectral gap.

The positive survivor is the exact classification and the explicit near-null
producer sequence. A negative no-gap statement alone does not close this card.
The full integer union should supply a concrete infinite-family example.
No RH, numerical experiment, or unproved analytic receiver premise is proposed.

The new finite-family theorem exposes this question: periodic missing nodes
were used only to bound run length, whereas the sharp packets and global
interpolation already live in unrestricted ℓ². Reuse those actual constructions.
Check primary closed-range/continuous-inverse theory before a paper proof.

Corpus check: `bounded consecutive runs closed range discrete derivative`,
BiScaleUncertainty filter, `--any`, 60-second request. All 20 candidate entries
and all 5 source arguments inspected. Hits include the newly proved finite-grid
run invariant and closed range, older two-grid closed sums, and unrelated
dyadic packet/transport results; no arbitrary-family classification found.
Search partial=true, text/source retrieval interrupted, coverage generation
1445834 pending, semantic coverage unmeasured, background refresh incomplete.
Returned compiler metadata is source-only; actual applicability remains to be
checked in Lean. These limitations do not establish external novelty.

Status: dependency-closed paper argument below prepared; Lean verification pending.
Uncounted until the full classification, sharp bounded case and near-null producer
have passed direct leaf checks and complete declaration axiom audit.

Plan: construct arbitrary-family data; prove least-run geometry and sharp bounds;
construct normalized sine packets; discharge closed-range equivalence; audit,
wire imports and update the ledger. Paper: `InfiniteDivisorRunGap.md`.
