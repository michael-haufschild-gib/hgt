# Actual partition density ratio: nonmonotonicity and endpoint rigidity

- **ID:** LI-CLOCK-PARTITION-DENSITY-RATIO-ENDPOINT-BOUNDARY
- **Stage:** 2-fully-proven
- **Type:** THEOREM (complete author, cross-agent and root paper/source audits PASS)
- **Source:** [actual Volterra partition](../3-formalized/li-clock-finite-partition-volterra-positive-area.md), [literal gap cancellation](../3-formalized/li-clock-completion-arithmetic-cancellation-boundary.md), [joint cancellation](../3-formalized/li-clock-joint-arithmetic-cancellation-window.md)
- **Statement:** For each actual fixed `N>=2`, the tilted difference-density ratio against the literal contiguous source is neither nondecreasing nor nonincreasing; on the retained support-edge neighborhoods it equals `κ_N=(Z_U/Z_A)^2>1`. The full normalized even-moment ratio tends `κ_N` as the order tends infinity. Audit the stronger full Borel-kernel ratio limit before formalization.

## Goal

Test monotone density-ratio forcing using the actual interval union, with every gap retained. If obstructed, formalize the strongest dependency-closed endpoint survivor. This is a subroute audit; RH and the actual growing-window residual sign remain open.

## Candidate source formulas

`S_N` is the full union `(log(2n+1),log(2n+2)]`, `n<N`; `L=log(2N)`, `ε_N=log(2N/(2N-1))`. The two half-tilt normalizers are `Z_A=∫_{S_N}exp(-u/2)du` and `Z_U=∫_0^L exp(-u/2)du`. Their normalized difference densities are obtained from both independent tilted variables; no exponential shift or gap deletion is permitted.

For `0<=x<ε_N`, the proposed exact ratio is
`r_N(x)=κ_N*(a_N-exp(x)*b_N)/(1-q_N*exp(x))`,
where `a_N=Σ_{n<N}1/(2n+1)`, `b_N=Σ_{n<N}1/(2n+2)`, `q_N=1/(2N)`. Its right derivative at zero should equal `κ_N*(q_N*a_N-b_N)/(1-q_N)^2<0`. Strict missing-gap mass also gives `r_N(0)<κ_N`.

At the support edges, the actual and contiguous unnormalized overlap densities coincide exactly: `r_N(x)=κ_N` when **`L-ε_N<abs(x)<L`**. At and outside `abs(x)>=L` both densities vanish; no quotient claim there. The strict upper endpoint is essential. The difference is supported in the smaller interval, so its full raw even-moment contribution decays geometrically relative to a retained edge rectangle. Raw product-measure domination also suggests `d_A,j<=κ_N*d_U,j` at every order and `B_A(t)<=κ_N*B_U(t)` at every nonnegative clock. The endpoint limits would make `κ_N` the optimal uniform coefficient for both families; for `N>=2`, strict comparison below `κ_N` and eventual `B_A>B_U` must be audited explicitly. Normalize only after proving this domination. Fixed `N` is essential: `ε_N` shrinks with `N` and no uniform growing-window estimate follows.

## Relative Volterra overlap

The existing full positive kernels permit the candidate exact identity
`2*(P_A-P_U)*(B_A*B_U)=(t*B_A')*B_U-B_A*(t*B_U')`.
Here `P_A-P_U` is the literal signed arithmetic gap clock. The forcing remains signed; positivity of the convolution kernel supplies no pointwise inverse-sign theorem. A full closed disk of partition nonvanishing is needed for its contour-to-central-series step. This algebraic identity alone does not close the residual `Re(C-K+H)>=0`.

## Prior-source audit

Pole ran the documented research directly: `/tmp/li_pole_joint_relative_research.json`, terminal55.406s, `partial=false`, query generation1150851. Coverage snapshot1150861 reports all63224 indexed files; semantic coverage unmeasured, background refresh incomplete and compiler freshness mostly pending/source-only. All20 candidates, all20 source arguments and the sole ingredient set inspected; the proposed theta-deletion/Levinson pair does not apply. Direct lexical `/tmp/li_pole_joint_relative_overlap.json`: all20 hits inspected, exact existing Volterra/cumulant/gap APIs recovered. Independent producer discovery agrees on the edge invariant and supplies the local-slope obstruction. Its direct research `/tmp/hgt-li-actual-relative-volterra-research.json` finished70.100s, `partial=false`, generation1150875 against snapshot1150879 with all63225 indexed; semantic coverage unmeasured, background refresh incomplete, compiler47653 pending/2660 stale. All20 candidates, all20 source arguments, one proof idea and one ingredient set inspected; the alternating/PNT proposal has incompatible observables and no quotient-sign estimate. Narrow lexical followup remains pending. No corpus absence or publication novelty claim.

## Gates

- [x] New card created before hard paper proof or Lean.
- [x] Actual/source versus model boundary identified; initial independent endpoint agreement.
- [x] Complete literal difference-density identification, all interval-overlap cases and local derivative proof.
- [x] Dependency-closed full moment-ratio proof, quantitative remainder, Borel-ratio audit and independent source checks.
- [x] No-go and strongest positive survivor independently audited; exact survivor stated before route retirement.
- [ ] Exact Lean formalization, named/direct/all-public foundational checks and umbrella wiring.
- [ ] Publication/novelty audit.

## Ownership

Root owns this card, integration, independent review and `LiClockPositiveEvenSeriesRatio.lean`. Current exclusively owns new `LiClockPairedEtaContiguousMeasure.lean`: literal reference measure, normalized full difference moments/Borel kernel and actual-source restriction/comparison APIs. Producer exclusively owns new `LiClockPairedEtaPartitionDensityRatio.lean`: full density-source identification, local/edge formulas, both radial monotonicity obstructions including a.e versions and signed forcing support. Pole exclusively owns new `LiClockPairedEtaPartitionEndpointComparison.lean`: full quantitative moment bounds, limits, sharp all-order/Borel constants and both kernel gap escapes. Each owns separate scratch files. Source-interface names must be coordinated; import only final READY dependencies. Existing final leaves stay frozen; one foreground Lean per agent; no other tree edits.

## Complete paper certificates

Density/source/no-go: `/tmp/hgt-li-density-ratio-paper.md`,272 lines, SHA256 `afcbe8ca8e1fdaa5bb75bf1468fb18ebd4d9e170a3c6b09d79e0e3452adedd39`. Endpoint/moment/Borel: `/tmp/li_pole_endpoint_paper.md`,214 lines, SHA256 `fd228a336b5495f4638ebdc84a65be0afaa32d6adb6c8c31a33c6631d5671191`. Root read every line of both notes, with independent cross-audits PASS; literal measure/partition/normalizer/source declarations spot-verified. Generic full-series transfer has its own [paper/formal card](li-clock-positive-borel-ratio-transfer.md).

For fixed `N>=2`, `a=L-ε`, `b=L-ε/2`, `D0=Z_U^2-Z_A^2`, and
`E=8*exp(-L/2)*(1-exp(-ε/8))*(exp(ε/8)-1)>0`, both mirrored endpoint rectangles are retained. Every order satisfies
`0<κ-d_A,j/d_U,j<=(κ*D0/E)*(a/b)^(2j)`.
Every real clock satisfies `B_A<κ*B_U`; the full positive-clock ratio tends `κ`, and both `B_A-B_U` and `κ*B_U-B_A` tend positive infinity. For every real coefficient `K`, each all-order or all-nonnegative-clock comparison holds exactly iff `κ<=K`. No positivity assumption on `K`, ratio monotonicity or uniform `N` rate is asserted. `N=1` has exact equality; `N=0` lacks probability normalization. Both a.e radial monotone-ratio shortcuts fail by open witnesses; reference probability-null and Lebesgue-null sets coincide inside support.

## Log

- 2026-09-30 06:48 UTC — Created following documented source search and independent agreement; source support endpoint corrected explicitly. No subroute retired, no RH sign claim.
- 2026-09-30 07:12 UTC — Complete272/214-line paper, normalization, source and independent audits PASS. Strongest sharp positive survivor fixed before no-go closure; movedStage2 and released disjoint Lean scopes. Formal work pending; no whole orientation-route retirement or RH conclusion.
