# Actual partition density ratio: nonmonotonicity and endpoint rigidity

- **ID:** LI-CLOCK-PARTITION-DENSITY-RATIO-ENDPOINT-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (exact density/source/classification and endpoint comparison Lean certificates FINAL; relative-clock expansion separately FINAL)
- **Source:** [actual Volterra partition](../3-formalized/li-clock-finite-partition-volterra-positive-area.md), [literal gap cancellation](../3-formalized/li-clock-completion-arithmetic-cancellation-boundary.md), [joint cancellation](../3-formalized/li-clock-joint-arithmetic-cancellation-window.md)
- **Statement:** For each actual fixed `N>=2`, the tilted difference-density ratio against the literal contiguous source is neither nondecreasing nor nonincreasing, including a.e. monotone versions on the positive half-support; on retained support-edge neighborhoods it equals `κ_N=(Z_U/Z_A)^2>1`. Full normalized even-moment and Borel-kernel ratios tend `κ_N`, with quantitative moment error and sharp uniform ceilings. Both kernel differences escape to positive infinity. These fixed-`N` results leave the actual growing-window residual sign open.

## Goal

Test monotone density-ratio forcing using the actual interval union, with every gap retained. If obstructed, formalize the strongest dependency-closed endpoint survivor. This is a subroute audit; RH and the actual growing-window residual sign remain open.

## Candidate source formulas

`S_N` is the full union `(log(2n+1),log(2n+2)]`, `n<N`; `L=log(2N)`, `ε_N=log(2N/(2N-1))`. The two half-tilt normalizers are `Z_A=∫_{S_N}exp(-u/2)du` and `Z_U=∫_0^L exp(-u/2)du`. Their normalized difference densities are obtained from both independent tilted variables; no exponential shift or gap deletion is permitted.

For `0<=x<ε_N`, the proposed exact ratio is
`r_N(x)=κ_N*(a_N-exp(x)*b_N)/(1-q_N*exp(x))`,
where `a_N=Σ_{n<N}1/(2n+1)`, `b_N=Σ_{n<N}1/(2n+2)`, `q_N=1/(2N)`. Its right derivative at zero should equal `κ_N*(q_N*a_N-b_N)/(1-q_N)^2<0`. Strict missing-gap mass also gives `r_N(0)<κ_N`.

At the support edges, the actual and contiguous unnormalized overlap densities coincide exactly: `r_N(x)=κ_N` when **`L-ε_N<abs(x)<L`**. At and outside `abs(x)>=L` both densities vanish; no quotient claim there. The strict upper endpoint is essential. The difference is supported in the smaller interval, so its full raw even-moment contribution decays geometrically relative to a retained edge rectangle. Raw product-measure domination also suggests `d_A,j<=κ_N*d_U,j` at every order and `B_A(t)<=κ_N*B_U(t)` at every nonnegative clock. The endpoint limits would make `κ_N` the optimal uniform coefficient for both families; for `N>=2`, strict comparison below `κ_N` and eventual `B_A>B_U` must be audited explicitly. Normalize only after proving this domination. Fixed `N` is essential: `ε_N` shrinks with `N` and no uniform growing-window estimate follows.

## Relative Volterra overlap (separately formalized)

Exact central-clock expansion is now separately formalized by [relative Volterra forcing](./li-clock-partition-relative-volterra-forcing.md): four modules and38 public declarations, with complete source/series admissions, literal clock subtraction and both common-disk guards. The density and endpoint consumer certificates retain their original classification/source/comparison scope.


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
- [x] Exact assigned density/source/classification and endpoint Lean formalization, named/direct/all-public foundational checks and umbrella wiring.
- [x] Separate [relative Volterra central-clock expansion](./li-clock-partition-relative-volterra-forcing.md) formalization: all38 declarations certified; outside these two original consumer certificates.
- [ ] Publication/novelty audit.

## Ownership

Root owns this card, integration, independent review and `LiClockPositiveEvenSeriesRatio.lean`. Current exclusively owns new `LiClockPairedEtaContiguousMeasure.lean`: literal reference measure, normalized full difference moments/Borel kernel and actual-source restriction/comparison APIs. Producer exclusively owns new `LiClockPairedEtaPartitionDensityRatio.lean`: full density-source identification, local/edge formulas, both radial monotonicity obstructions including a.e versions and signed forcing support. Pole exclusively owns new `LiClockPairedEtaPartitionEndpointComparison.lean`: full quantitative moment bounds, limits, sharp all-order/Borel constants and both kernel gap escapes. Each owns separate scratch files. Source-interface names must be coordinated; import only final READY dependencies. Existing final leaves stay frozen; one foreground Lean per agent; no other tree edits.

## Complete paper certificates

Density/source/no-go: `/tmp/hgt-li-density-ratio-paper.md`,272 lines, SHA256 `afcbe8ca8e1fdaa5bb75bf1468fb18ebd4d9e170a3c6b09d79e0e3452adedd39`. Endpoint/moment/Borel: `/tmp/li_pole_endpoint_paper.md`,214 lines, SHA256 `fd228a336b5495f4638ebdc84a65be0afaa32d6adb6c8c31a33c6631d5671191`. Root read every line of both notes, with independent cross-audits PASS; literal measure/partition/normalizer/source declarations spot-verified. Generic full-series transfer is [FINAL/Stage3](../3-formalized/li-clock-positive-borel-ratio-transfer.md).

For fixed `N>=2`, `a=L-ε`, `b=L-ε/2`, `D0=Z_U^2-Z_A^2`, and
`E=8*exp(-L/2)*(1-exp(-ε/8))*(exp(ε/8)-1)>0`, both mirrored endpoint rectangles are retained. Every order satisfies
`0<κ-d_A,j/d_U,j<=(κ*D0/E)*(a/b)^(2j)`.
Every real clock satisfies `B_A<κ*B_U`; the full positive-clock ratio tends `κ`, and both `B_A-B_U` and `κ*B_U-B_A` tend positive infinity. For every real coefficient `K`, each all-order or all-nonnegative-clock comparison holds exactly iff `κ<=K`. No positivity assumption on `K`, ratio monotonicity or uniform `N` rate is asserted. `N=1` has exact equality; `N=0` lacks probability normalization. Both a.e radial monotone-ratio shortcuts fail by open witnesses; reference probability-null and Lebesgue-null sets coincide inside support.

## Log

- 2026-09-30 06:48 UTC — Created following documented source search and independent agreement; source support endpoint corrected explicitly. No subroute retired, no RH sign claim.
- 2026-09-30 07:12 UTC — Complete272/214-line paper, normalization, source and independent audits PASS. Strongest sharp positive survivor fixed before no-go closure; movedStage2 and released disjoint Lean scopes. Formal work pending; no whole orientation-route retirement or RH conclusion.
- 2026-09-30 08:08 UTC — Reference base `LiClockPairedEtaContiguousMeasure.lean` FINAL/FROZEN and wired:600 lines,54 public declarations,SHA256 `9564ce2fce59b915d8256429fa187c50d4c6c274eb0f1227bcda87d286f63dcd`. Root and pole read every private/public proof; exact tree snapshot matches both audits. Named1282 exit0,own26s; exact direct5907 exit0 EMPTY; all54 public axioms81145 exit0,only foundational axioms. Logs `/tmp/li_current_contiguous_measure_{named,direct,axioms}.log`; full literal headers and audit certificates `/tmp/li_current_contiguous_measure_{api_ledger,proof_audits}.md`. Exact filled reference transform/MGF, both tilt normalizers, all moments and complete real/complex Borel series, actual full-union restriction/raw-product domination, normalized all-order comparison, N1 equality and N>=2 strict normalizer gap closed. Density/no-go and sharp endpoint consumers still required; card remainsStage2.
- 2026-09-30 08:20 UTC — Both dependencies FINAL: reference54 and [generic full-series transfer11](../3-formalized/li-clock-positive-borel-ratio-transfer.md),65 public foundational certificates. Exact source/header audits and unique umbrella imports PASS; closure index78758 exit0. Global lint83316 exit1 on11 unrelated unreachable modules, no owned-leaf/proof-debt error; full error list and logs recorded on generic card. Endpoint may use the direct product-defect decomposition and literal/local scale/width to avoid depending on the larger density/no-go leaf; every original214/272 paper target remains required before this card advances.

2026-09-30 09:17 UTC — Root and independent auditors READ ALL consumer proofs: endpoint1208/33 public and density1446/83 public PASS. Header-only sole-leaf promotions released; final certification underway. Original section7 central-clock relative Volterra expansion is explicitly preserved on [separate Stage2 card](./li-clock-partition-relative-volterra-forcing.md), with every source/factorial/common-disk obligation retained. No claim that signed-density identities alone formalize relative clocks.

## FINAL exact consumer certificates

2026-09-30 09:20 UTC — Full root and independent proof/source audits PASS, all public statements matched to exact final source. Endpoint `LiClockPairedEtaPartitionEndpointComparison.lean`:1217 lines/33 public, SHA256 `70e0b471bda434151361d280b3a6d6609afd55c8ea8ea7952ea4a4a564536d61`; named84868 exit0 (leaf73s,12995jobs), exactdirect50524 exit0 EMPTY, all33 axioms65342 exit0 only `propext, Classical.choice, Quot.sound`. Density `LiClockPairedEtaPartitionDensityRatio.lean`:1463 lines/83 public, SHA256 `e5f9dbafe30b1a47fbfa498093aac715e407778b1454b8d696a35495404384ab`; named92435 exit0 (leaf71s,12994jobs), exactdirect23931 exit0 EMPTY, all83 axioms25644 exit0 only foundational axioms. Logs `/tmp/li_pole_endpoint_{named,direct,axioms}.log` and `/tmp/hgt-li-density-ratio-{named,direct,axioms}.log`; complete exact headers `/tmp/li_pole_endpoint_final_api_ledger.md` and `/tmp/hgt-li-density-ratio-api-ledger.{md,json}`. Public header extraction retains every type-level let before actual proof delimiter; all116 checked mechanically against source. Both unique umbrella imports added; index/lint integration gate pending.

Density retains every interval pair and both independent square normalizers, exact full/radial pushforward laws (fold factor2 and zero atom), local strict decrease/right derivative, strict edge plateau, both pointwise and all source/Lebesgue a.e. radial order obstructions, N1 equality, every source moment, raw central missing mass at least1/6, exact signed antisymmetry/ratio coupling, smaller forcing support and every continuous-test four-coordinate Bochner identity. Endpoint retains both mirrored rectangles/E, full missing-product loss, all-order strict defect and geometric error, fixedN ratio limits, ALL-J full Borel bound, sharp ceilings iff for every realK, both separately licensed divergent gaps, full factorial defect envelope and actual complex absolute/compact-local uniform sums. No N0 probability interpretation, outside-support ratio plateau, uniformN rate, inverse forcing/clock sign or RH inference. The strongest positive survivor is fully formalized before closing the two radial-order shortcuts; the entire orientation route stays OPEN.

2026-09-30 09:23 UTC — Integration index86071 exit0: generated API/gaps/overview and incremental search refresh5 changed/0 removed. Global lint48213 exit1 ONLY14 unrelated unreachable modules; no owned consumer or proof-debt error. Logs `/tmp/hgt-li-consumers-final-{index,lint}.log`. Every reported error:

- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMApertureChainProfile`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMApertureTranslationChains`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMExponentialRampPrimeMoment`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMExponentialRampSourceDissipation`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMExponentialRampTerminalEntropy`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMRetainedChainKernelLower`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaNotchDualCarrier`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaNotchDualContour`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaNotchDualOscillation`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaNotchDualOscillationBound`
- `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving`
