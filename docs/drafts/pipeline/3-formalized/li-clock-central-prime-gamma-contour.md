# Literal clock as a central prime–Gamma contour functional

- **ID:** LI-CLOCK-CENTRAL-PRIME-GAMMA-CONTOUR
- **Stage:** 3-formalized; exact coupled all-clock source capstone verified
- **Type:** THEOREM; phase-preserving identity, no new sign estimate
- **Parent:** [actual-current research loop](../1-in-progress/li-complex-orientation-conjecture-loop-2026-09-29.md)
- **Prior work:** [literal reciprocal sine source](../3-formalized/li-actual-clock-reciprocal-sine-source.md)

## Exact source already inspected

Set `T=inverseTiltedPrimeGammaSourceTrace` and `G=normalizedTraceMomentGerm T=−dslope T 0`.
`InverseTiltedPrimeGammaCentralSource.lean:153,162` gives unconditional local equality with the canonical centered moment germ and all real coefficients `analyticTraceMoments G j=M_j`.
`PrimeArchCentralMomentGerm.lean:339` identifies the complex even moment series locally.
The existing clock source gives, for every real t,

`F(t)=Σ_j (−1)^j t^(2j+1) Re(G^(2j)(0)/(2j)!)/(2j+1)!`.

The two factorials have different origins. Equivalent odd-trace coefficient formula is

`F(t)=−Σ_j (−1)^j Re(T^(2j+1)(0)) t^(2j+1)/[(2j+1)!]²`.

Both coefficient transports preserve all multiplicity copies through the existing exact reciprocal sine identity. Their complex source coefficient identity is used by the exact Lean contour capstone; odd-trace two-factorial rewrite remains the recorded paper consequence.

## Proposed exact contour survivor

There is one r₀>0 such that every positively oriented circle `|z|=r`, with `0<r<r₀`, lies in the common analytic central germ disk. For every real t,

`(F(t):ℂ)=(2πi)⁻¹∮ G(z)sin(t/z) dz=−(2πi)⁻¹∮ T(z)sin(t/z)/z dz`.

Paper proof: on the fixed circle, analytic Taylor series of G and entire sine Laurent series converge absolutely and uniformly. The coefficient of `z⁻¹` is exactly the full odd factorial clock response, with complex coefficients equal to the real central moments. Also `T(0)=0` and `T(z)=−zG(z)` locally. Integrate the complete double series, retaining every term. The essential singularity at zero is intentional; t=0 gives the zero identity.

## Literal arithmetic formula and domain ledger

With s=1+iz,

`T(z)=i[(D(s)−Q(s))/(2A(s))+γ_R(1/2+iz)]`,

where D is `inverseTiltedDyadicContinuedSource`, Q is `inverseTiltedCriticalMellinCorrection` and A is `inverseTiltedDyadicMellin`. Exact reconstruction is `InverseTiltedPrimeGammaCentralSource.lean:28,56,116`.

- Honest finite-coefficient Dirichlet source equality requires `Re(s)>3/2` (`CCMInverseTiltedDyadicPrimeTomography.lean:797,816`). Center has `Re(s)=1`; ordinary prime-series substitution on the central circle is unsupported.
- Quadrature correction converges for `Re(s)>1/2`; aperture is zero-free for `Re(s)>0`. Small central circle satisfies both.
- Canonical continuation D explicitly contains `logDeriv regularizedRiemannZeta (s−1/2)` (Tomography:266). Subtracting Q and dividing by 2A cancels aperture/error machinery back to the regularized critical-Mellin defect. No independent signed estimate enters.
- Local center analyticity is unconditional, from ζ(1/2)≠0. Analyticity throughout `Re(s)>1` is explicitly RH-equivalent (Tomography:1320); do not import it as an arithmetic premise.
- Use the filled divided difference G. Endpoint quotient `−T(z)/z` without filling has value zero at z=0, whereas G(0)=M_0>0.
- Existing Guinand–Weil entire-test contour APIs do not admit `sin(t/z)/z`, which has an essential center singularity. Finite regularized Cauchy-superposition APIs do not by themselves justify the complete sine functional.

## Work plan and limits

1. Independent hostile audit PASS: one radius for every real clock, complex coefficient reality, complete double interchange, all literal factorials, t=0 and counterclockwise orientation.
2. Prior research audit of direct source-side phase-preserving contour/summation interfaces; retain reported incomplete semantic/compiler coverage.
3. Formalization is final: generic central Cauchy–sine transform in `LiClockCentralSineContour.lean`; exact coupled prime–Gamma capstone in `LiEvenCrossActualClockPrimeGammaContour.lean`, with one radius for every real clock. Do not rename coefficient identity as an arithmetic positivity producer.
4. Seek a central arithmetic regularization whose clock interchange and signed cancellation estimate are independently controlled.

The strongest current survivor is exact phase-preserving continued-source identity. There is no new all-clock sign, negative literal witness, independently controlled prime-clock sum or RH conclusion. Neither far-right adaptive positivity nor scalar theta Hilbert norms gives this missing estimate. No route is retired.

## Log

- 2026-09-30 — Producer inspected exact central source/germ, finite prime convergence half-plane, multiplicity tomography and Guinand–Weil test classes. Root checked source definition, center germ, raw response factorials and explicit RH-equivalent half-plane analyticity statement. Independent arithmetic audit confirms coefficient transport but no source sign law. Card recorded before contour formalization or further hard proof work.

## Audited generic mechanism

For any complex function G holomorphic inside a positive-radius disk and continuous on its closure (`DiffContOnCl`), uniform boundedness of G on its circle and the entire sine series justify complete interchange. Cauchy derivative formula then gives

`∮G(z)sin(t/z)dz=2πi Σ_j (−1)^j G^(2j)(0)t^(2j+1)/[(2j)!(2j+1)!]`.

This works for every complex t and does not require G even; the contour selects even coefficients. This generic strengthening is the same dependency-closed Cauchy proof, not a new arithmetic premise. For the literal G, exact central germ identity makes the even coefficients real and identifies every coefficient with M_j. Existing installed Cauchy derivative API must be verified in the local toolchain before implementation.

- 2026-09-30 — Independent hostile contour audit passed, including common radius, complete uniform double envelope, coefficient reality and center residue sign. Promoted paper identity to stage two. Core arithmetic gap remains finite prime series domain versus central continuation; no RH-equivalent half-plane holomorphy assumed.

## Search and validation ledger

Documented deep query `exact reciprocal sine zero sum explicit formula prime archimedean von Mangoldt source central moment analytic continuation` (`--mode deep --budget-seconds 300 --explore 0`) returned partial results at generation/current 1145175, with unfinished semantic retrieval and reranking. Hybrid OR query `"reciprocal sine" "inverse tilted" "endpoint prime" "central source"` (`--any --explore 0`) returned partial reranking at generation/current 1145191, 183 lexical declarations in 44 modules. Complete inventories covered all 63090 files; semantic coverage unmeasured and compiler metadata mostly pending/stale. Both were source-only; evidence retained in producer tool transcripts, sessions 43735/71023. Independent source audit search returned useful source-only partial reranking at generation 1145201/current 1145202. Source applicability was checked directly; no world-novelty or corpus-wide absence claim.

Owned packet/response-height integration is final and wired. Authoritative `scripts/formal_tools.py index` exited0 (six changed files); `scripts/formal_tools.py lint` exited1 with 19 unrelated unreachable modules. No proof-debt error was reported in that run. Evidence: `/tmp/hgt-li-packet-response-height-{index,lint}.log`. Global formal gate is not green.

- 2026-09-30 — [Paired integer central source](../3-formalized/li-clock-paired-eta-central-source.md) is now formal: convergent complete arithmetic source, explicit source-only denominator floor, sharp finite tails and quantitative complex-clock contour error. Eleven leaves/63 public declarations passed named/final checks and foundational axiom audits. Literal growing-window approximation and normalized fixed-window positive fractions are formal. All-clock signed cancellation remains open; source identity alone is not an orientation producer.

## Lean verification

`LiClockCentralSineContour.lean` has four public declarations: exact coefficient definition, complete absolute summability, summability and contour identity for every complex t under only `r>0` and `DiffContOnCl`. Named build passed (2713 jobs, own leaf6.2s), final exact source check empty, all four axiom audits foundational. Evidence retained in current-agent tool sessions27770(named),77559(direct),27435(axioms); no filesystem logs were created. Root read complete134-line proof.

`LiEvenCrossActualClockPrimeGammaContour.lean` has exact public `exists_liEvenCrossActualClockPrimeGammaContour_radius`: common radius, both normalized source integrals, every real clock. Named build passed (9522 jobs, own leaf57s), final direct check empty, public axiom audit foundational. All source-side radius, filled normalization and complex coefficient helper proofs were checked separately before composition. Evidence: `/tmp/hgt-li-clock-prime-gamma-contour-{build,direct,axioms}.log`; helper/source scratch evidence `/tmp/hgt-li-clock-prime-gamma-contour-{helpers,work}.log` and `/tmp/li_pole_contour_source_proofs.log`. Root read proofs and all own evidence. Both imports wired into `RHTower.lean`.

- 2026-09-30 — Promoted exact all-clock contour theorem after both leaf named/direct/axiom checks. Five public declarations foundational. Integer eta source representation and quantitative approximation remain on their separate stage-two card; no all-clock signed cancellation or RH claim.
