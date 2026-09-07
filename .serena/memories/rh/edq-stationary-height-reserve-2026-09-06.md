# EDQ stationary height reserve — verified component; RH remains open

Active goal is unconditional closed Lean proof/falsification of RH via EDQ. Neither achieved. Keep goal active; no genuine external blocker. Previous SQC component was verified progress; this turn SHR also changes proved source inequalities.

## New leaf and statements
`formal/GaloisForLFunctions/RHTower/ArithmeticStationaryHeightReserve.lean`: 386 lines, 30 declarations (25 theorems, five definitions), namespace RHTower.DeletionMixedRefinement. Imports existing ArithmeticStationaryEndpointOrientation and PrimeLogZetaAbelPole. Wired once after ArithmeticStationaryQuadrantComparison in RHTower.lean.

J_beta(t,v)=integral_Ioi1 x^-beta sin(anchoredLogPhase 1 t v x). Exact positive dilation proves Im A(s,N,k)=w_k J_(sigma+2)(t,2*pi*k*N). The already proved logarithmic power moment integral x^-beta log x=1/(beta-1)^2 and sine Lipschitz give |J_beta(t,v)-J_beta(u,v)|<=|t-u|/(beta-1)^2. Thus same-real-part actual atoms differ in imaginary value by at most w_k*|delta t|/(sigma+1)^2, independent of N and phase frequency.

For beta>2,v>0, E_beta(v)=J_beta(-v,v)>0 from prior positive endpoint integral. Define stationaryHeightReserve beta v=(beta-1)^2*E_beta(v)/2>0. Exact compensated positive density representation proved. At v<=t<=v+r, J_beta(t,-v)<=-E/2. Combining prior t<=v negative sign gives actual negative Fourier atom Im<0 through t<=v+r. Power mass |J|<=1/(beta-1) proves r<=(beta-1)/2; in 0<sigma<=1, 0<r<=1.

stationaryBeyondReserveIndices filters original stationary negative frequencies to v+r<t; stationaryBeyondReserveBudget is actual reduced sum. stationaryReserveMass M_N sums w_k E/2 over removed collar modes; M_N>=0. Exact original S_N satisfies S_N<=B_N-M_N. IMPORTANT: this is an upper envelope after estimating removed terms, not a numerically tighter bound than retaining exact original S_N. It improves mere deletion by retaining guaranteed negative margins and reduces number of unknown terms.

Full source: N^(2sigma+1)*Im g_s(N)<=B_N-M_N+1/[12*(2*pi*N+t)]-t/[12normSq(s+1)]. In usual strip and t>=1, scaled Im g<B_N-M_N. r<=1 and 2*pi*N>1 put first collar below second threshold, so reduced sector empty for t<=2*pi*N+r_(sigma+2)(2*pi*N). `normalizedWeightedRemainder_im_neg_of_first_height_reserve` proves complete remainder strictly negative throughout this extended cutoff. `riemannZeta_ne_zero_of_first_height_reserve` excludes actual closed-right strip zeros in corresponding unit chamber (sigma>=1/2,<1,t>=1).

Zero lower bound for B_1 includes old displacement/mean/ceiling lower bound PLUS M_1. Every closed-right zero forces B_1>M_1. `exists_positive_first_harmonic_beyond_height_reserve_at_closed_right_zero` strengthens actual positive-witness extraction to v+r<t. Includes critical zeros and is not RH selection.

## Audits DONE — do not repeat
Scratch completed without warnings. Final foreground LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticStationaryHeightReserve compiled EXACTLY ONE leaf in 4.9 seconds. 9900 jobs were dependency traversal/replays, not compilations. New-only /tmp axiom audit exact-matched all 30 declarations; only propext, Classical.choice, Quot.sound. No prior source rebuilt or re-audited. Own-tree full declaration basename collision search passed. Final target source count, exact audit-name coverage, single umbrella import, certificate and whitespace checked; git diff --check passed.

Global formal lint FAILED only on concurrent unwired modules outside this work: RHTower.ThetaCuspCenterCompensationFlux, RHTower.ThetaCuspCenterMixedAllOrderIntegration, HTGeometry.AlternatingPairJetIntegral (all under GaloisForLFunctions). Do not change unrelated work or repeat unchanged lint. Index refreshed once: 32739 files, 399729 declarations, 3909 gap markers.

All owned Lean/Lake handles terminal (probe66481; scratch2356,86656,82521,23460,15254,53932; build4938; audit8845; lint62201). Process check found no own Lean/Lake. Removed /tmp/edq_height_reserve_probe.lean, edq_height_reserve.lean, edq_height_reserve_axioms.lean, edq_height_reserve_names.txt. Logs retained /tmp/edq_height_reserve_{build,axioms,lint,index}.log. No computation/numerical certificate or added axiom. No commits.

## Docs and next frontier
Promoted certificate `docs/drafts/pipeline/3-formalized/edq-stationary-height-reserve.md`; contains complete paper proof, exact scope and audit records. Updated current EDQ main paragraph and row in frontier map. STATUS existing rule 'Must retain the exceptional initial terms after proving a uniform tail sign' updated with positive source-reserve cutoff and lack of uniform lower bound. Source-only reserve positivity is proved but no uniform positive lower bound across varying parameters is claimed.

Remaining RH gap: signed comparison of whole remaining strict stationary head against exact opposing sectors and mean, or joint-source signature orientation. Shrinking threshold collars alone does not solve the high unit head. Next work should seek that whole-head comparison or an actual cancellation law; avoid substituting more coordinate changes or small cutoff extensions for the required global source law. Older endpoint, quadrant, dilation, frequency-budget proofs and audits are complete; do not repeat them.