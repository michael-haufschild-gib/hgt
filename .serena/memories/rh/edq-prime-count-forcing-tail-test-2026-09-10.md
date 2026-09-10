# EDQ endpoint transfer verified; forcing tail-test paper proof

RH goal ACTIVE, not achieved. This turn made PROGRESS, not an external block. Frontier map read-only and untouched; no STATUS edit because existing absolute-scale rules already cover the findings. No numerical experiment, no commit, no subagents.

## Completed Lean
formal/GaloisForLFunctions/RHTower/EulerDeletionPrimeCountEndpointTransfer.lean imports EndpointVariance and CoefficientPrefixEnergy.
Five new public theorems:
- RHTower.DeletionCoefficientTransfer.endpointJet_error_energy_le
- RHTower.PrimeCountDamping.jetCoeff_eq_primePower_convolution
- RHTower.PrimeCountDamping.sum_jetCoeff_smul
- RHTower.PrimeCountDamping.endpointJet_eq_primePower_packets
- RHTower.PrimeCountDamping.jetHarmonic_eq_primePower_harmonic.
Scratch passed warning-free. Final leaf-only lake build --old passed, ONLY new module compiled186s,13644jobs includes cache. Separate /tmp axiom audit all5 only propext/Classical.choice/Quot.sound. DO NOT re-audit these or earlier core8/variance13/amplification15. Umbrella wired, no umbrella build. Index refreshed4changed including foreign changes; lint passed existing large-file warnings only. Deleted obsolete docs/drafts/pipeline/1-in-progress/edq-endpoint-transfer-draft.lean.txt and replaced its only card reference.
Foreign broad build stopped leaving2missingimports. Only Sieve.MaynardLongAmplitudeExclusion90s and MaynardEndpointReserve5.4s restored individually --old. All owned Lean/search/index/lint processes ended.

## Card and next actual mathematical target
docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md new sections at2360 onward, tail-test near2577 (lines can shift). Read bounded sections. Existing mem:rh/edq-prime-count-endpoint-transfer-2026-09-10 describes earlier core8 and still has stale pending5 status; this memory supersedes that status.

Full chain Euler deletion -> cofinal subpower bound on COMPLETE SIGNED physical source -> exclude off-line zeros -> RH. Actual mixed covariance still open. Relative profile errors cannot close it.

Use full-ray representatives b=fract(x)/x, b_n=(fract(x/n)-fract(x)/n)/x; b_n=0 below1. G_N=sum mu(n)b_n, a_N=sum mu(n)/n.
Paper exact:
b_qm=D_q b_m+b_q/m, D_q f(x)=f(x/q)/q, norm² scale1/q.
J_N=-sum_(q primepower<=N)[D_q G_floor(N/q)+a_floor(N/q)b_q].
Thus both propagated part and harmonic forcing needed in <G,J>.
Centered Ramaré incidence lemma requires sum c=0; actual physical c sums to G, so no sign transfer.
Universal accretivity false: N4, a1=0,a2=1,a4=t -> sourceb2+t b4, primepower responseb4, mixed pairing runs through all real values. b1 invisible but its response atN2 isb2. Positive survivor is now-formal vector convolution, NOT route retirement.

## New paper forcing result (not Lean)
P_L=sum_primepowers<=L b_q.
B_N=sum_q a_floor(N/q)b_q=sum_m mu(m)/m P_floor(N/m).
Full proposed L2 profile logN B_N(Nx)->h(x)=sum_m mu(m)/m j(mx), j(x)=integral_x∞ fract(v)/v².
Norm bound P_L<<sqrtL/log(L+2) from PNT Q(L)~L/logL and Abel. Prime-power normalized counting measures + full-ray L2 Phi_u continuity/head bound give logL P_L(L.)->j. m-tail split sqrtN gives C sum_m>M m^-3/2+O(logN N^-1/4); fixedm dilation handles floor. Detailed proof on card, not formalized.
c2=sum mu(m)/m²>=1/4 by sum_m>=2 m^-2<=3/4. Periodic primitive F=(fract²-fract)/2 gives |j(y)-1/(2y)|<=1/(4y²). Hence h(y)=c2/(2y)+error <=sum_m m^-3/(4y²), h(y)>=1/(16y) fory>=8. h nonzero.
h is NOT scalar*j: derivative jump atx1/2 is4sum_even mu(m)/m²=-4c2/3; j derivative continuous there. Locally uniform function and derivative-majorant arguments justify one-sided limits.
A_m f=f(m.)/m, normm^-3/2, multiplicative. Absolute operator sums T=sum mu A_m and Z=sum A_m are inverse via divisor sum. h=Tj. This is paper, no Lean. Not new missing positivity.

### Stronger shortcut: forcing lower bound without full profile limit
W_N=sum_q a_floorN/q, V_N=sum_q a_floorN/q/q, R_N=sum_q |a_floorN/q|(q+1/q).
PNT +m-tail split yields W_N~c2 N/logN.
|V_N|<=H_N².
R_N<=K N²/logN from |a_M|<=H_M and positive double-sum reversal; q+1/q<=2q; use sum_m m^-3/log(2+N/m).
g_T(x)=1_(x>=T)/x, norm²1/T.
Exact <b_q,g_T>=[j(T/q)-j(T)]/q.
Error from(1-1/q)/(2T) bounded(q+1/q)/(4T²).
Thus <B_N,g_T> >=(W_N-V_N)/(2T)-R_N/(4T²).
Choose c>0 with W-V>=cN/logN, A>=max(1,K/c), T=AN.
Pair>=c/(4AlogN), so ||B_N||²>=c²/(16A) N/log²N eventually.
DEPENDENCY-CLOSED PAPER proof, NOT Lean. Good next formal target: general tail-test lower certificate plus actual PNT weighted counts. Does not prove RH; shows actual forcing size requiring signed cancellation.

### Finite inversion is NOT a new obstacle
Search found FloorTransformHarmonicInverse.lean; read1-175. Scalar exact comp and inverse alreadyclosed. Vector finite regrouping on paper gives P_N=sum_d B_floorN/d/d. Both transforms preserve UNIFORM N^epsilon norm ceilings epsilon>0 via sum d^-1-epsilon. Does NOT transfer only cofinal-subsequence ceilings. Therefore don't call moving-cutoff inversion itself open; actual pairing after combining B and propagated source is open.
Compressed full-ray T can preserve tail carrier by projection because A_m sends x>=1 to mx>=1; inverse semigroup still works. Not documented oncard yet. It does NOT automatically preserve zero-detector annihilation / BD generating span. No claim of RH via inversion.

## Searches and external papers
5deep/method OR queries180s max2rounds, all lanes inspected. Partial coverage822592..822612, source-only, no proofideas/ingredientsets. Primepower querysemanticQdranttimeout; no runtime restarted. No corpus absence claim.
Useful source reads:
- RouteERamareIncidenceConditionalNegative1-255: exactcentered assumption.
- EulerDeletionMobiusCurrentEscape1-200.
- EulerDeletionQuotientHarmonicBound1-160: harmonic floor bound ALREADY exists.
- EulerDeletionMobiusPeriodCovariance290-335: completeperiodmean exact, not physicalweights replacement.
- MobiusAdditiveDilationDiagonalizationwhole~110.
- SoninEulerInversePolarCorner1-100,230-315: ONE PRIME positiveweightinverse, not our all-integer profile inverse.
- FloorTransformHarmonicInverse1-175.
Do not reread all unrelated files.

Broad arxiv hysteresis/ergodicity searches, newest. Read Brown-Rosenthal-Zhou2609.07819v1 sections5.1-5.3 proof: finiteexcursion symmetricrandomsign covariance embedding; mayfactorreversiblekernels but chainnotreversible; no actualEDQ randomization or tightness.
Read Jha-Dayal2609.06354v1 AppendixC electrostaticDiraccorrection; boundaryretention methodological only, no stochastic identification.
Citations oncard. No externaltheorem used inLean.

## Efficient continuation
Use lake env lean /tmp/... foreground only oneownLean. Newleaf final lake build --old MODULE only. No umbrella/full builds. Newaxioms only. SharedCPU makes imports2-4min; don'trestart ifCPUtimeprogress. For EndpointVariance importedclosure preflight use .lake/build/ir/...EndpointVariance.setup.json importArts missingpaths. No active ownprocess remains.
Five proof repair: unfold PrimeCountDamping.endpointJet before rw reverse private range_shift_eq_Icc. Remove unused Complex.ofReal_intCast from real_smul simplification. convert! handles reducible casts.
