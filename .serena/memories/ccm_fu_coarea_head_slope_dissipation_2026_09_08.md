# CCM-FU: coarea head slope, actual growth, and general prime dissipation

Goal remains ACTIVE and unbudgeted. RH not proved/falsified. This turn is PROGRESS: one independently audited RunPod falsification plus twenty kernel-checked new theorems in three leaves, including a new all-prime monotone quantity. Frontier map remains strictly READ ONLY. No subagents, commits or pushes. No owned Lean/remote job remains, and all owned /tmp scratch/audit dirs removed. Foreign Lean process /tmp/hb-endpoint.5PQBeIvU/api2.lean was running at cleanup; do not kill it.

## Current artifacts
- formal/GaloisForLFunctions/RHTower/MobiusDivisorCoareaHeadTransport.lean (12 public theorems, 4 definitions).
- formal/GaloisForLFunctions/RHTower/MobiusDivisorCoareaInitialSlopeGrowth.lean (4 public theorems).
- formal/GaloisForLFunctions/RHTower/MobiusDivisorCoareaSlopeDissipation.lean (4 public theorems).
All three wired consecutively after MobiusDivisorPositiveNormalizationCost in RHTower.lean. Do not umbrella build.
- docs/drafts/pipeline/5-failed/ccm-fu-coarea-mass-envelope.md: frozen candidate, empirical failure, dependency-closed positive proofs, remaining core, exact verification status.
- docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-coarea-mass-envelope-2026-09-08/: source_screen.py, screen.py, summary.json, audit.py, audit.json, README.md. These are numerical guidance, no Lean negative certificate.
- Universal STATUS gained route-independent Cannot reverse invariant growth by subdividing or reordering its increments, with proof link. Frontier map not edited.

## Exact new mathematics
C_d = actual signed divisor coefficient. A_R(M,P) sums original |C_d| in retained label R; F_R signed sum. Define a=A_empty, f=F_empty, K=sum over nonempty retained labels of F_R^2/A_R (zero masses contribute zero). New head action H=f^2+aK; slope g=K-a-2f.
HeadTransport proves A>=0 and |F|<=A; exact isolated late-prime A support and update; K' = K-b for fresh prime p<M with M<=2p, b=|C_p|. Such prime has coefficient -b and updates (a,f,K)->(a+b,f-b,K-b). Consequently g is invariant, H'-H=b*g. Full fresh late-prime block L: g(P union L)=g(P), H(P union L)-H(P)=(sum_L |C_p|)*g(P). Positive total block mass makes action nonincrease iff g<=0. The head action equals a times complete conditional energy, including zero mass; if a is the largest absolute cell mass, Q(P)<=H(P). This dominance persists under late-prime insertion. No favorable source sign g<=0 is proved.

InitialSlopeGrowth proves a(M,{2}) <=(6/5)sqrt M (head contains indices1,2 only). For ALL N including0, K(4N,{2})>=LatePrimeMass(4N). Thus g(4N,{2})>=LatePrimeMass(4N)-4sqrt(4N). Existing unconditional prime-window mass theorem has LatePrimeMass(4N)/(4N)->infinity, so NEW source capstone tendsto_mobiusDivisorCoareaHeadSlope_two_div_atTop proves g(4N,{2})/(4N)->infinity without hypotheses. This supplies actual eventual positive slope after prime2; late-prime reordering/subdivision/batching cannot reverse it.

SlopeDissipation proves for EVERY prime p<M and EVERY P (freshness and fibre-sign assumptions unnecessary): K(P union{p}) <= K(P)-F_p^2/A_p. Exact head updates then give
  g(P)-g(P union{p}) >= (F_p+A_p)^2/A_p >=0.
This is a genuinely general all-prime monotone quantity. Names: mobiusDivisorFibreAbsoluteMass_insert; mobiusDivisorNonemptyCoarea_insert_le; mobiusDivisorCoareaHeadSlope_insert_loss_ge; mobiusDivisorCoareaHeadSlope_insert_le. Scalar proof uses weighted conditional Cauchy on every nonempty complementary pair, preserving all signs/zero mass cases. The forcing term vanishes for isolated pure negative late primes; transverse conditional variances account for remaining decrease.

## Hard remaining producer
Full chain actual source -> uniform signed-energy control through exhaustive prime order -> O(M) Abel bound -> CCM-FU -> RH. Need joint control of g dissipation and growing absolute/signed head mass, not another bare contraction identity. Initial g after2 is large positive. Late primes can change head mass without lowering g; mixed small/middle prime mergers lower g. A schedule must balance these operations with quadratic head-action/raw energy ceiling. No such schedule or critical quantitative rate proved.
Useful algebra, not yet new formal lemma: H=(f+a)^2+a*g. g-drop >= shifted singleton energy. Pure g-loss maximization could postpone zero-loss late primes; any rule that postpones ALL isolated late primes until the full half-prime core is already excluded by existing MobiusDivisorLatePrimeHeadAsymptotic (half-core head grows superlinearly). Do not run a predictable experiment merely rechecking that barrier. No next experiment is frozen yet.

## RunPod diagnostic, frozen before running
Candidate B(P)=max_R A_R * sum_R F_R^2/A_R. Greedily choose smallest next B among ALL remaining primes p<M, ties increasing p, start P empty, run to completion. Four workers M512,1024,2048,8192. Strict gain threshold1e-10 max(1,B0). Screen6.666s, audit0.481s; each90s internal/100s outer timeout, BLAS/OMP1thread. No local mathematical computation. Remote /root/ccm-coarea-envelope-EsKZia fully removed.
Results (M, steps, strict-positive steps, peakB/B0, peakQ/Q0):
512,97,48,2.253066348,1.262506594;
1024,172,99,4.061133589,2.314992485;
2048,309,174,6.679569481,3.892478855;
8192,1028,623,21.89847261,15.80035298.
80-digit ORIGINAL TIME-SUM audit checks every greedy prefix choice through earliest trap at M512, P=[2,479,509]. Every remaining prime increases B; min503 gain0.7176745122862473498, next choice margin0.876300502809716. g approximately63.504668288870557 after2 and unchanged through479,509. Head mass reaches largest-background boundary when503processed. No interval arithmetic or Lean sign certificate. Finite peak ratios do not prove asymptotic unboundedness or reject every other prime order.

## Validation done; do NOT repeat
All three scratches and installed exact leaves passed lake env lean. New oleans emitted only. All20newpublic theorems #print axioms audited exactly once (12+4+4), only propext/Classical.choice/Quot.sound. No old audit. Final isolated exact-module lake builds sequentially passed: HeadTransport5.8s3jobs, InitialSlopeGrowth7.0s4jobs, SlopeDissipation4.6s4jobs. Only3newleaves compiled, zero dependency rebuilds. Sources byte-identical verified. Temp package removed. See mem:ccm_fu_positive_normalization_cost_2026_09_08 for empty-glob cache package technique; missing stub manifests produce packaging warnings only. No full/umbrella build.
Indexes regenerated once. Global formal lint ran ONCE and failed SOLELY because foreign SelbergMaassAugmentedDirection, SelbergMaassChordEnergy, SelbergWeightedPathEnergy were unreachable from RHTower. None of those3imports existed at final check; files not ours and not edited. No passing global lint claimed. Re-run lint only after evidence owner wired them; do not repeatedly rescan unchanged failure. Own imports, docs links, source copies and whitespace passed. New files remain untracked, as user did not request commit.

## Search/read notes
Broad OR research used explicit --any for alternative mass/variance/signed coupling/conditional mixing/parity balance, then coupling/coarea/Stein/entropy/conductance (5175 declarations1002modules), maximumcell/largestfibre/conditionalenergy/massgrowth (13/8), slope dissipation/absorbingenergy/coarea forcing (4/2). Targeted AND coarea head slope was intentional. Initial query refreshed search index; most later broad queries --no-refresh. Read current frontier CCM-FU section (read-only), previous normalization card, scientific-method.md. Explored RouteECofactorUnsignedMass, RouteEOppositeParityMetropolisRejection, RouteEDegreeNormalizedGibbsBoundaryVariation, MobiusBoundaryOppositeSignTransport surfaces: their accepted-flow/Hall/comparison rates remain unsupplied. Used actual LatePrimeFibres and LatePrimeCompensation rather than training assumptions.
Mathlib gotcha: Real.sqrt_le_self does NOT exist; Real.sqrt_le_self_iff does, in Mathlib/Analysis/Real/Sqrt.lean. Finset subset_singleton_iff gives s=empty OR s={a}. rw if_neg rewrites only one visible occurrence; use simp only [if_neg ...] for paired signed/absolute updates. Real square/div absolute needs zero case, proven by div_eq_iff + sq_abs; no computed certificate.
