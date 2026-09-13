# HB original causal potential — 0913ai

RH remains UNPROVED; unbounded goal active. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Main missing physical action incidence and extinction are not proved here.

## New closed result
New 230-line `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalCausalPotential.lean`, namespace `RHTower.D4BMOriginalCausalPotential`, import NativeAngularGreen. Define `Z=fullNullResponse q s a p r X k + radialLift s 0 a 1 ((p-r)/2)*timeOnset(2*s)p*fullSquarePotential q ![X,exp k]`, s=physicalRate q branch.
- `originalPotential_wave`181: for 0<p<=r, actual mixed null derivative obeys 4 Z_pr − angularLaplacian(Z)/cosh((p-r)/2)^2 = timeOriginalForcing q branch a ((p+r)/2)((p-r)/2)![X,exp k]. Full original gradient source, original amplitude and fixed onset retained; no source-ID/equation premise. Geometric domain conditions are explicit. This is the original scalar potential equation, NOT full metric/Einstein action incidence.
- Public `originalPotential_first`159 and `originalPotential_mixed`168 give actual HasDerivAt statements; exposed so future metric work does not have to reproduce derivative existence from an equation of totalized deriv values.
- `originalPotential_angular_smooth`153 joint angular C∞.
- `originalPotential_boundary`210 zero p=r for all real p.
- `originalPotential_before_onset`215 zero p<=0.
- `originalPotential_modular`221 actual SL(2,Z) invariance.
- Lift null derivatives: liftFirst=L' eta/2+L eta'; liftMixed=−L''eta/4−L'eta'/2. Exact original time gradient absorption cancels differentiated-onset cross term.
- Source log-coordinate Laplacian derived from native mean_laplacian_commutes at radius zero and mean_zero. Generic second_add plus genuine C∞ angular slices justify angular derivative linearity. No added axioms/computations/heartbeat increases.

Modified only by appending three public API lemmas to existing `ThetaCuspHawkingBMFullNativeWave.lean` (now1972lines): fullNullResponse_differentiable_first, fullNullResponse_differentiable_mixed, fullNullResponse_nonpositive. Proofs use already internal fullResponse_first/fullEffective continuous FTC and responseJet_nonpositive. Existing proofs and definitions unchanged. This API closes the existence gap needed to differentiate sums with the explicit lift.

## Validation/wiring/cleanup
Scratch `lake env lean /tmp/...` passed; no #print axioms. Exact isolated leaf audit FullNativeWave passed14s (only leaf built,2656 cached jobs); OriginalCausalPotential final passed27s [2/2]. A prior34s leaf pass was followed by exposing first/mixed APIs publicly and the final27s audit. Artifacts installed atomically. New leaf wired after NativeAngularGreen in RHTower line17410; NO umbrella build.
One lint invocation: only global error unrelated `GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionCoprime` unreachable from umbrella; existing large-file warnings, FullNativeWave included. No active sorry/admit/axiom declaration issue. Do not alter concurrent unrelated module.
Exact lexical research found originalPotential_wave. All owned searches and Lean/Lake handles terminal. Removed /tmp/hb-audit-stage-0913ai (unlinked packages symlink first) and18 owned temporary files. No owned Lean process remains. No Git, launch, mathematical computation, subagent, frontier edit or STATUS edit.

## Durable docs
Own facts log `docs/drafts/pipeline/1-in-progress/hb-own-research-facts.md` now F01–F93/N01–N04. Added only F92 original causal source equation and F93 angular/modular/boundary/onset properties. Main card `hb-physical-mode-action-contact.md` last section Original causal potential in null coordinates contains proof and precise remaining bridge. Frontier read-only. STATUS no new route-independent fact.

## Avoid rediscovery loops
The full causal kernel convolution was ALREADY constructed and solves its forced wave equation in FullNativeWave (599), Dirichlet (662), Goursat (626). NativeAngularGreen already gives fullNullResponse_angular_smooth249. NativeModularTransport already gives fullNullResponse_modular213. Do NOT re-conjecture these as missing.
The major previous ah result is still `ThreeFieldMetric.literalMetric_einstein` (all16 actual SS sourced Einstein components); do not redo scalar-angular tensor vanishing, three-field reconstruction or horizon cancellation.
Current result does NOT assert joint spacetime C2/C3, full spin-two metric reconstruction, original raw mixed source B(S,V) admission, left-QNM incidence, or extinction. Raw source still B+L(k)=T and full Peierls pairing keeps all four correction terms; see card opening.

## Concrete next analytical bridge
`ThetaCuspHawkingBMOnsetGreenReconstruction.originalForcing_retarded_reconstruction`1027 already proves actual original retarded direct/image action equals lift − original angular seed/parameter + unchanged onset pulse action/parameter. `retardedNullAction_lift_wave`838 already reconstructs the lift.
To identify the newly restored Z with the actual retardedNullAction(timeOriginalForcing), prove native fullNullResponse equals retardedNullAction(timeReducedCoefficient*F). Its native odd-source rectangle 0<=a<=p,0<=b<=r splits at a=b. Lower triangle source is minus the swapped original source; swapping a,b gives the reflected image triangle. Upper triangle gives direct action. Preserve one-quarter kernel/null Jacobian and source signs. Then use gradient absorption, finite-integral linearity, and existing retarded lift identity. No inverse-uniqueness assumption needed. This bridge is an analytical mechanism, NOT formalized here. Beyond it, actual mixed metric/action and boundary trace pairing remain central obligations.

## Search evidence
Many broad/deep searches this continuation: retarded, causal source equation, boundary/current OR, fullNullResponse, even, smooth even square root, split source rectangle into direct/reflected triangles. Inspected candidate_lemmas/source_arguments/proof_ideas/ingredient_sets and coverage; most source_only. Some deep requests partial; generated ingredient_sets for triangle query irrelevant apart from real triangle_swap lemma. FullNativeWave private triangle_swap402 and NativeSourceEquation private triangle_swap33 have exact continuous triangle Fubini proof using restricted indicator rectangle; read useful402–446. No general smooth even-root descent found. Do not infer absence from partial searches. The arcosh endpoint regularity detour was not needed for this null-coordinate source attachment.
Broad arxiv searches transmutation/absorbing/characteristic found old unrelated material; opened arxiv2210.02246 (2022, transmutation review). No 2026 theorem applied or claimed.
