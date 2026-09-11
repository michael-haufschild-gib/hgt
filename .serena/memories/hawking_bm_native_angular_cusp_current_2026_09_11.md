# HB native angular cusp current — verified 2026-09-11
Goal remains ACTIVE. RH and complete physical-current cancellation are unproved. Frontier map READ ONLY; no edits made. Universal STATUS unchanged (new result is route-specific). No Git, launch.sh, numerical experiments or subagents. One foreground Lean/Lake at a time; no dependency/full/umbrella builds. Only six newly created theorems had axioms audited.

Proof chain each new turn: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Hard target: 2 Omega(B(p,p)/2,B(m,m)/2)=0 with original source, clock, all physical boundary faces and independent SS/SV/VV.
Prior turn: actual physical lift horizon currents and source contacts closed (hawking_bm_physical_lift_horizon_current_2026_09_11); do not re-audit.

## Important ingredient found already complete
ThetaCuspHawkingBMNativeCausalEquality.lean, namespace RHTower.D4BMJointSource:
nativeJointResidual_eq_causalJointForcedResponse q branch a proves nativeJointResidual q (physicalRate q branch) a =ᵐ[volume] causalJointForcedResponse q branch a in original real-time Hilbert space. Uses original covariance Volterra equation, time primitives, contractive embedding, positive energy, injectivity; no native growth hypothesis. Stage3 hb-native-causal-equality.md read. Do NOT reprove uniqueness despite stale frontier text. Actual derivative/trace transport and complete current remain open.

## New verified owner
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeAngularCurrent.lean (411 lines).
Namespace RHTower.D4BMNativeAngularCurrent. Uniquely wired into RHTower.lean.
Stage3 docs/drafts/pipeline/3-formalized/hb-native-angular-current-cusp.md holds exact result/proof/validation.
Stage1 namesake full analytical card, plus updated hb-mixed-complete-current.md last scope paragraphs.

Definitions:
nativeField q p = mean q (p 0) (p 1) (p 2).
nativeRemainder q p = cuspMeanRemainder q (p 0) (p 1) (p 2).
E a p (private) = Complex.exp(a * p2).
principalJet q n p = sum_i A_i alpha_i^n powerCircle alpha_i p0 * exp(alpha_i*p2).
alpha = [2q,1,2-2q], A = [weylTrue²/2,weylTrue*weylFalse,weylFalse²/2].
No principal/source term deleted.

verticalGreen q d e X k =
exp(k)*(F_d,k F_e,XX - F_e,k F_d,XX)
+ exp(-k)*(F_d,k F_e,kk - F_e,k F_d,kk),
all actual ordered nativeJet derivatives of full mean.
principalFlux = exp(-k)*(P_d,k P_e,kk-P_e,k P_d,kk).
pairCoefficient q i j d e =
A_i A_j alpha_i alpha_j (alpha_j-alpha_i)
*(C_i(d) C_j(e)-C_j(d) C_i(e)), C_i=powerCircle alpha_i.
principalFlux exactly B01 exp(2q*k)+B02 exp(k)+B12 exp((2-2q)*k).

originalVerticalGreen uses actual ordinary height/horizontal derivatives of f_d(X,Y)=mean q d X (log Y):
F_Y * [Y²(G_XX+G_YY)] - G_Y * [Y²(F_XX+F_YY)].
Actual log-to-height dictionary proven, including both Jacobian factors:
originalVerticalGreen q d e X (exp k)=verticalGreen q d e X k.

Six public theorems (new only, all axiom-audited):
1 native_angular_jet_decomposition line151: full actual k,kk,XX jets = principal jets + actual full remainder jets.
2 principalFlux_three_channels line196: exact three original principal interactions.
3 weighted_native_remainder_tendsto_zero line228: any ordered word:List(Fin3), nonnegative radius, arbitrary horizontal path, every complex exponential height weight →0.
4 verticalGreen_cusp_expansion line284: for d,e:Ici0, arbitrary X:R→R,w:C, exp(w*k)*(verticalGreen-principalFlux) →0.
5 originalVerticalGreen_eq line380: actual height-coordinate dictionary.
6 originalVerticalGreen_cusp_expansion line401: same complete weighted expansion for originalVerticalGreen at Y=exp k.
13 API rows (7 defs + 6 theorems) verified.

Proof ingredients:
- NativeCircleGauss.powerCircle_eq_legendre; CausalSourceKernel.legendre_contDiffAt valid z>0 including characteristic z1.
- NativeResponse.nativeMean_joint_smooth.
- NativeCuspJets.nativeCuspJet_rapid_bound for all words, compact radius, arbitrary horizontal x.
Choose natural N>Re(w), norm bound proportional exp((Re(w)-N)*k). Shift w by each principal exponent for mixed principal/remainder products; weighted/unweighted product for two remainder jets. Principal diagonal cancels, pair orientations antisymmetrize.
Actual slice derivatives via Function.update, then log_first/log_second. No artificial jet assumptions.
Fixed radii only for current theorem. Radius derivatives of reconstructed fields and passage through original causal integrals still needed. No finite-part prescription, raw flux vanishing, physical-current equality or RH claimed.

## Validation
lake env lean scratch: clean.
Isolated lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeAngularCurrent: passed, 208s, 3 jobs. 4135 own cached dependency modules, 20531 hardlinked artifact files reused, all 12 path dependency stubs; no dependency/umbrella build.
All six axioms: exactly propext, Classical.choice, Quot.sound.
Source + .olean/.ilean/.olean.hash/.ilean.hash/.trace installed byte-identically from audited input/artifacts.
Umbrella import exactly once. 12 local links across 3 cards resolve.
scripts/formal_tools.py index: terminal0, generated API/GAPS/OVERVIEW, search cache 0 changed (already indexed), 13 new module API rows verified.
Global lint terminal1: SIX unrelated umbrella reachability errors:
RHTower.EulerDeletionSignatureWordExpansion;
RHTower.Sieve.MenonHarmonicRamareLadderSwapped;
RHTower.Sieve.MenonHarmonicRamareLadderSwappedVolume;
HTGeometry.WeightedMinimax.Alternation;
HTGeometry.WeightedMinimax.Coefficient;
HTGeometry.WeightedMinimax.Perturbation.
No error for our module. Do not claim global gate passed or modify other ongoing modules blindly.
All owned Lean/Lake/check/build/index/lint handles terminated. Cleanup of exact owned /tmp directory and four search JSONs follows this memory write.

## Searches and next attack
Own deep searches: reciprocal/concomitant OR, complete forced-wave causal reciprocity, Lagrange identity, even smooth square root. Partial generation823339; inspect candidate_lemmas/source_arguments/methods/ingredient_sets, many source-only unverified candidates, no applicable closure theorem. Do NOT read search implementation/help or run launch.sh.
Recent own broad arXiv words symplectic, bisolution, Peierls:
2609.04164 A Superconducting Peierls Instability (Sep3 2026), 2608.22517 Anomalous dynamical energy flows via nonlinear phononics in spin-Peierls chains (Aug23 2026), primary abstracts inspected; no applicable HB theorem or proof premise.
Next substantive target: carry explicit three antisymmetric cusp coefficients (and radius derivatives required by reconstruction) through original causal source integrals, combine with source contacts and temporal/radial faces. Then independent SS/SV/VV. Avoid repeating native/causal uniqueness, prior lift-horizon calculations, or proving only an insufficiency/no-go.
Original source-producer full four-divergence transgression remains paper proof; CommonSourceGreen supplies actual common producer transposition and 3-current finite characteristic identities. Actual physical current cross-response cancellation still not established.