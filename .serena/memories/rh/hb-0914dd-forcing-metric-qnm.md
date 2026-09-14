# HB DD: original forcing boundary through temporal/metric/QNM restoration

2026-09-14, cwd /Users/michael/Documents/code/hgt, Lean 4.32.2. Active unbounded RH/HB goal remains open. Full temporal/metric/QNM matching and impossibility remain unproved. No numerical computations, experiments review, frontier-map edits, Git, launch.sh, axiom printing, heartbeat/transparency/instance hacks, umbrella builds or subagents this turn.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Immediate target remains full temporal/metric/QNM matching or impossibility. Prior source-product estimates: mem:rh/hb-0914dc-angular-product-joint-matching.

## Four finished leaves
All have clean scratch checks with LEAN_NUM_THREADS=2 lake env lean /tmp/...; exact isolated leaf audits with lake build Exact.Module; authoritative .olean/.ilean present; source bytes equal audited source; umbrella imports wired without building umbrella. Global scripts/formal_tools.py lint passed (existing large-file warnings). One foreground owned Lean/Lake command at a time. All four audit sessions terminal EXIT0. Temporary cleanup follows this memory write.
Prefix formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBM:
1. OriginalFixedForcingProducts.lean, 151 lines, SHA256 2b2ec45a4b50c53b857f02eb7dcacbb60f3079409f36a63cf96dac22beb19101. Audit 7.8s, 2 jobs.
2. OriginalForcingProductBounds.lean, 359 lines, SHA256 723935ad9aa5dc6ca13098461d2694677905226304cd70193597f3b5b6ae5e82. Audit 32s, 2 jobs.
3. OriginalMetricForcingMatch.lean, 194 lines, SHA256 d2953d48bff515193f93dc02ffba69471950e2114dd33e08014c55a4050357a5. Audit 77s, 2 jobs.
4. OriginalForcingBoundaryQNM.lean, 287 lines, SHA256 3dc06906c630c350d5787618986810b9724fa6b6d35b3af04912973520471c3a. Audit 143s, 2 jobs.

## Mathematical closure
Namespace D4BMOriginalForcingProductBounds (leaves 1–2):
- sourceField(q,b) = fullSquarePotential if false, fullGradientEnergy/2 if true. sourceCoefficient = principalAmplitude or canonical principalGradient. sourcePrincipal retains all three K=(2q,1,2−2q) powers; sourceRemainder = sourceField−sourcePrincipal.
- fixedProduct(q,br,b,d,x,k)=J*G_d−P_J*Q_d, with actual angular reader value/ordinary height derivative. fixed_product_decay: every N, norm≤C exp(−Nk), all x,k≥0, both fields, both reader operations, both physical source branches. Keeps all principal/tail cross terms.
- reader_smooth_coefficient_error48: n_L F(u_L)−beta F(1) ≤ C(exp(−L)+exp(−Re(w)L)) for smooth-at-1 F, nonreal Re(w)≥1.
- normalizedProduct138: original timeOriginalForcing/Z times angularJet minus onset*all three profilePrincipal products, times unchanged n_L. horizonProduct145: actual forcingTrace and horizon principal products times beta.
- original_forcing_product_error184 and time_error226: C S exp(−Nk)exp(−p), time integral removes exp(−p), uniform T≥0.
- rawProduct257 retains original forcing before /Z; raw_product_factor263 gives raw=Z*normalized.
- metric_forcing_product_time_error292: norm(R²*int_0^T exp(−wp)(raw−Z*horizon)/f²)≤C exp(−Nk), f=R²−1. Exact R² Z=f, not a guessed metric normalization. metric_forcing_product_joint_limit342 covers arbitrary T(L,k)≥0 and X(L,k).

Namespace D4BMOriginalMetricForcingMatch (leaf 3):
- physical_mode_normal29 gives actual normal derivative of modeScalar.
- mode_amplitude_collar49: actual modeAmplitude=R exp(−wp)n_L. radiusLift is R*modeProfile, NOT reciprocal radius.
- forcing_principal_collar62: each existing OriginalCompactBoundary.forcingPrincipalCoefficient = Z*onset*profilePrincipal(u_L,i).
- forcingTransferCut99 is actual T(F,W) minus all three existing modeTransferCoefficient(j=3) powers.
- forcing_transfer_cut106: cut=R exp(−wp)rawProduct(d=true).
- metricForcingBoundaryError133 uses actual complete-boundary coefficient −wR/f². metric_forcing_boundary_error137 attaches exactly to leaf2 weight R²/f².
- physical_forcing_boundary_joint_limit156 and horizontal-period version170 prove independent horizon/cusp restoration uniform in time cutoff in Re(w)≥1. Horizontal period is integral in x of time-integrated comparison.

Namespace D4BMOriginalForcingBoundaryQNM (leaf 4):
- firstWeight=E_square−E_gradient, secondWeight=E_gradient, where E uses normal angular reader. Both decay at every cusp order uniformly in x.
- boundaryKernel is actual principal-subtracted forcing profile times exp(w*t)*normalizable(w,chi,Z(t))*actual angular normal reader.
- boundary_two_kernels32: boundaryKernel=A*forcingKernel(K=0)+B*forcingKernel(K=1), exact before radial integration.
- original_product_kernel42: normalizedProduct=original onset*boundaryKernel.
- physical_metric_kernel52: f*((−wR)/f²*forcingTransferCut)=−w exp(−wp)*onset*boundaryKernel. The f is original dR/dt.
- physical_metric_laplace82: actual physical density is time-integrable for Re(w)>Re(2s); its time integral is −w*continuedOnset(s,w)*boundaryKernel.
- physical_metric_QNM_laplace108: BOTH actual QNMs satisfy this admission, since currentRate_re_lt (namespace D4BMModularCore) gives Re(2s)<−2 and physicalFundamentalFrequency_strip gives Re(w)>−2. No critical-line premise. The forcing onset contains exp(2s*p), not merely a transition tending to one.
- physical_metric_time_cut125: exact same kernel with finite-time factor int_0^T exp(−wp)onset.
- integral_two_kernels172: actual radial integral, with admitted compact kernels.
- radialCut retains two sets of source-derived radial counterterms c0 e^w/w+c1 e^(w+1)/(w+1)+d0 log(e), weighted at the SAME finite cusp height.
- forcing_boundary_joint_QNM207: choose neighborhood of either QNM and source-derived coefficients; actual radialCut tends to zero as (horizon e→0+, logheight k→∞) independently, for every w in neighborhood and arbitrary horizontal path X(e,k).
- physical_forcing_three_cutoff_QNM261: multiply the radialCut and its counterterms by SAME finite-time onset integral and −w. At either actual QNM, joint filter ((e→0+)×(k→∞))×(T→∞) gives zero; arbitrary relative cutoff rates. Time integral admission plus intervalIntegral_tendsto_integral_Ioi, and kernel radial restoration, supply proof.

IMPORTANT scope: this is the FOURTH FORCING BOUNDARY transfer. Its two angular weights vanish. The scalar BULK forcing weights in OriginalForcingJointHorizon instead tend (physicalSelfSourceCoefficient,0); bulk forcing/full action is NOT proved zero. Full matching to OriginalMetricQNM.regularAction remains open.

## Current records and next actual obstacle
Own facts docs/drafts/pipeline/1-in-progress/hb-own-research-facts.md F255–F258, lines509–515; F254 survivor clarified. Own card hb-physical-mode-action-contact.md current obligation598, fourth-transfer closure607. Frontier read only; STATUS unchanged because new facts route-specific.

Next: attach the other three actual metric transfers and canonical finite-height/horizon counterterms, including temporal endpoints; justify their joint restoration and QNM continuation. Expected exact identities (DERIVED CANDIDATES, NOT YET CHECKED): with A_jd=DC angularProduct, R=tortoiseRadius(−L/2), f=R²−1,
T(U,W)−CT = R² exp(−wp) A_0,true;
T(W,U)−CT = R² exp(−wp) exp(−k) A_1,false;
T(Delta U,W)−CT = R² exp(−wp)[exp(2k) A_2,true + A_3,true − A_1,true].
The outer 1/(R² f) cancels those R² factors. Laplacian term needs extra cusp order to absorb exp(2k). Endpoint estimates require actual pointwise source product bounds as well as integral bounds. Do not plug a QNM into DC right-half-plane estimates.
Useful verified source anchors: OriginalModularOrbit.mode_complete_boundary_time_transfer1276 retains all four transfers and endpoints. OriginalCompactBoundary.compactBoundaryCoefficient860 and mode_complete_boundary_compact_cusp877 fixed compact-time only. OriginalContactCusp.original_source_normal423 and source_angular_restriction91 retain source R. OriginalCuspFlux.original_source_logarithmic_remainders1086 converts canonical coordinate jets J[1],J[0,0],J[1,1] to actual normal/Laplacian operations. Need identify those coordinateJet words with DC baseOperator derivatives (ordinary derivatives in x,k), using smoothness/coordinate-update, not assumed equality. DC OriginalAngularProductBounds.original_source_jet_expansion168 is exact and public. OriginalOrbitCusp.principalCoefficient359=R*OriginalCuspJets.coefficient(p,p−2tortoiseR,i). OriginalMetricQNM.original_corrected_action_QNM184 proves removable radial/corner QNM pole after angular restoration, not full matching and not zero finite value.

## Search/validation facts
DD broad OR forcing/defect, deep fixed-angular-field/smooth-radial-coefficient mechanism, logarithmic broad, and deep Taylor/uniform finite-part continuation all completed; JSON candidates/source_arguments/proof_ideas/ingredient_sets inspected. Coverage inventory~58016 complete, but compiler pending~45165 and source_index_incomplete/semantic warnings. Deep Taylor search proposed mathlib Taylor remainder + finite-part transport; no verified full evolved-source continuation result found. Actual forcing QNM bridge uses existing OriginalMetricHorizon.forcing_horizon_restoration and exact two-field decomposition. Broad primary arXiv searches conormal/gluing found no applied result; 2404.09580 metric/Piola/Kato source was not used in a proof.

## Efficient isolated audit setup
DD audit used /tmp/hb-dd-audit with minimal lakefile: project name GaloisForLFunctions; lean_lib HBNew roots=[EXACT NEW LEAF ONLY]. New source(s) only; imports satisfied by top-level cache namespace symlinks (92) under audit/.lake/build/lib/lean to repo and dependency cached namespaces. This avoids 280k-file hardlink copies and avoids dependency builds. Lake overrides external LEAN_PATH, so setting only LEAN_PATH failed immediately and is not the method. GaloisForLFunctions cache namespace symlink points to authoritative repo cache; exact new-leaf audits therefore installed their owned new artifacts directly. All final source bytes matched audit source. No old module or umbrella build ran. Safe cleanup uses shutil.rmtree on audit (does not follow directory symlinks), preserving authoritative caches.
