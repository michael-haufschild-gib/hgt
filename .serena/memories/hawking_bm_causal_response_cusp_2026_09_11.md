# HB original causal cusp jets and Goursat traces — 2026-09-11

Goal remains ACTIVE: unconditional RH proof/falsification via literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. RH and the complete physical current cancellation 2 Omega(B(p,p)/2,B(m,m)/2)=0 remain unproved. This turn made progress, not a blocked/status-only turn.

Rules: NO Git, NO launch.sh, NO numerical experiments/Runpod. Frontier map READ ONLY (later user override). No new route-independent STATUS entry was warranted. One owned foreground Lean/Lake process at a time; scratch lake env lean, final exact-module lake build only, no dependency/full/umbrella build. Audit axioms only newly created public theorems. No subagents authorized/spawned. Direct documented research tool, no research help/implementation/backend inspection. Spaces AND; broaden with single words/--any. Partial/source-only search outputs are suggestions; inspect source methods and ingredient groups.

## Installed new owner
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCausalResponseCusp.lean, 832 lines, namespace RHTower.D4BMCausalCusp.
Imports NativeAngularCurrent and NativeResidualAdmission. One umbrella import in formal/GaloisForLFunctions/RHTower.lean.
New stage3 card docs/drafts/pipeline/3-formalized/hb-causal-response-cusp-current.md.
Stage1 docs/drafts/pipeline/1-in-progress/hb-causal-response-cusp-current.md updated to actual proof status; hb-mixed-complete-current.md final scope paragraph updated. Frontier and universal STATUS untouched.

Six public definitions: radius36, sourceWeight57, principalResponse104, responseRemainder108, jetIntegral123, remainderForcing751.
Eight public theorems:
- principal_coefficient_integral146: original physical principalNullResponse = 1/4 double integral principalAmplitude*powerCircle(original continuous arcosh radius)*original odd sourceWeight on nonnegative p,r.
- responseRemainder_integral260: literal U minus sum_i c_i exp(alpha_i k) = original double native-remainder source integral, with factor1/4.
- responseRemainder_jet_integral345: every actual ordered coordinateJet word (Fin2 angular X,k) equals jetIntegral word, whose nativeJet word.map Fin.succ uses radius/X/k (Fin3).
- responseRemainder_jet_uniform_bound382: q actual Xi copy, arbitrary complex s/amplitude, any word and natural N,T:Ici0: exists D,B>=0; p,r in [0,T], any X, k>=D imply norm jet <= B exp(N(D-k)).
- responseRemainder_jet_weighted_tendsto_zero435: any complex weight w, arbitrary p,r:R→Icc0T and X:R→R, exp(wk)*actual angular remainder jet tends0. No path continuity assumed.
- responseRemainder_goursat728: closed nonnegative causal quadrant; actual R double primitive of original source remainder plus actual hyperbolic angular Laplacian divided by 4cosh((p-r)/2)^2.
- responseRemainder_first_null800: p:Ioi0,r:Ici0; actual HasDerivAt in p equals integral0..r remainderForcing(p,b).
- responseRemainder_second_null816: p:Ici0,r:Ioi0; actual HasDerivAt in r equals integral0..p remainderForcing(a,r).

U=fullNullResponse q s amplitude p r X k.
c_i=original principalNullResponse; alpha=[2q,1,2-2q].
R=U-sum c_i exp(alpha_i k), uncut decomposition, NOT globally the physical cutoff residual.
remainderForcing = nativeRemainder q ![0,X,k]*sourceWeight/4 +(exp(k)^2 R_XX+R_kk-R_k)/(4cosh((p-r)/2)^2).
All actual scalar coefficients, original odd source, null Jacobian and characteristic edges retained; no source/equation/extinction premise supplied.
Scope: angular jets arbitrary order, compact causal rectangles only. First-null identities proved; higher angular-null rapid bounds remain only on paper, not formalized. No unbounded horizon limit or reconstructed full-current cancellation in this owner.

## Proof mechanism / reusable private code
principal coefficient uses radialResponse_null_native, powerCircle_eq_legendre, scalar causal invariant >=1 and cosh(arcosh).
nativeRemainder all-order smooth from nativeMean_joint_smooth plus explicit powerCircle/Legendre principal sum. Differentiate angular variables through two compact integrals via hasDerivAt_parametric_intervalIntegral; arcosh radius need only continuous, no null derivative of radius used.
geometry_bounds bounds original sourceWeight and radius on compact causal rectangles; existing nativeCuspJet_rapid_bound passes through two signed interval integrals.
Goursat subtraction: original fullNullResponse_goursat minus all three radialResponse_goursat; (-alpha)(1-alpha)=alpha(alpha-1) is exact angular eigenvalue.
Private effective is a globally continuous extension built from jetIntegral; on forward quadrant it equals actual remainderForcing. This supplies FTC even at the other zero-length characteristic edge.
Private principal PJet derivative, full_action, rectangle integration helpers verified; private names cannot be called downstream.
Technical fixes: fullNullResponse_angular_smooth is on R×R, compose with Angular→(z0,z1) and use simpa only [Function.comp_def] using! to avoid instance isDefEq blowup. Unknown Function.update_same/update_update: use simp, not guessed names. Explicit show 0<=p.val from p.property avoids subtype membership elaboration. norm_integral_le_of_norm_le_const domain uIoc, not uIcc. One-dimensional continuity helper must specify volume through an expected integral type.

## Analytical next trace argument
For canonical angular derivatives D_X^u D_k^v, differentiating exp(2k) R_XX gives exp(2k) sum_(j=0)^v binom(v,j)2^(v-j) D_X^(u+2)D_k^j R. Input cusp bound order N+2 controls every term. Differentiate the Goursat double primitive in angular variables, then FTC, to get actual null/angular derivative formulas without assuming commutation of mixed orbit derivatives. Compact-source weight/potential bounds give their rapid cusp limits. This is next positive analytic lemma for reconstruction, not yet Lean.

## Recovered existing source identity — DO NOT REPROVE
Broader Peierls/Darboux searches and direct original source-operator analysis led back to:
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullSourceOnsetReduction.lean (read full relevant parts), stage3 hb-full-source-onset-reduction.md (read).
D4BMJointSource.timeOriginalForcing_full_onset_decomposition352:
 original F = timeFieldWave(timeLiftField) - timeFieldWave(timeAngularSeedField)/alpha + fullSourceOnsetPulse/alpha,
alpha=parameter q branch=(2s+1)(2s+2), s=physicalRate.
All actual wave derivatives/full angular inverse already supplied without hypotheses; 21 old public theorems previously audited, DO NOT re-audit them.
Full source pulse transition333 and support outside ingoing v∈[0,1]344 already proved.
D4BMGlobalAngularResponse.fullAngularField H satisfies Delta H=alpha(H+Q).
Let u=-tanh x, Q=fullSquarePotential q, k_s=s(s-1)/4, r_s=a²(1+u)^(2s), b=r_s u, ell=-k_s r_s u³.
Phi=(b H+ell Q)chi(v)e^(2sv).
Original F=L Phi+2(b' H+ell'Q)chi'(v)e^(2sv), L=∂τ²-∂x²-(1-u²)Delta.
Incoming horizon Phi→a²2^(2s)(H-k_s Q)chi(v)e^(2sv); full integrated physical current and causal pulse pairing still needed.
The physicalLiftHorizonCurrent owner audited in earlier turn computes ONLY the -k_s Q part, not the H plus pulse.
ThetaCuspHawkingBMFullAngularMasterCurrent.lean (read): fullAngular_master_current50 already proves original steady two-factor exterior master source identity with constructed fullAngularCovector and rough Laplacian. physicalRate14 is q-2 for true and -q-1 for false.

Independent paper calculation recovered (not new theorem needed):
sigma=2s, 4lambda=sigma²+6sigma+8, E=(1+u)∂u.
Local cubic lift c u³F, c=(2sigma-lambda+2)/4=-s(s-1)/4, matches the Delta part of original source. Its remaining bulk wave error is u[(sigma+1)(sigma+2)]F plus explicit fixed-onset derivative. Existing FullSourceOnsetReduction already gives stronger complete angular-inverse version. Reuse; do not spend another turn re-proving this polynomial or a negative obstruction.
Concrete next physical action remains pairing incoming H-k_sQ with actual causal pulse response, retaining all faces and SS/SV/VV. Original master's source Pdagger A(Gret-Gadv)P measure factors in hb-mixed-complete-current.md remain mandatory.

## Searches
Current original searches: polyhomogeneous, long causal-integral/parameter-derivative goal, Volterra, lexical Goursat, reciprocity. Additional continuation: Peierls, Darboux. Used --mode deep --budget-seconds120 --no-refresh --json except lexical Goursat.
Inspected declarations, candidate statements, source methods, proof ideas and ingredient groups. All partial/source-only; several semantic/reranking runtime deadlines. Backend errors say run launch.sh: IGNORE, user forbids.
Peierls gen823347: 56,595 files,503 pending,723,712 decls; proposed Peierls response/remainder group not verified, did not provide physical pairing. Source methods include known stationary-channel elimination with supplied symmetry/causal hypotheses and RH equivalences; none applied as unconditional extinction.
Darboux gen823347 pending: native mean/source Darboux equations already own dependencies; proposed Karamata gap telescoping group not applicable. No new premise.
Broad arXiv own words polyhomogeneous, Volterra, memory, reciprocity-related symplectic/isotropy; recent query via domain arxiv.org and recency90 worked better than URL-prefix2609.
Opened abstracts math/0506423 Chrusciel/Leski wave expansions without corners (2005/2006), 2404.15885 Schlue/Taylor Vlasov-Poisson expansions (2024), 2609.03329 SINFONIA (3Sep2026), 2606.25993 quadratic intervals (24Jun revised28Jun2026). No full paper proof or numeric result used. SINFONIA suggests signed balance channels as questions, not proof premises. No numerical computations.

## Validation and cleanup
Scratch final lake env lean passed; style-only comments/sequence cleanup then exact isolated final lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalResponseCusp passed in340s,2jobs, no dependency or umbrella rebuild.
Audit froze 4,136 own compiled import-closure modules via20,536 hardlinks and12 name-only path-dependency stubs; unused Cli has no installed build dir, empty audit build dir used. Dependency directImports read from .ilean; source fallback if no .ilean. Only new source leaf owned by audit lean_lib.
Eight NEW publics #print axioms in /tmp via lake env lean: exactly propext,Classical.choice,Quot.sound; no added axioms/sorry/computational certificate.
Installed source and .olean,.ilean,.olean.hash,.ilean.hash,.trace byte-identical.
Index run once passed (3changed0removed); all14newpublicAPIrows checked; uniqueumbrellaimport;18 local doc links valid.
Global lint run once FAILED only2 unrelated unwired modules: RHTower.Sieve.MenonHarmonicWindowThresholdSplit and HTGeometry.ChronologicalTensor.CubicRepairGamma. Do NOT falsely report global lint passed or change other active agents' modules. Older six-error snapshot is obsolete.
All owned Lean/Lake/search/index/lint handles terminal, no running task to restart. Own /tmp/hb-causal-response-cusp-0911 plus seven search JSON files scheduled for immediate cleanup after this memory; verify cleanup result in final tool output. No goal completion/blocked status call warranted.
