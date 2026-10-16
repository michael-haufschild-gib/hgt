# CHMD compact C2 operator cores — formalized 2026-10-16

Mission remains unconditional RH through CHMD. Goal ACTIVE, unbounded; RH NOT proved. This turn completed a substantial structural contribution: compact C2 sources form operator cores for BOTH actual CHMD generators, not merely form cores or compact-support operator cores.

Card: docs/drafts/pipeline/3-formalized/chmd-compact-smooth-operator-core-2026-10-16.md
Prior result: `mem:rh/chmd-compact-support-operator-core-2026-10-16`.
Ground generators: `mem:rh/chmd-stationary-ground-generators-2026-10-16`.

## User constraints for next turn
Read /Users/michael/.codex/attachments/2c5020c9-b71c-40b8-ba6c-e8fb1100e229/pasted-text-1.txt before continuing. Corpus-first conjecture/proof loop; significant structural CHMD advance per turn. No web, old research Markdown, novelty audit, numerical experiments, or computations. No full/umbrella builds; targeted lake --old build only, ONE owned Lean/build process at a time. Final audit plain lake env lean each affected file. Axiom/API probes in /tmp only; no raised heartbeats. Wire completed leaves, lint, clean owned scratch. No commits/push by us. No delegated agents authorized. Long Python jobs use scripts/run_guarded.py with finite timeout. Serena ignores Lean files; established rg/apply_patch fallback. update_plan and multi_tool_use.parallel unavailable; current cards track work and Promise.allSettled batches independent reads.

## Capstone
formal/GaloisForLFunctions/RHTower/CHMDCompactSmoothOperatorCore.lean:
- line 18 stationaryGenerator_compact_smooth_graph_closure
- line 44 stationaryGenerator_compact_smooth_core
- line 68 arithmeticGenerator_compact_smooth_core
- line 87 arithmeticGenerator_compact_smooth_graph_closure

For every maximal-domain u, a sequence v_n in that ACTUAL operator domain has compact C2 representatives, v_n -> u in mass L2 and operator(v_n) -> operator(u). Both full operator graphs equal closure of their compact C2 restrictions. Unconditional actual objects, no RH/sign/domain-admission premise.

## Nine new leaves (143 declarations, 1206 lines)
1. CHMDStationaryVolumeGraph (27): H=L2(dx), literal difference graph for ACTUAL stationaryMeasure=kappa(t)dt dx, dense source, R=S S*, A=R^-1-I self-adjoint, nonnegative, closed; groundToVolume.
2. CHMDStationaryTranslations (19): stationaryMeasure product identity; source/edge translations; volumeGraphTranslate preserves graph inner product; strongly continuous source translations; volumeResolvent_translate via Riesz uniqueness.
3. CHMDStationaryOperatorMollification (8): volumeSmooth n u = integral rho_n(a) T_-a u da; strong convergence; resolvent commutation; volumeGeneratorSmooth preserves Dom(A), A S_n=S_n A, simultaneous source/output convergence.
4. CHMDStationaryConvolutionRepresentative (9): integrable_mollifier_pairing uses domination by rho(a)*(u(x-a)^2+v(x)^2), product shear; Hilbert Bochner average = literal smooth convolution for arbitrary L2 representatives; compactness under compact AE representatives. Explicit import HTGeometry.CompactKernelL2Convolution necessary.
5. CHMDStationaryVolumeCutoff (26): first-moment edge measure t*kappa(t)dt dx; bounded endpoint pullbacks; volumeCutoff; exact bounded C_n=El* B_n Er-Er* B_n El with B_n=(chi_n(left)-chi_n(right))/t. Complete-form edge commutator identity.
6. CHMDStationaryLocalTransform (20): generic admittedMultiplier across absolutely continuous measures, automatic boundedness via closed graph; bounded J=thetaToVolume; local inverse W_n=localThetaInverse with factor chi_n/theta; J W_n=M_n, W_n J=massCutoff n. localToGround transports the full ordinary form graph after cutoff.
7. CHMDStationaryLocalOperatorDomain (23): actual-domain lifts; complete-form Riesz admission; ordinary volumeGeneratorCutoff and A(M_n f)=M_n Af+C_n f. stationary_of_volume_mem_domain / stationary_of_volume_apply: if f=J u is in Dom(A), then u is in Dom(G), G u=J*Af. localized_theta_mem_volume_domain: if massCutoff n fixes u in Dom(G), then J u belongs to Dom(A). This is the hard local domain bridge.
8. CHMDStationaryLocalSmoothCore (7): localizedVolumeVector; localStationarySmooth k u hu n=W_k S_n(Ju); actual generator-image formula; localStationarySmooth_tendsto in BOTH mass-space graph coordinates; compact C2 representatives; exists_cutoff_fix_compact and exists_massCutoff_fixed.
9. CHMDCompactSmoothOperatorCore (4): closure and sequence core statements for G then L=G+bounded groundPerturbation.

Two existing helper blocks generalized without changing actual generators:
- CHMDStationaryGenerators generatorOfResolvent and helper theorems now arbitrary real complete Hilbert H, instead of fixed MassSpace. CompleteSpace omitted on apply/identity where unused.
- CHMDArchMomentPullback admittedPullbackLM/admittedPullback now implicit source measure mu, instead of fixed massMeasure. Existing call signatures infer mu from admissions. All callers examined; affected old compact support core also rechecked.

## Key proof
Actual ordinary A uses kappa, NOT Gamma-clock kappa/t.
J:u->theta*u bounded mass L2 -> ordinary L2, globally injective but no bounded global inverse. W_n:f->chi_n*f/theta is bounded only after compact localization.
E(M_n f,q)-E(f,M_n q)=<C_n f,q> on complete form domain.
If u in Dom(G) and mass cutoff fixes u, f=Ju and M_n f=f. Local test W_n q lies in ground form graph, yielding E(f,q)=<W_n*G u+C_n f,q>. Riesz admission gives f in Dom(A). No separate far-field kernel argument needed.
Conversely f=Ju in Dom(A) gives G u=J* A f by complete-form tests.
u_j=W_n S_j f: J u_j=M_n S_j f in Dom(A). A M_n S_j f=M_n S_j Af+C_n S_j f -> Af because M_n f=f. Bounded W_n and J* give mass source/output convergence. Representative is chi_n*(rho_j*f)/theta, compact C2. No common support estimate for mollifiers needed.
Combine local smoothing with prior compact-support operator graph closure; use sequential closure to get actual approximating sequences. Bounded perturbation transfers G core to L.

Do NOT assert global Dom(G)={u:Ju in Dom(A)}: only forward compactly localized admission is proved. No critical signed-form sign, primal cardinal synthesis, or unconditional RH follows from core alone.

## Validation completed
- Targeted lake --old build capstone EXIT0, no warnings from task leaves.
- Final plain lake env lean checks: 12 files, ALL EXIT0 with EMPTY logs (nine new, two generalized, prior CHMDCompactSupportOperatorCore).
- /tmp #print axioms audit of ALL 182 declarations in nine new + two generalized modules: only propext, Classical.choice, Quot.sound.
- Mathlib API probes passed.
- All nine root RHTower umbrella imports exactly once; no umbrella build.
- Global scripts/formal_tools.py lint EXIT1 on exactly five unrelated unwired modules at check: CHMDLevySymbolLowerBound, CHMDWindowFourierTail, PaperThetaNativeArithmeticResolvent, PaperThetaNativeQuantileDomain, WeilCutEvenMeanZeroDeficit. No task-scope lint failure.
- Source hashes unchanged through final audit.
- All 28 owned scratch files removed after terminal successful guarded verification; no owned running build/check remains.
- Workspace has concurrent writers/commits; we performed no commit/push. Do not revert unrelated work.

## Audited SHA256
CHMDStationaryGenerators: 2676e42c33f537d7545d5ce94a9a302193c77d38d1d935c8f3585f530b04bf3d
CHMDArchMomentPullback: ed2a6a76291575e2d1c3e312043c12e28bab6f4ff81c6a537a81875caef36f79
CHMDCompactSupportOperatorCore: 53212585e2a27e329a3eed6d034f935ee538c4d15f3a120b5d195b27b412571c
CHMDStationaryVolumeGraph: 26d4771cf6f5b7f5e96a57c2ce254e6c9edf0eed208fd0080dd201c1c4fb6103
CHMDStationaryTranslations: 70629576d48104dcae447fcb8116b3b68ed59432f643db6590f306823b13c172
CHMDStationaryOperatorMollification: f5841fe349b457b45a18ff35c58b3260e2d78b54f660da9332c8c2724f0cb491
CHMDStationaryConvolutionRepresentative: 3e7b33ca04d847e454c1b3136d67857cc77f5a286180dbc0d9310974172f8a55
CHMDStationaryVolumeCutoff: df3f764387b06cde48e4cf4068adac937fc652667d6329941bbe98ff890121e1
CHMDStationaryLocalTransform: 29d8efd3149a4634f899a1a723a2bbb0a943a83cf2ab155b5364ec77ad78dc55
CHMDStationaryLocalOperatorDomain: 5c8ae50a4c90fee6d7306a9f429cd69ca0490c5fced66ed26eae688619e8fdef
CHMDStationaryLocalSmoothCore: f4778a9837a3f6192581803407829b85b090ece78d3f1934220b4004f86d0feb
CHMDCompactSmoothOperatorCore: dee41bf4a88bb06c104ad03ed6ad0dfbaf6b2c04fdb7695f3f525bdf2fabfa27

## Lean elaboration lessons
Explicit types avoid heartbeat issues; no limits raised.
- compact_memLp_volume: name HasCompactSupport (fun x=>v x^2) before invoking integrable_of_hasCompactSupport.
- rw does not reliably match composition/Pi operations to literal lambdas; type measurability hypotheses explicitly, use apply (memLp_two_iff_integrable_sq ...).mpr rather than rw.
- right endpoint identity: change target to literal e.2+e.1 first; simp Function.comp_def, Pi.add_apply, add_comm.
- Subtype range witness rewrites often need erw or typed generator identity matching volumeGenerator/stationaryGenerator instead of generic generatorOfResolvent.
- Identify graph cutoff edge coeFn explicitly with change before rw.
- volume smoothing convergence: unfold local let f and localizedVolumeVector when simpa.
- Tendsto.fst/snd projections of nhds product can leave inference unresolved; compose continuous_fst/continuous_snd.tendsto with paired limit explicitly.
- Metric.mem_closedBall is qualified unless Metric open.
- Mathlib API probes with @Name require explicit universe levels; Integrable.mul_prod has THREE.
