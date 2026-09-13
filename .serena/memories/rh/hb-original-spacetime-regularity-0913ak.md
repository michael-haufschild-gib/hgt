# HB original spacetime regularity — 0913ak

RH remains unproved; goal active. Previous aj was progress. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Completed, audited, wired — DO NOT REDO
1. NEW `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMRetardedTriangleGeometry.lean`, namespace `RHTower.D4BMRetardedTriangleGeometry`. Imports CausalRiemannKernel, HTGeometry.ConstraintMotiveRelativity.PrimeGammaReesEventGerm, Mathlib Complex RemovableSingularity/RealDeriv, Arsinh/Arcosh/Trigonometric.Inverse. No heartbeats raised. Exact leaf audit passed, 84s; only this source compiled (2719 cached/setup jobs).
   - `sinhc_smooth`: existing HTGeometry.ConstraintMotiveRelativity.sinhc is C∞, via entire complex dslope(sinh)0 and ContDiff.real_of_complex. Positive removable sinhc source already had sinhc_mul/pos.
   - sourceB image p r alpha beta = p*alpha+(if image then p-p*alpha else r-p*alpha)*beta.
   - triangleInvariant = original invariant with actual direct/image source radius, all source coordinates retained.
   - positiveFactor exactly Hdirect/Himage in aj card, with U written p-p*alpha.
   - `triangleInvariant_factor`: invariant−1=2(1-alpha)(1-beta)H, all real parameters.
   - `positiveFactor_pos`: p>0, p<r, alpha≤1 imply H>0, all beta.
   - `triangle_radius`114: actual arcosh(max1 invariant)=2arsinh(edgeWeight*sqrtH), alpha,beta≤1, including characteristic edges.
   - `positiveFactor_smooth`: globally C∞ in Fin4 coordinates.
   - `logarithmicRadius image z`: put p=exp(z0), r=p+exp(z1), alpha=sin(z2)^2, beta=sin(z3)^2, c=cos(z2)*cos(z3) into 2arsinh(c sqrtH).
   - `logarithmicRadius_smooth`154: globally C∞ all real z; H>0 because alpha≤1. Signed radius outside physical integration chart is fine.
   - angleMap t=arcsin(sqrt t); continuous globally; on unit interval sin²(angleMap t)=t, cos(angleMap t)=sqrt(1-t).
   - `logarithmicRadius_eq`190: at ![log p,log(r-p),angleMap alpha,angleMap beta], recovers actual triangle radius for p>0,p<r and alpha,beta in[0,1]. No trigonometric Jacobian needed: angleMap is continuous integration parameter for globally smooth extension.
2. Appended public `D4BMNativeResponse.unitCube_integral_smooth`162 to `ThetaCuspHawkingBMNativeAngularGreen.lean`. Exact wrapper around existing private triple_integral_infty. Smooth f:E×P→G plus continuous gamma:R×R×R→P yields C∞ of triple unit integral. Scratch/full leaf audit pass, 146s, only that source rebuilt (2629 cached/setup jobs). No old theorem changed.
3. NEW `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalSpacetimeRegularity.lean`, namespace `RHTower.D4BMOriginalSpacetimeRegularity`. Imports geometry + aj OriginalRetardedIdentity.
   - **`originalPotential_smooth`288**: for each actual XiZeroCopy q, both physical branches, any complex amplitude, actual Z(p,r,X,k) is joint ContDiffAt ℝ ∞ at every 0<p<r. No smoothness/source-ID/inverse/harmonic-completeness premise.
   - Proves smoothness of complete original source through positive circle charts: actual half-square, gradient energy, fixed onset, original complex radial power remain.
   - `extendedIntegrand` private: p=exp u, r=p+exp v, alpha/beta=sin² angle; original Jacobian p*(upper−A), actual timeOriginalForcing at (A+B)/2,(A−B)/2 and original circle radius, angle2pi*c, divided by4.
   - gamma uses angleMap(alpha),angleMap(beta),c. Fixed cube integral direct minus image globally C∞ via public helper.
   - Exact affine rescaling and average_unit prove `extendedRetarded_original` (private). Uses aj originalPotential_eq_retarded with NNReal p,width r−p. Then local log-coordinate composition transfers regularity to actual Z.
   - Scratch passed with no errors/warnings. Exact audit **[2/2] Built ... (30s)**, no other source compiled. Both new imports wired RHTower; no umbrella build.
All 3 sets of 5 artifacts (.olean,.ilean,.olean.hash,.ilean.hash,.trace) atomically installed after exact stage/repo source comparison.

## New analytical hard-boundary result — NOT LEAN YET
Own facts log F98 and main card final section 'The original causal source at the future horizon' give a dependency-closed smooth-extension proof for actual retarded Z. This directly attacks causal metric horizon admission, not an artificial proxy.
Fix ingoing time p>0. rho=exp(p−r), source z=exp(a−b), E=exp(p−a), source u=(1−z)/(1+z). Exact original invariants:
 direct−1 = 2(E−1)(z−rho/E)/((1+rho)(1+z));
 image−1 = 2(E−rho)(z−1/E)/((1+rho)(1+z)).
Direct domain z∈[rho/E,1], image z∈[1/E,1]. Original forcing factor 1−u²=4z/(1+z)² cancels db=−dz/z exactly. Complete transformed source density:
 −8u/(1+z)² * power(2s,2/(1+z)) * amp² * timeOnset(2s,a)
 * [((5s²+15s+4)/4) J + s(s−1)u²/4*((s+2)²J−K)],
J=fullSquarePotential, K=fullGradientEnergy/2 at original circle point. Overall action factor1/4 and direct−image survive. This density smooth for z>−1, including0; no log z needed after simplification.
Rescale a=p alpha,
 zD=rho/E+(1−rho/E) beta, Jacobian1−rho/E;
 zI=1/E+(1−1/E) beta, Jacobian1−1/E.
Both invariant increments have numerator2(E−1)(1−rho/E) beta. With expc(t)=integral0..1 exp(vt)dv, E−1=p(1−alpha)expc(p(1−alpha)). Circle radius=2arsinh(sqrt((1−alpha) beta)*sqrtH),
 H=p*expc(p(1−alpha))*(1−rho/E)/((1+rho)(1+z)).
For p in compact positive interval, |rho|<1/2, both H smooth and uniformly positive on whole unit square. Both z>−1/2. Use continuous angleMap parameters, edge cos(angle_alpha)*sin(angle_beta), for smooth compact extension. All original source fields retained. Dominated compact differentiation yields actual causal potential smooth continuation across future horizon rho=0 in p,rho,X,k. Actual positive-rho identity uses F94; no log(rho) at/below0. Physical R=(1+rho)/(1−rho), so this is genuine R=1 horizon.
For any smooth reconstructed stream P_A, original blocks h_tA=f*P_R and h_RA=P_t/f, f=R²−1, become h_pA=f*P_R+P_p and h_RA=−P_R in ingoing coordinates. This cancels apparent pole. Does NOT evaluate or annihilate horizon action current; full sourced causal tensor/pairing, onset/AdS/cusp traces and fixed-clock extinction remain open.
Next major work: formalize this exact compact horizon representation and its source Jacobian cancellation, then actual metric/current traces (or attach current interior jets to original full mixed reconstruction). Do not redo F94 source identity, F97 geometry, F99 spacetime smoothness.

## Corpus and external research
7 searches completed and inspected: sinhc hybrid; smooth integral compact neighborhood deep; contDiffAt_integral/compact_integral/exists_contDiff_extension OR deep; compact_integral_infty etc OR; nullWave/mixed_null/spacetime OR deep; exprel/exprelc OR. Source/compiler coverage mostly source_only/pending; candidates applied were verified in Lean. Global compact extension initially looked local; sin²/angleMap positive representation removed need to build general local smooth-extension machinery.
- `HTGeometry/PoincareHopf/SmoothExtension.exists_contDiff_extension`19 only C2 on a ball, not used.
- Existing SpinTwoDelayCharacteristic copies same private compact-integral helpers but gives delay-current transfer, NOT the new full spacetime/horizon result. Do not copy its maxHeartbeats600000.
- `HTGeometry/Arxiv2608ExprelFilon.lean`23: cgcExprel abbrev forwardWindowKernel; zero/of_ne/continuity/finite-time average theorems.
- `HTGeometry/UniversalSpectralSemigroupWallCrossingLaw.lean`25: forwardWindowKernel=dslope Complex.exp0. Existing removable exp kernel is a candidate for future horizon expc formalization. Source read, no new Lean applicability check yet because not used this turn. Smoothness can use same entire-dslope proof as sinhc.
- Broad arxiv desingularization/wavefront search returned old papers. Corpus exprel search found actual **arXiv2608.18589**, opened https://arxiv.org/abs/2608.18589: 'Fourier Transforms of Color Glass Condensate Multi-Wilson-Line Correlators via Filon Quadrature', Duan/Dai/Yi/Zhao, submitted19Aug2026 revised10Sep2026. Abstract explicitly uses exprel to remove0/0 instability. HTMLv2 cache miss. No quadrature/computations/theorem from paper used as proof. Prior generic old desingularization paper not used.

## Lean efficiency / exact pitfalls
No computations, Git, launch.sh, #print axioms, heartbeat/recursion raises, subagents, umbrella/full builds. One foreground Lean/Lake at time, LEAN_NUM_THREADS=2 pinned lean4:v4.32.2.
- ContDiff has NO const_mul/mul_const/const_add helpers here: use contDiff_const.mul / hf.mul contDiff_const / contDiff_const.add hf. For constant complex division use hf.mul(const c⁻¹) and div_eq_mul_inv; avoids underconstrained .div constants.
- fun_prop does not handle Matrix.vecCons in narrow geometry imports. Use contDiff_pi.mpr; intro i; fin_cases i; dsimp; fun_prop. Give explicit composition maps. Predicate dischargers for variable cosh denominator need intro x then exact mul_ne_zero... cosh_pos.ne'.
- logCircle_pos is PRIVATE; prove local circle_height_pos from exp k*(1/denominator)>0.
- ContDiffAt composition with fullSquarePotential can greedily unfold it into1/2*S²: first bind an explicitly typed hf:ContDiffAt ℝ∞(fullSquarePotential q)(C z), then hf.comp z hC.contDiffAt.
- qualify D4BMNativeCircle.average (MeasureTheory.average also open).
- Add dsimp only after integral_congr intro before rewriting affine integral.
- NNReal coercion algebra: change p+(r−p)=r; ring, rather than dsimp exposing opaque constructor coercions.
- Do not leave underspecified `_` arguments in the extendedIntegrand original-chart change: explicitly spell source time/radius, letting simple rw reduce log/exp/angleMap.

## Audits, logs, cleanup
Main card `docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md` opening current closing obligation updated, interior section marked formalized, full future-horizon analytical proof appended. Own crisp log `hb-own-research-facts.md` now F01–F99,N01–N04. F96 updated Lean closureF97/F99; F97 geometry Lean; F98 futurehorizon analytical; F99 actual spacetime regularity Lean. No new nogo. Frontier map READ ONLY, STATUS unchanged (no new route-independent law).
Lint once: only error unrelated existing unreachable RHTower.Sieve.KloostermanGlobalCollisionCoprime; existing large-file warnings. No own lint error. Do not modify other agent's module.
Audit stage needs a restricted **roots=[exact audited source modules]** appended to temp lakefile.toml under lean_lib. Otherwise Lake tries rebuilding missing dependency sources. Copy repo lakefile/manifest/toolchain, symlink .lake/packages, recursively read project import closure, hardlink cached dependency artifacts where present (only .olean mandatory), stage only new/modified source leaves. No source modules beyond audited leaves compiled. Default toolchain metadata checks cached jobs; job count is not compilation count. Early stage attempt lacked roots and failed before compilation; fixed. Never run full builds to repair cache.
All scratch/search/audit handles terminal. Stage plus18 owned temporary files removed after verifying no owned Lean/Lake process remains. One attempted OS sample failed because target had already exited; its temporary output removed. No processes from other agents touched. All proofs persist in tree; no pending scratch work.