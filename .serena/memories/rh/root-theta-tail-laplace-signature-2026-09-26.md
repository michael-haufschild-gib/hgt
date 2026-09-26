# C12/C12+ formalized: exact theta-tail and double-Laplace signature

Persistent goal: unconditional Lean proof/falsification of RH, NOT achieved. Keep active. User forbids git, numerical mathematical computations, increased heartbeat/recursion limits, multiple owned Lean processes, full/umbrella builds, other agents' log edits. Scratch first; LEAN_NUM_THREADS=1 lake env lean -j1; named leaf builds only. Scientific/stroke-of-genius methods remain binding; corpus-led conjecture loops and whole-route audit. Prior optimization complete (31.15% raw proof heartbeat reduction), see `mem:rh/root-lean-proof-optimization-2026-09-26`. Prior C11 reserve obstruction closed, see `mem:rh/root-geometric-boundary-obstruction-2026-09-26`.

## Closed result
For every real tail a, every sigma>0, every finite r, the actual complete theta first-moment K on x>a has complex negative dimension r iff its literal double-Laplace transform / Hermitian bilateral Bezoutian sampled on sigma+i*t (all t real) has dimension r. C12 was frozen for sigma>1/2, C12+ separately frozen for sigma>0 after analytic proof exposed stronger range. Both proved. Derived [BRIDGE], never a primary sign conjecture. No sign/RH premise or truncation.

Three new leaves, each wired once:
- HTGeometry/KernelClosedSpanInertia.lean: 198 lines; 12 theorem/lemma declarations, 3 defs. KernelClosedSpanInertia.kernel_negative_iff_closedSpan, kernel_negative_iff_of_closedSpan_eq, kernel_negative_scale_iff. Generic bounded operator; no Hermitian or completeness assumption needed. Strict negativity on finite unit sphere open, finite tuple approximation, Finsupp synthesis gives literal kernel packets.
- RHTower/ThetaTailLaplaceTotality.lean: 299 lines; namespace RHTower.ThetaTailSignature, 22 lemmas, 3 defs. Actual scalar Fubini and Fourier annihilator/closed-span equality; all-real-tail analytic uniqueness; source and transformed kernel identities.
- RHTower/ThetaTailLaplaceSignature.lean: 67 lines; same namespace, 3 theorems: thetaTail_negative_dimensions_vertical_iff, thetaTail_negative_dimensions_eulerLine_iff, thetaTail_negative_dimensions_doubleLaplace_iff.

Own closed card (complete paper proof, novelty/route and verification audit): docs/drafts/pipeline/3-formalized/rh-theta-tail-exact-signature-root-2026-09-26.md. In-progress copy moved, not duplicated. Own fact log docs/drafts/pipeline/1-in-progress/rh-reflection-source-sign-2026-09-26-facts.md through F96.

## Exact mechanism
SourceDouble = WithLp 2 of two SourceL2s. F(x) channels 1_(s>0)(x+s±1)Phi(x+s). differenceForm J=diag(+1,-1). <F(y),J F(x)>=2K(x,y).
Define L(w) as the actual L2 channels 1_(s>0)e^(-ws)(X1(w)±X(w)), with X actual bilateral transform, X1 first moment=derivative. Re w>0 ensures L2. For arbitrary u and channel d, the absolute scalar x integral equals |u(s)|e^(-Re(w)s)*integral |thetaTailChannelIntegrand d w 0 x| dx. Existing all-w actual source transform and moment integrability give finite x factor, L2 Cauchy-Schwarz gives finite s factor. pairing_integrable, pairing_swap, weighted_inner_integrable, laplace_channel_identity close this fully; NO unproved Bochner vector-integral claim.
Weak analytic source pairings give continuity. Fourier of e^(sigma*x)<u,F(x)> at t is <u,L(sigma-2*pi*i*t)>. Zero transform integrable; Continuous.fourierInv_fourier_eq proves zero pairing. Reverse direct scalar Fubini. laplace_annihilator_iff and laplace_closedSpan_eq. real_tail_annihilator_iff uses actual strip analyticity and tailAccumulationSet frequently_nodes; real_tail_closedSpan_eq.
inner_laplaceChannels and existing integral_thetaTailKreinDifference_eq_bilateralLaplaceBezoutian give laplace_section_kernel: <L(v),J L(w)>=2 thetaBilateralLaplaceBezoutian w v. This Hermitian B already conjugates v; entire thetaTailFirstMomentBezoutian uses w (conj v). Both source and transform factors2 cancel by positive real kernel scaling. Density result retains EVERY finite dimension.

## Verification
/tmp/rh-c12-complete-signature.lean exit0 without warnings before promotion. Named builds all exit0; /tmp/rh-c12-build-density.log, -build-totality.log, -build-signature.log. No new-leaf diagnostics; existing dependencies replay unrelated warnings.
/tmp/rh-c12-axioms.lean imports final leaf and audits every one of43 declarations including6defs; /tmp/rh-c12-axioms.log and -axiom-names.txt. All43 present, standard propext/Classical.choice/Quot.sound only. No nonstandard axiom or sorryAx.
Index refreshed after builds. /tmp/rh-c12-final-index.log exit0. Final lint /tmp/rh-c12-final-lint.log exit1 ONLY unrelated unwired RHTower.ThetaPowerFejerTransfer. Previous ShiftedDirichlet wiring errors no longer appear. Do not modify other agent module/log. No own-leaf or stale-generated-file error. All owned handles exited; final scan none.

## Searches
Current turn deep searches flux-contraction, source-factorization, stein-method, signature-search, laplace-totality, density-method in /tmp/rh-c12-*.json. Laplace-totality and density-method complete with no reported errors; other searches partial deadlines/disconnects. Density inventory59704 files, compiler mostly pending/source-only/stale. Candidate lemmas/source arguments/proof ideas/ingredient groups inspected; no generated premise treated as theorem. Inspected corpus had real-tail analytic totality and transformed entry identities/receivers, not actual cross-representation signature theorem. No external literature priority claim.

## Lean pitfalls / efficiency
- integral_norm_thetaTailChannelIntegrand_eq is NOT a simp rule: s=0 RHS contains same integral, recursively loops. Target rw [lemma d w s].
- Integrable.add on function expressions can introduce ContinuousENorm diamond; use generated .fun_add with explicit lambda. MemLp.integrable_mul function-product form: .congr (Eventually.of_forall fun s=>rfl) gives typed lambda.
- WithLp.prod_inner_apply produces ofLp projections; simp only [WithLp.ofLp_fst,WithLp.ofLp_snd].
- beta-reduce setIntegral_congr_fun goals with dsimp only before targeted rw. Complex star and starRingEnd need simp only [Complex.star_def] before ring.
- Normalize Complex.ofReal_one in the c=1 Bezoutian identity before linear_combination2.
- Generic operator lemmas cannot use A.sectionQuadratic field notation unless in CLM namespace; use sectionQuadratic A.
- Generic kernelForm_inner sums need outer Finset.sum_comm for chosen kernel orientation.
- Standalone Hilbert Fourier closed-span theorem also passes /tmp/rh-c12-fourier-totality.lean, but NOT promoted: actual weak scalar proof avoids vector continuity/integrability requirements.

## Whole route / next work
RH and common signature sign remain open. C12 establishes no hidden negative directions in the literal transform or arbitrary real tail, including arbitrary positive sigma. Moving to far-right line or far tail cannot change signature. This is not a positivity producer. Next substantive work must attack exact sign of J on actual source span (equivalently actual two-channel contraction), NOT package another equivalent receiver or strict-margin no-go. No primary next sign conjecture has been frozen. The actual TiltedSchwartz API is only |a|<1; do not assume all tilts, use actual all-w exponential integrability when needed.
