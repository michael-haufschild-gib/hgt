# HB DP: full original source cancellation and metric/temporal diagonal

RH active/unproved. Sole task full temporal/metric/QNM matching or impossibility. Canonical static matching/QNM continuation ALREADY exist; hardest current gap is evaluate canonical QNM action from literal sources, then compare physical extinction receiver. No experiment review, frontier map read-only, analytical only, no Git/launch.sh/#print axioms/heartbeat or instance hacks. Chain every new turn: literal theta cusp → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Verified current turn
Two new leaves, namespace RHTower.D4BMOriginalSourceResolvent, all scratch checks and isolated exact-module audits passed; imports wired in formal/GaloisForLFunctions/RHTower.lean. Global `scripts/formal_tools.py lint` PASSED (size warnings only). No unfinished owned processes. Private audit workspace and completed scratch files removed. Audit logs `/tmp/hb-dp-global-audit.log` (67s), `/tmp/hb-dp-diagonal-audit.log` (115s), `/tmp/hb-dp-formal-lint.log` retained. No need repeat audits or axioms checks.

1. ThetaCuspHawkingBMOriginalRegularizedSourceResolvent.lean
- readerIncomingPart_integral_below: one source-derived B supports every smaller b and independent nonreal reader v with Re(w+v)>0. BOTH actual horizon density integrability and equality to readerIncomingPart derived.
- readerIncomingPart_neg_eq: incoming(-v)=oppositeRegular(v)+E_b/(w-v), exact pole.
- readerFullRegularPart=readerHorizonRegularPart+actual outer integral b..1.
- readerFullRegularPart_source_identity_below (line97): actual global pole subtraction (v²-w²)*Ireg=J(w,v)+(v+w)*E_b*beta(v), mixed convergence wedge; no admission premise.
- incomingResponseEndpoint_eq_amplitude_below (line156): uniform source neighborhood/all smaller cutoffs E_b(u)=actual greenHorizonAmplitude(u), assuming actual connection nonzero. Uses original source primitive split, not assigned amplitude.
- sourceDensity_diagonal_amplitude (line183): actual whole diagonal source admitted and J(v,v)=-c(v)*E(v), from original normalized outerMoment.
- readerFullRegularPart_source_difference_below (line201): fixed source data, source/reader Chamber, nonreal, both source convergence, Re(w±v)>0:
  (v+w)*Ireg(w,v)+c(v)*(E(v)-(v+w)*E(w)/(2v))/(v-w)
  = -int_0^1 n_v*(S_v-S_w)/(v-w).

2. ThetaCuspHawkingBMOriginalMetricTemporalDiagonal.lean
- mixedOuterIntegral_continuousAt line13: actual fixed-source outer pairing continuous in arbitrary reader, through actual endpoint1. Derives actual response boundary limit, continuous extension on [b,1], compact powers and outerGauss_uniform_bound, then DCT on Ioo b1. No domination premise.
- greenHorizonAmplitude_analyticAt line98: actual E is analytic (not just punctured meromorphic) if w nonreal, Rew>-2, sourcepole avoided, c(w)≠0. Derives via source-local split and analytic original moments.
- temporalSourceQuotient_tendsto line134: actual quotient above tends c(w)*(E'(w)+E(w)/(2w)), including exact fixed constant.
- fullMetricTemporal_diagonal_limit_below line163: full left side tends 2w*(original normalizableHorizonPairingFinitePart+actual outer integral)+c*(E'+E/(2w)). Original source Chamber etc; all sufficiently small common cutoffs.

OriginalHorizonGreenMatch import initially needed ONE missing object BMMixedRadialActionCurrent; transitive source preflight confirmed only one. Built unchanged dependency with foreground `LEAN_NUM_THREADS=1 lake env lean -o .lake/build/lib/lean/...MixedRadialActionCurrent.olean GaloisForLFunctions/RHTower/...MixedRadialActionCurrent.lean`; PASSED. Its object now exists: do NOT avoid original amplitude import or rebuild dependency forest.

## Next hardest step: actual-source divided-difference DCT
Own fact log docs/drafts/pipeline/1-in-progress/hb-dn-source-resolvent-facts.md now DN1–DN12. Own paper hb-dn-source-moment-reduction.md records exact source formula and Cauchy analytical proof. Other hb-own-research-facts.md belongs to other stream; don't modify.

No new source-bound Lean draft exists. Need formalize DN12 on actual functions, not generic toy:
For fixed s,chi,amp,J,K; w nonreal, Rew>0, w-2s≠0, derive R,C>0 with
∀u,v∈ball w R,∀0<z<1, ||normalizable v chi z*continuedSourceProfile s amp J K u z||≤C*z^(-1/2).
Proof: normalizable reader = A(v) horizon(v)+beta(v) horizon(-v), original coefficients. Both continuous and locally bounded; A-continuity proof in ReaderRegularization lines299–311. HorizonGauss_uniform_first_bound at ±w bounds Gauss factors on [0,1/2]. Source remainder jointly continuous on compact frequency/radius rectangle; fixed onset T(u)=1/(u-2s)+onsetCorrection locally bounded and analytic away pole. Powers combine to z^((u±v)/2), real exponents >-1/2 if R≤1/4 and Rew>0. Outer [1/2,1] uses outerGauss_uniform_bound and compact cpow bounds. z^-1/2≥1 absorbs outer constant.
Then fix reader v, apply `Bottcher.norm_sub_le_of_bounded_on_ball` to f(u)=n_v(z)*S_u(z), yielding ||n_v*(S_v-S_w)/(v-w)|| ≤(2C/R)*z^-1/2 on half ball. Pointwise dslope limit and entire reader give n_w*deriv(source profile) w. DCT closes 2w GreenFP+c*(E'+E/(2w))=-int n_w*partial_w S_w. ALL differentiation holds chi,K,s,amp,J fixed. Do not differentiate fundamentalSourceMoment along fundamental curve (changes K).

Exact APIs inspected:
- Bottcher/Montel.lean:26 norm_deriv_le_of_bounded_on_ball hR (DifferentiableOn f ball) bound, derivative bound 2*C/R on half ball.
- same file:53 norm_sub_le_of_bounded_on_ball hR hf hbd {z w} hz hw -> ||f z-f w||≤(2*C/R)*||z-w||. Available via CauchyDominatedIntegralHolomorphy imports.
- Complex.norm_cpow_eq_rpow_re_of_pos hz exponent.
- Real.rpow_le_rpow_of_exponent_ge hz0 hz1 lower_exponent_le.
- sourceProfile_frequency_entire with fixed T=1; multiply analytic actual onset to prove S_u holomorphic away pole.
- sourceRemainder_joint_continuous s amp J K 1.
- actual A(v) continuity uses horizon_frequency_analyticAt and horizonFirst_frequency_analyticAt at -w, normalizable_frequency_entire, normalizableFirst_frequency_entire, all at z=1/2; unfold horizonRegularCoefficient/radialBracket and divide -v.

Then need source finite-part continuation with exact counterterms to physical QNM and receiver comparison. QNM raw source integral NOT admitted; incoming subtraction still necessary. Exact target in own paper: -mu*C*((mu-2)*(T'*M+T*X)+w*T*Z0). Preserve tortoise -log2 in X; forcing temporal corner retained until c(w0)=0 with analytic forcing factor. No matching/impossibility/RH claim yet.

## Search/method status
Deep searches this turn: parameter integral boundary continuity; divided difference dominated holomorphic integral; source reader uniform. JSON files `/tmp/hb-dp-outer-continuity-search.json`, `/tmp/hb-dp-source-difference-search.json`, `/tmp/hb-dp-mixed-source-search.json`. Partial cached coverage ~58155files/752kdecls, mostly source-only compiler metadata; verified actual applicability through Lean. Second search's method/source hits gave CauchyDominatedIntegralHolomorphy and ClockParametricIntegralHolomorphy. Broad recent arXiv transmutation search read arxiv2601.03616, no theorem imported/no relevance claimed. Serena initial_instructions READ this turn; its output includes huge memory inventory, do not repeat. docs/architecture.md and testing.md absent. Both scientific method files read as in prior turn summary.

## Lean efficiency
Only one foreground owned Lean/Lake at time, LEAN_NUM_THREADS=1. Scratch cwd formal `lake env lean /tmp/...`; exact audits private minimal lakefile with ONE root module, symlink root/dependency lib objects to audit/.lake/build/lib/lean, copy only current leaf source; no root/umbrella build. Remove private workspace after final audit, installed objects remain. Source signs: solving J from hid LHS=J+term uses `linear_combination -hid`. In temporal quotient proof `continuousAt_id.eventually_ne` yields `hv0 : id v≠0`; `change v≠0 at hv0` before field_simp is required. Use explicit change on Tendsto before rw dslope_same. No raised heartbeats or instance modifications in new leaves.