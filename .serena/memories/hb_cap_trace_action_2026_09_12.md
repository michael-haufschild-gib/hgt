# HB cap trace/current research, 12 September 2026

Active goal remains literal theta -> Xi -> retained spin two -> actual causal/left-QNM action -> fixed Hawking-clock extinction -> RH. Complete extinction and RH are unproved.

Own facts/no-go log: docs/drafts/pipeline/1-in-progress/hb-extinction-own-research-log.md, now 24 entries. Own paper card: docs/drafts/pipeline/1-in-progress/hb-radiative-source-period-attack.md. Entries 22-23 are new audited Lean results; entry 24 is a paper proof only. No other worker's results were added as own discoveries.

New leaf: formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCapTraceAction.lean, namespace RHTower.D4BMCapTraceAction, 264 lines. SHA256 623290b6d38b2272588777d5fb55f46c6699ab054963c7aa5e577275b4c18313. Scratch lake env lean /tmp/hb-cap-trace-action.lean passed without diagnostics. Exact isolated cached lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCapTraceAction passed (16s, 2 jobs). Target artifacts published with source hash guard. Umbrella import exactly once. scripts/formal_tools.py lint passed with existing large-file warnings. No heartbeat/transparency/instance overrides in new leaf; only autoImplicit false. No #print axioms or numerical computation. All owned Lean/research/lint sessions terminated normally.

Closed results:
- contact_is_original identifies regular ingoing master contact with existing original ingoingContact at every exterior point.
- physical_current_add_contact identifies all four actual Einstein stream current + source contact components. Radial component: R^-2 sum[(f P_R+P_v) A Q-(f Q_R+Q_v) A P], f=R^2-1, A=rough angular Laplacian minus one. Time/cusp faces retain normal/mixed curls.
- radial_horizon evaluates regular expression at R=1 to sum[P_v A Q-Q_v A P]. This is not an integral-field limit theorem.
- scalarTrace_is_cap_limit reuses audited original scalar cap limit. covectorTrace_is_coexact proves actual coexact derivative of that scalar trace. Actual time derivative and angular trace action also proved.
- traceFlux_eq_lift_angular: two physical-source branches' boundary trace pairing equals lift's contact-corrected radial trace expression.
- traceFlux_original_clock: K exp(-6v) chi(v)^2 angularPair. angularPair=(2lambda-2) angularSquare+2 gradientPair. Important original normalization: fullGradientEnergy_coexact gives *dE=2 fullGradientCovector, so writing the gradient piece as *dE gives coefficient ONE, not two.
- traceFlux_finite_integral retains K clockMass(V) angularPair.
- traceFlux_physical_step: v>=1,T>=0, traceFlux(v+T)=exp(-6T)traceFlux(v). Same physical time, no retuning. No universal nonzero claim, complete-action invariance or extinction inferred.

Unproved actual interface: derivative interchanges for cap's infinite integral and horizon limit; products with actual left QNM; weighted normal remainders; full nonlinear SS/SV/VV, quadratic corrections, spin two, metric weights and other faces. Physical cap stream is R H, so R belongs in D_R P. Exact finite-radius error decomposition CD is recorded on paper. Field-value convergence alone does not discharge it.

New paper opposite-horizon datum PH: tau=v+x, x->-infinity, H -> -l_inf[ integral_0^infinity g'(u) M_Q(1+2exp(u-v))du - integral_v^infinity g'(u) M_Q(2exp(u-v)-1)du ]. Direct shift u=v+2x+h changes invariant to 1-c(x)+c(-x)exp(u-v), c=exp x/cosh x; c(x)->0,c(-x)->2. Image support u>=v remains. Onset removes negative u. Direct radius <=u+|v|+log6, image <=u+|v|+log4 on remaining u>=0. Existing a0<c0<2 growth/decay supplies integrable exp((a0-c0)u). DCT proves paper PH. Its vanishing/nonvanishing and cancellation with advanced/seed/pulse data remain unproved. This exposes a past face in causal comparison; cap subtraction alone is not causal identification.

Search: two deep/method whole-corpus queries partial=false, 57317 files, compiler snapshot 44818 pending. Useful actual current/contact/native primitive hits inspected and verified in scratch. Follow-up cap-actual-trace-admission-deep.json partial=true,57326 files, no verified actual cap derivative admission. Files in formal/.lake/hb-extinction-scratch: cap-physical-current-traces-deep.json, cap-angular-derivative-methods.json, cap-actual-trace-admission-deep.json. Broad recent arXiv searches returned no applicable Jun-Sep2026 theorem; direct date-sorted pages failed cache/429. Retrieved Getzler arXiv math/0002164 is 2000 hydrodynamic Hamiltonian deformation paper, no HB theorem adopted.

Validation logs/scripts: /tmp/hb-cap-trace-action-check.log (empty), /tmp/hb-cap-trace-action-audit.py, /tmp/hb-cap-trace-action-audit.log, /tmp/hb-cap-trace-action-lint.log. Prior FutureHorizonCap leaf unchanged and not rebuilt. Shared foreign edits were preserved.