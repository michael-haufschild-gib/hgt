# HB FC: original future pulse identity and regularity

Chain: literal theta-cusp → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Full temporal/metric/QNM matching and RH remain open. Goal stays active.

New leaf formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFuturePulseIdentity.lean (339 lines), namespace RHTower.D4BMFuturePulseIdentity. Imports FuturePulseAssembly and FutureSourceBridge.

Verified: response_eq_compactFutureAction identifies independently admitted original future response at tau=r-exp(W)/2,x=-exp(W)/2 with compactFutureAction in Fin 4 coordinates (r,W,X,k). original_response_smooth proves its joint C∞ regularity. Exact gated original finite-cut → null coordinates → exponential source substitution → direct-minus-image compact cut; actual support truncates at r+pulseSpan(r); FB compactMean_cut_tail removes three omitted strips; uniqueness with original truncatedResponse_limit closes identity. No analytic matching premise introduced. This closes original full pulse regularity, not full metric/current/QNM matching.

Next hard obligations: horizon-cap regularity, differentiated metric/current identification and noncompact left-QNM admission. Do not return to source-event identity or redo experiments/results.md. Combined cap CSeed/kappa-CLift might be preferable to separate cap regularity, but this is only an untested possibility, not a fact.

Own log DN82 in docs/drafts/pipeline/1-in-progress/hb-dn-source-resolvent-facts.md. Current working card hb-fb-full-future-pulse-assembly.md updated, as are own EU and FA cards. Frontier remains read-only, STATUS untouched.

Efficiency: check4 failed at 92.59s with deterministic isDefEq timeout in continuity slice and unresolved interval measure. Fixed using generic continuous_clamped_slice(F,hF,v), preventing huge actual-source unfolding, and explicit (μ := volume). No heartbeat changes. check5 passed 41.29s. Exact isolated leaf audit passed 104.41s, 2 jobs, no warnings. Installed source bytes verified identical to audit and installed olean 629400 bytes. Umbrella import wired without building umbrella. No Lean processes from these checks remain; final lint was launched separately and must be collected in current turn. Retain /tmp/hb-fc-check5.log, /tmp/hb-fc-exact-audit.log and /tmp/hb-fc-formal-lint.log; scratch and isolated audit tree are being removed.

User asked why build was running for 30 minutes. Process inspection initially found NO Lean/lake compiler running; collected old handle38919 exit1, log92.59s. There was no evidence identifying cause of displayed30min. Do not invent UI cause or pretend a30min process was killed. Completed targeted fixes and required leaf audit with one foreground Lean process, guarded240s. No full builds, umbrella builds, #print axioms, git or launch.sh.
