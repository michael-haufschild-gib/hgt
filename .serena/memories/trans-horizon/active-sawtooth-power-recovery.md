# Active sawtooth power sampling and calibrated recovery

Fourth connected contribution, 2026-10-18. Open-ended goal remains active; do not mark complete. Prior facts: `mem:trans-horizon/all-horizon-radical-sawtooth-defect`, `mem:trans-horizon/radical-state-defect-normal-form`, `mem:trans-horizon/radical-checkpoint-sign-rigidity`.

Leaf: formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ActiveSawtoothPowerSamplingAndCalibratedRecovery.lean. Card: docs/drafts/pipeline/3-formalized/thim-active-sawtooth-calibrated-recovery.md. Ledger: logs/thim-radical-sawtooth-knowledge.md. SHA256 3f9d54ec171a4708fdbcd6db8b30335459f7e635ffc8ef042afc61feae975391.

## Exact results
Write A_N(c,j)=activeCenteredSawtoothSum N c j j. Twice A is the divisor transform of truncated(c-c/d). Explicit inverse activeSawtoothMobiusLift a d = (2*d/(d-1))*sum_{uv=d} mu(u)*a(v) recovers c(d) for 2<=d<=N, arbitrary c. For squarefree-supported c, any common exponent m>=1 replaces every sample with A_N(c,j^m).

Exact complete active-profile kernel = equality of coefficients [2,N]. Within squarefree support, only squarefree bases j in [2,N] are needed; all divisors of squarefree targets are squarefree and other coefficients vanish. Theorem active_squarefree_power_samples_eq_iff_tail_eq formalizes this reduction.

For weights equal on [2,N], response difference is constant H_c-H_b, where H=finiteHarmonicSum. Exact prefix law D_c(M)-D_b(M)=(H_c-H_b)*(s_b(M+1)-s_b(1)) for every M. Therefore finite reduced power samples alone determine every additive jump and every Dirichlet-energy window; adding one harmonic scalar recovers all visible coefficients [1,N] and every prefix defect. No zero-mean restriction. Main APIs: calibrated_active_power_samples_eq_iff_weight_eq, sieveRenormalizedPrefixDefect_eq_of_calibrated_power_samples, sieveDirichletWindow_eq_of_active_power_samples.

Uniform cofinal sampling: exists_calibrated_power_recovery_above chooses m=B+1, putting every measured j^m>B for j>=2, uniformly in weights. This is power sampling, not a full-period translation scheme.

Stability: active_power_samples_coefficient_stability proves |c(d)-b(d)| <= 4*sum_{uv=d}|A_N(c,v^m)-A_N(b,v^m)|. Factor four independent of horizon/exponent multiplies divisor-indexed l1 error. Do NOT claim a divisor-count-independent sup-norm bound. Coefficients outside [1,N], including zero, stay invisible. No global fixed-Mobius/damped sign theorem follows.

## Verification
20 public theorems + 1 public definition + 1 private helper. Actual source compiled with lake --old env lean -o ... exit0/no warnings. Axiom scratch exit0: all22 closures exactly propext/Classical.choice/Quot.sound. Unique field umbrella import, MainTheorems reachability, fresh olean, all21 public API entries, source hygiene and whitespace verified. Evidence logs/thim-recovery-{lean,axioms,index,lint}.txt and logs/thim-recovery-audit.json. Index exit0. Final lint exit1: eight unrelated unwired leaves (seven BiScaleUncertainty, one BezoutValuationIncidence) and existing THIM field-umbrella registration. No own-leaf finding or stale generated file after one refresh. First-run logs preserve stale findings. Global clean status not claimed.

All7 owned scratch files removed; all owned jobs terminal. No README edits, numerical experiments, full builds, added axioms, heartbeat changes, commits or pushes. Field README read-only to this agent, read fully each new turn. User forbids hgtl7. One owned foreground Lean process at a time; other agents build concurrently. Serena ignores Lean, use rg/read/patch fallback. update_plan unavailable, pipeline cards track plans. Before next topic run documented research search directly; corpus coverage was complete for hybrid search but some source-only compiler freshness, no external novelty claim.

Open research frontier: fixed nonnegative damped families impose extra multiplicative/sign structure beyond squarefree support, unit normalization and coefficient bounds. These conditions alone cannot control all canonical radical representatives. Existing corpus envelope through 3N and parts of next band; do not claim residual global sign. Period drift belongs to another track.