# CCM-FU second-centered hyperbola and improved unit floor — verified 2026-09-07

## Goal / honest frontier
RH goal remains ACTIVE and OPEN. Full chain: completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → coherent prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH. Source SD1, all-cutoff two-prime ceiling, factor-two unit comparison and geometric reserve remain open. No conditional receiver is a completed RH proof.

## New closed analytic results
`formal/GaloisForLFunctions/HTGeometry/SecondCenteredModularAbel.lean` (254 lines, 2 definitions + 11 public theorems) defines B_d=(d²−1)/(12d), S_d(N)=r(d−r)(d−3−2r)/(12d), r=N mod d. Proves S(N+1)−S(N)=P(N+1)+B, |S|≤d²/12; exact mean sum P(k+1)=−dB; second finite Abel identity retaining mean and moving terminal phase; exact square-root clock gap and its antitonicity. For birth d² the gap ≤1/(4d³), giving actual mean/terminal error ≤1/(48d), including literal Ico(d²,M) transport. No computations as premises.

`formal/GaloisForLFunctions/RHTower/DivisorSecondCenteredHyperbola.lean` (331 lines, 9 public theorems) proves:
- Per-modulus centered channel C_d(M) lies between −1/24−d*w_M/24−1/(16d) and −1/24+d*w_M/12+5/(48d), d>0,d²≤M.
- With s=Nat.sqrt(M−1), C(M) lies between −s/24−s(s+1)w_M/48−H_s/16 and −s/24+s(s+1)w_M/24+5H_s/48.
- All natural cutoffs: −5√M/96−log(M+1)/16−7/96 ≤ C(M) ≤ −√M/48+5log(M+1)/48+1/6.
- For every ε>0 eventually (−5/96−ε)√M≤C(M)≤(−1/48+ε)√M; C tends to −∞. No convergence to one coefficient claimed.
- Smooth prefix ≥N/6−17√N; smooth Abel ≥√M/6−17log(M+1)/4−13 using exact kernel bound √k*(w_k−w_(k+1))≤1/(4k).
- Actual unsigned unit channel K_1(M)≥√M/16−5log(M+1)−14. For every ε>0 eventually K_1(M)≥(1/16−ε)√M.

These improve actual source control, but existing uniform upper K_d≤7√M is too loose to infer K_p≤2K_1. Need sharper actual upper bounds or direct dilation comparison. No numerical table was recomputed this turn.

## Verification complete — do not repeat
Both complete scratch proofs and both exact leaves checked with `lake env lean`, required new leaf oleans generated. No dependency/full/umbrella rebuild. Both leaves wired exactly once. Exactly 22 NEW public declarations axiom-audited once; only propext, Classical.choice, Quot.sound, no added axioms or computational certificates. Formal lint PASSED (large-file warnings only), index refreshed (4 changed, 0 removed). Scoped diff whitespace and new card links passed. Six exact owned /tmp scratch/log files removed; final strict process snapshot showed ZERO live lean/lake processes.

## Documentation
Formal card `docs/drafts/pipeline/3-formalized/ccm-fu-second-centered-hyperbola.md`; Stage1 duplicate absent. Updated two-prime local-blocks candidate, adaptive-prime-ceiling candidate, mobius-divisor source diagonal dominance, current frontier map and universal STATUS. New route-independent rule MUST-RECENTER-DISCRETE-PRIMITIVES: retain primitive mean, moving terminal phase and next centered remainder separately.

## Useful Lean details
PositivePrefix import introduces graph notation ≤s: always write a space in ≤ s. `Real.nat_sqrt_le_real_sqrt (a := N)` exists. `harmonic_eq_sum_Icc` has implicit n; use simp with Rat.cast_sum/inv/natCast and one_div. sum_div direction is (Σf)/a=Σ(f/a), so reverse for aggregation. `mobiusDivisorDilationChannel_one_eq_hyperbola` comes from existing MobiusDivisorAbelQuadraticDiagonal. Never rebuild existing dependencies merely to recheck them.

## Prior work
See `mem:ccm_fu_two_prime_local_factor_and_unit_obstruction_2026_09_07` for exact factor-two local criterion and unconditional failure alternative; `mem:ccm_fu_uniform_channel_square_root_and_reserve_2026_09_07` for uniform 7√M upper and 57M late-release budget. Reuse frozen unit-clock CSV through1024 for any new separately frozen diagnostics; avoid rerunning old screens.