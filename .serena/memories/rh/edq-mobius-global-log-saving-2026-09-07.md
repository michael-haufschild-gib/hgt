# EDQ complete arithmetic source: unconditional arbitrary-log saving

RH/EDQ goal remains ACTIVE and NOT achieved. No unconditional RH proof/falsification exists in this work. Current full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH. Previous completion: `mem:rh/edq-mobius-gram-cancellation-2026-09-07`.

## New completed artifact
`formal/GaloisForLFunctions/RHTower/EulerDeletionMobiusGlobalLogSaving.lean`, 389 lines, namespace `RHTower.DeletionMobiusGlobal`, imports only `EulerDeletionMobiusGramCancellation`; 12 public theorems, no new public definitions. `set_option autoImplicit false`. Wired into `formal/GaloisForLFunctions/RHTower.lean` (one import). Card moved from 1-in-progress to `docs/drafts/pipeline/3-formalized/edq-mobius-global-log-saving.md`.

Finite signed arithmetic argument: if N,L≥1 and |M(k)|≤eps*k for every k≥N, finite Abel summation on the entire omitted µ-floor sum yields `|floorResidual N n|≤2 eps n L` whenever 1≤n≤NL. Thus literal primitive A_N(n)=−raw modular approximant obeys `norm A_N(n)≤1+n*(|H_N|+2 eps L)` on that whole extended prefix. For any positive integer T and any real b satisfying the prefix bound, the genuine complete arithmetic energy is ≤`4+2*T*b²+N²/T`. (No b≥0 premise needed for this generic finite-prefix energy theorem.) The head uses the inverse-square sum≤2, the entire complementary tail uses norm primitive≤N and inverse-square tail≤1/T. Specialization T=NL gives `E_N≤4+2*N*L*(|H_N|+2 eps L)²+N/L`.

New reverse carrier comparison `norm(rawVec_N)²≤E_N`; combined with old PET gives two-sided `norm²≤E_N≤2 norm²`.

For q natural, r=q+1, P=(log N)^r, L=floor P. Existing corpus Mertens rate at exponent2r gives C≥0 and uniform eps=C/P² beyond N, while existing harmonic rate gives |H_N|≤1/P². Eventually P≥2, P/2≤L≤P, P≤N; b≤(1+2C)/P. Complete energy ≤(6+2(1+2C)²)*N/P. Hence full energy, full raw norm squared, ABSOLUTE complete signed cross sum, and absolute real current at EVERY actual nontrivial zero are `o(N/(log N)^q)` for every fixed natural q. Cross absolute bound uses norm² + diagonal, with existing diagonal≤4log N. Current uses existing fixed-zero transfer constant.

## Public theorem locations
59 floorResidual_le_of_mertens
104 primitive_extended_prefix_le
130 primitiveEnergy_le_of_extended_prefix
186 primitiveEnergy_le_of_mertens
203 modular_norm_sq_le_primitiveEnergy
232 primitiveEnergy_log_saving
309 modular_norm_log_saving
317 abs_cross_log_saving
360 primitiveEnergy_log_pow_div_tendsto_zero
365 modular_norm_log_pow_div_tendsto_zero
370 abs_cross_log_pow_div_tendsto_zero
376 abs_sourceCurrent_log_pow_div_tendsto_zero

## Remaining mathematical gap
N/log^q ceilings remain MUCH larger than polynomial-log ceilings. They coexist with the previous hypothetical off-line superlogarithmic escape. Do not exchange quantifiers or allow q to grow with N without uniform constants/thresholds. Still need actual cofinal polynomial-log signed-cross upper bound, or zero-dependent cofinal polynomial-log current upper bound, or another independent source annihilation/comparison. No RH converse is asserted for full norm/cross ceiling. New work is a derived [BRIDGE], not a new primary conjecture or route label.

## Validation completed, do not repeat
- Full actual `/tmp/edq_global_finite.lean` scratch session26759 exited0 with EMPTY diagnostic log, after fixing first-pass indexing/casts/syntax. All actual source proofs, including whole infinite energy, checked.
- Final `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionMobiusGlobalLogSaving`, session4500 exited0. ONLY new leaf compiled (7.4s); graph13109 jobs otherwise replayed cached outputs. No umbrella/full build run by this agent.
- ONE final new-only axiom file session55031 exited0. All12 public declarations depend exactly on propext, Classical.choice, Quot.sound; no sorryAx or added/computational axioms. Private helper closure covered through public results. No repeat old axioms.
- `python3 scripts/formal_tools.py lint` session78008 exited1 ONLY because concurrent unrelated `MobiusDivisorCoupledTwoSourceCone`, `PartialSubsetEnergyOrder`, `ThreePlaneSourceMargin` were unwired. No new EDQ lint error. Do NOT claim global gate passed; do not modify/rebuild foreign unfinished modules to hide it. Existing large-file warnings too.
- Index refresh completed:4 changed,0removed,33063files,403329decls,3947gapmarkers.
- Scoped git diff whitespace, explicit untracked-new-file whitespace, all12 audit coverage, standard-only dependency set, no forbidden declarations, umbrella uniqueness, new documentation links passed.
- All owned Lean processes exited. Removed four `/tmp/edq_global_{api,axioms,finite,local}.lean` scratch files and `/tmp/edq_global_missing.txt`. Audit/build/check/lint/index and old diagnostic logs remain under `/tmp/edq_global.*.log`.

## Documentation
Frontier current topology sentence, new paragraph after GramCancellation, and EDQ table row updated with unconditional full-source bound and remaining growth gap. Concurrent edit changed the earlier EDQ topology sentence during work; replacement reread current text and preserved all other routes. STATUS appended route-independent `MUST-COMPARE-THE-FULL-GROWTH-SCALES`, explaining cutoff powers, nonuniform exponent thresholds, and complete complementary tails. Formalized card explicitly records unrelated global lint failure, not a passing gate.

## Important process/API lessons from this turn
The original shared cache temporarily lost successively imported own-tree oleans due OTHER task's large build `lake build +GaloisForLFunctions.RHTower.ConstrainedWeilTwistedOddTest`. Do NOT imitate or kill it. Earlier this agent repaired only needed EulerPrimitiveCommonTestXiTraceTransport, EulerPrimitivePolarizedHodgeBetaTransgression, EulerPrimitiveJointDepthOffDiagonalCountertransport, foreground sequential `lake env lean -o ...`; remaining missing dependencies restored by other workers. Final read-only closure scan had4439own-tree deps and ZEROmissing. Transient cache issue resolved, not a goal blocker.
On macOS `ps comm` truncates full paths and misses full-path lean/lake. Inspect `ps ... args`, first executable basename; PPID50845 is shared by other agents and is NOT ownership. Only exact owned scratch commands/PIDs may be cleaned.
A temporary Mathlib-only generic test wrapper using local notation `normalizedPrimitive => normalized primitive` silently generated a `normalized sorry` in the SECTION VARIABLE hypothesis. Exit0 plus `declaration uses sorry` warning was REJECTED. Diagnostic print showed sorryAx; this wrapper was discarded. Actual corpus proof has no such wrapper, passed with autoImplicit false and final new-only standard axiom audit. Do not reuse that notation pattern or interpret discarded wrapper as a corpus theorem.
Mathlib names: abs_add_le (NOT abs_add), Nat.card_Icc (NOT Finset.card_Icc). Nat.div_le_div_left numerator may need explicit typed intermediate statement before exact_mod_cast; expose let w first. On this toolchain add_le_add_right prepends common term; prefer `add_le_add _ le_rfl` to append it. `field_simp` can finish a goal, so trailing ring can cause No goals. `|*` without whitespace lexes badly in real absolute products; write `| *`.

## Latest persistent user steering
Read entire `docs/meta/scientific-method.md` this turn and explicitly acknowledged user: computations ONLY when outcome uncertain and can change hard-open-problem approach; never predictable by reasoning or hours-long. This bridge is already paper-derived, so NO numerical experiment run. Future numerical experiments: freeze informed primary truth-hunch independently of proof toolkit, falsifiers/discriminating parameter-free predictions; [BRIDGE] does not replace primary conjecture. Use RunPod ONLY `ssh root@157.157.221.29 -p 27094 -i ~/.ssh/id_ed25519`, optimize multicore, bounded runtime, download/document results in `docs/drafts/pipeline/2-fully-proven/computations`. Local symbolic proofs and Lean checking/repo bookkeeping remain allowed. No numerical results inside Lean proofs.
