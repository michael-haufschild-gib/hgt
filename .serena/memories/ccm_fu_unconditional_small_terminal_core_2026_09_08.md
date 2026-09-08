# CCM-FU unconditional terminal-core endpoint — 2026-09-08

RH goal active, NOT solved. This turn made actual progress: an unconditional source construction removes prepared-front and prior-energy premises for a favorable terminal ENDPOINT. It does NOT give a bounded path reaching that endpoint or the final signed Abel bound.

Full chain: actual divisor source → renewable signed reserve → exhaustive prime selection → uniform signed Abel bound → RH.

## New closed main theorem
formal/GaloisForLFunctions/RHTower/MobiusDivisorTerminalCoreExistence.lean:
exists_mobiusDivisorSmallTerminalCore (line122).
∃b≥8,∀ε>0,eventuallyN, with M=7(b+1)(4N), A=primesInIoc(b(4N),(b+1)(4N)), B=mobiusDivisorActiveLatePrimes M:
∃P⊆selectionPrimes M, selectionPrimes M\(A∪B)⊆P,
smallSelectionPrimes M⊆P, |F(M,P,∅)|≤5√M, Ψ(M,P)≤εM².
No initial energy, freshness, prepared-core, RH or numerical premise.

Proof: start P0=all primes below M outside A∪B. All remaining quotients≤7; M≥64 makes core terminal, with fixed core<8 already processed. Positive A singleton equals old quotient7 source, B singleton is negative literal late channel. Head identity H+X−Y=S. New private positive_window_covers_total compares positive mass lower bound c n√n/(2log(bn)) with existing S(M)logM/(M√M)→0, so |S|≤X eventually. Old total/lateMass→0 plus positive mass gives |S|≤Y. Therefore −H≤X and H≤Y. Select actual one-sign source cover with overshoot≤5√M, giving P=P0∪L and small head. Prime sparsity gives subquadratic current and every single successor energy.

Private helpers in main file: positive_window_covers_total, late_covers_total, isolated_singleton_eq. First import PositivePrimeSupply, not GrowingSignedPrimeBatches.

## New reusable module
formal/GaloisForLFunctions/RHTower/MobiusDivisorTerminalBudgetRecovery.lean (~152 lines).
4 public declarations:
1 mobiusDivisorSmallSelectionPrimes_subset_of_quotient:
M≥(J+1)², all remaining M/p≤J → smallSelectionPrimes M⊆P.
2 mobiusDivisorSuccessorEnvelope_le_terminal_density:
terminal P, remaining quotient≤J, |head|≤a√M, a≥0 →
Ψ≤[(a+.6J)²+.36J²*pi(M)]M.
3 eventually_mobiusDivisor_terminal_envelope_small:
fixed J,a≥0, ε>0 → eventuallyM uniformly in all P with bounded remaining quotient and small head, Ψ≤εM².
4 exists_signedScalarHeadCover:
finite A,B, 0≤c≤a on A, 0≤−c≤a on B,
−h≤ΣA c and h≤ΣB −c → ∃L⊆A∪B, |h+ΣL c|≤a.
Mass-cover input is directional; requiring |h| covered by BOTH supplies would be too strong here.

Private prime_density_zero uses existing tendsto_primeCounting_nat_ratio and inverse log.
Private singleton_abs_bound and terminal_leaf_squares_bound retain all literal source coefficients.

## Exact remaining obstacle
Existing exists_mobiusDivisorTerminalPrimeOrder_iff says terminal completion below budget iff current energy AND S(M)² fit budget. New result supplies current energy with arbitrarily small quadratic constant; it does not improve S beyond the existing PNT o(M√M/logM). All remaining operations are isolated but their accumulated signed sum still carries the RH-bound S=O(M). Reachability from empty under one global quadratic ceiling is also unproved.
Next turn should attack cumulative signed mass / complete-path arithmetic, NOT merely refine density constants, create another finite receiver, re-audit old lemmas, or describe endpoint existence as RH progress beyond this precise closure.

## Validation and cleanup
Both scratch files passed lake env lean. Both exact leaf oleans emitted via lake env lean file -o exact. Main final emit with reduced imports passed. Base module docstring added after identical proof emission (no mathematical changes). All FIVE new public declarations audited ONCE through temporary #print axioms: only propext, Classical.choice, Quot.sound. Do NOT repeat those audits.
Both modules wired into RHTower. No umbrella/full builds. Lake package audit pending; prior scoped package planning expands broad dirty dependency graph, do not repeat preflight/build.
Generated indexes refreshed; formal_tools.py lint --check-generated PASSED (existing large-file warnings only). Scratch /tmp/ccm_terminal_recovery.lean, ccm_terminal_core.lean, ccm_terminal_core_tail.txt, ccm_terminal_axioms.lean removed. All owned exec sessions exited; no owned Lean running. No computations or RunPod activity.

## Docs
3-formalized/ccm-fu-small-terminal-core.md: exact statement, complete proof, validation, remaining endpoint criterion.
1-in-progress/ccm-fu-terminal-budget-recovery.md: remaining bounded complete-path work.
1-in-progress/ccm-fu-inherited-debt-source-cycles.md: current remaining obligation updated, previous producers preserved.
universal-law-field/STATUS.md: added MUST-CONTROL-COMPLETION-AFTER-LOW-ENERGY-PREPARATION (route-independent distinction).
FRONTIER MAP READ ONLY, unchanged by us.
Shared worktree has external edits/commits including our files committed during active work. No commit/push by us. Preserve other edits.

## Lean efficiency / pitfalls found
One foreground owned Lean process at a time. No computations local (file tooling/Lean/index allowed).
In main file, unqualified mem_sdiff rewrite resolved incorrectly; explicit Finset.mem_sdiff works. Avoid dsimp [P] on concrete finite prime cores: it can unfold all finsets into List membership. Use change with opaque selectionPrimes and explicit Finset.ext, then Finset.mem_sdiff.
Actual mathlib name Finset.sdiff_sdiff_eq_self exists (Data/Finset/SDiff.lean:223), though final main proof uses explicit membership.
Prime density inverse-log term needs explicit change to pointwise (Real.log M)⁻¹ before field_simp.
No subagents authorized. New turn must state complete proof chain and decisive target. Frontier map remains strictly read-only.