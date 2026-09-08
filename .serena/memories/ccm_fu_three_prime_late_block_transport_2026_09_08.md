# CCM-FU: complete third interactions and late-block successor budgets

Goal ACTIVE, RH unproved. Previous goal turn PROGRESS (prescribed-prime universal tail coverage); this turn PROGRESS (eight actual-source theorems). No external blocker. Frontier READ ONLY by user override. Frontier and universal STATUS untouched. No subagents, commits, pushes, full/umbrella builds or math experiments this turn.

## New checked modules

formal/GaloisForLFunctions/RHTower/MobiusDivisorThirdEnergyInteraction.lean:
:24 definition mobiusDivisorThirdEnergyDifference: eight-term D3 = Qtrip - sum Qpairs + sum Qsingles - QP, as p,q mixed difference at P+r minus at P.
:36 mobiusDivisorThirdEnergyDifference_eq: for active distinct unprocessed p,q,r, sum over all free R. With a,b,c,d,e,f,g,h at R,R+p,R+q,R+r,R+p+q,R+p+r,R+q+r,R+p+q+r, D3=2 sum_R(a*h+b*g+c*f+d*e). All overlaps retained. Uses existing mixed-two identity and exact fibre insertion. hrP structural parameter unused internally (_hrP).
:136 mobiusDivisorThirdEnergyDifference_empty_nonpos: D3(empty)<=0 including active triples; actual parity gives odd complementary cardinality sum.
:165 mobiusDivisorThirdEnergyDifference_late_nonpos: every core P of late primes s<M<=2s has D3(P)<=0 if M<=p*q*r. No head sign, Q ceiling, reserve or cardinality premise. Triple parent vanishes; nonempty parity after late blocks is already proved.
:207 mobiusDivisorThirdEnergyDifference_union_late_primes: arbitrary starting core P, unprocessed late block L, distinct p,q,r outside L:
D3(P union L)=D3(P)+2*(sum_s in L signedChannel_s)*F_P({p,q,r}).
No primality or energy condition on P, no active-prime condition on p,q,r needed for identity. All overlaps. Proof takes eight instances of EXISTING Q(C+L)=QC+2headC*S+S²-J. Constant terms cancel. Third difference of head = retained triple fibre (private head_third). No asymptotic argument.
:257 mobiusDivisorThirdEnergyDifference_union_late_eq_of_le_product: arbitrary-core D3 unchanged by L if M<=p*q*r, via support.
:275 mobiusDivisorThirdEnergyDifference_late_eq_unsigned: at original core, D3(L)=D3(empty)+2*(sum unsigned K_s)*K_(pqr). Signed block mass=-unsigned mass; empty triple fibre=-K_(pqr). Includes active overlaps.
:319 mobiusDivisorThirdEnergyDifference_late_nonpos_iff: exact threshold D3(L)<=0 iff 2mass(L)*K_(pqr)<=-D3(empty). Does NOT assert every block meets it. Positive survivor: exact overlap payment and inactive boundary.

formal/GaloisForLFunctions/RHTower/MobiusDivisorLateBlockSuccessorEnvelope.lean:
:22 mobiusDivisorSuccessorEnvelope_late_block_le_max_endpoints: arbitrary P, unprocessed late block L, EVERY R subset L satisfies
Psi(P+R)<=max(Psi(P),Psi(P+L)).
Full exact successor envelope, not merely Q or geometric Phi. For q outside L use existing actual-Q endpoint theorem at P+q. For q inside L but not R use Q endpoint law at subset R+q. Covers all current/successor energies. No head sign or accumulating per-step loss. Every order through late-only block is admitted if two endpoint envelopes are admitted. Does NOT supply admitted endpoint or allow nonisolated blocks.

## Validation/cleanup

Eight public theorems plus one definition, two new leaves. Foreground scratch lake env lean and exact leaf checks with only their olean emission passed without Lean warnings. Imports wired after UniformSuccessorTransport and SmallCoreInteractions respectively. No old prerequisite rebuilt, no umbrella built. Known Lake packaging audit remains pending: graph expands broad stale rebuilds; do not repeat preflight/build.
One /tmp audit of exactly nine NEW closures found only propext, Classical.choice, Quot.sound. No old re-audit, no computation premise. Global formal lint passed (existing size warnings), index refreshed, scoped diff and new-file trailing-whitespace checks passed.
All owned Lean sessions terminal. Process scan found no lake env lean/lake build/owned target Lean. Removed exact four temps: /tmp/ccm_three_prime.lean, /tmp/ccm_late_envelope.lean, /tmp/ccm_three_prime_audit.lean, /tmp/ccm_three_prime_lint.log. New required oleans retained. No remote process/computation this turn.

## Docs

Stage3 docs/drafts/pipeline/3-formalized/ccm-fu-three-prime-late-block-transport.md: exact formulas, dependency-closed proofs, validation, open scope.
Stage1 docs/drafts/pipeline/1-in-progress/ccm-fu-three-prime-repair-interaction.md links closure. It retains explicitly PAPER-ONLY refinement: if pqr>=M, D3 depends only on P below max(M/p,M/q,M/r)+1 by copied-fibre interpolation. General small-core filter identity NOT checked in Lean. Pair-products-all-inactive ->D3zero also paper-only here.
Stage1 ccm-fu-forced-prime-repair.md updated with closed third-interaction and intermediate-block components. Frontier and STATUS untouched. Unrelated shared worktree edits preserved.

## Next hard target

Chain: actual divisor source -> renewable signed reserve -> exhaustive prime selection -> uniform signed Abel bound -> RH. Main missing producer: choose admitted endpoints while including a prescribed nonisolated/small prime, retaining ALL successor comparisons. Third identity/late transport now closed; do NOT repeat them or add generic fourth-order identities merely to raise arity. First/second changes and retained triple fibre after NONISOLATED steps still need a signed source inequality. Late endpoint theorem removes intermediate loss only once endpoints are known. Prior universal prescribed LARGE-prime theorem is fixed-core/asymptotic; doesn't cover least omitted small prime or uniform cutoff onset.
No new computation needed for analytically predictable identities. Prior RunPod all-prescribed repair screen remains finite evidence (39220 cases, no failures) in mem:ccm_fu_prescribed_prime_pair_reserves_2026_09_08; no repeated/larger scan scheduled. New experiment must have distinct discriminating hypothesis, frozen scientific-method protocol, RunPod only, short multicore execution, downloaded results/cleanup.

Lean: Finset.notMem_empty is current name (not not_mem_empty). Standalone literal sets need explicit : Finset Nat for .card/products/prime predicates; otherwise Singleton metavariables stick. simp only [← insert_union] normalizes eight block cores. Private parity_product_nonpos/cross_three_nonpos helpers live in new leaf. Using existing complete block-energy formula avoids difficult R=singleton cases.
