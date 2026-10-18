# Successor obstruction and minimal phase refinement

- **ID:** thim-primary-002
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Multiplicative observation states support deterministic successor evolution exactly at horizons N≤2; full future sieve observations instead classify residues modulo L_N=lcm[1,N].

## Goal and plan

1. Audit current corpus against existing averaged successor phase-loss results.
2. Prove the exact pointwise successor obstruction, with arbitrarily remote witnesses.
3. Extract and formalize the positive survivor: residue phase is a complete invariant of every future observation; a finite N-step trace suffices.
4. Audit original Lean source and every public axiom closure, wire umbrella, refresh indexes, run lint, update ledger and clean scratch files.

## Paper proof [PROVED HERE]

Let C_N be the complete multiplicative observation state from package 001 and L_N=lcm[1,N].

For N≥3, states at 1 and L_N−1 agree: any active divisor of L_N−1 also divides L_N, hence divides 1. Their successor states differ, since N divides L_N but cannot divide 2. Adding a sufficiently large common multiple of L_N gives witnesses beyond any prescribed bound. For N≤2 every observation is determined by the constant and parity tests, and these do evolve deterministically under successor.

For the positive refinement, observations at k+t and l+t for all weights are equal exactly when every active divisor has the same divisibility test at those integers. For fixed d≤N, choose t=(d−k mod d) mod d<d≤N. Then d divides k+t, hence l+t, which forces k≡l mod d. Combining all d by their lcm gives k≡l mod L_N. Conversely this congruence preserves every translated active divisor test. Thus an N-step trace (t<N) already recovers the entire future observation class. No assertion that N is the sharp trace length.

The return offset satisfies (k+t) mod d=0 because adding d−(k mod d) cancels the residue; reducing the offset modulo d does not change this. If k≤l, agreement modulo each active d means d|(l−k); taking their lcm gives L_N|(l−k). If l≤k, reverse the two integers. This closes the combination step without any analytic input. At N=0 the lcm is 1, the trace is empty, and every sieve response vanishes, so the same theorem holds.

For cofinal counterexamples choose T=N+B+1, k=1+TL_N and l=L_N−1+TL_N. Positivity of L_N gives k,l>N+B. Package 001's exact modulus recurrence preserves their common present state and their unequal successor states. No upper observation-window bound is used.

For N≤2, every active divisor is 1 or 2. The constant test is unchanged by successor, and the divisibility-by-two test is complemented. Thus equal current states have equal successor states. An explicit update is F(x)=C_N(x+1); idempotence C_N(C_N(k))=C_N(k) verifies its action. Conversely any update F, linear or nonlinear, must send equal current states to equal successor states and is contradicted by the cofinal pair above.

The phase P_N(k)=k mod L_N satisfies P_N(k+1)=P_N(P_N(k)+1), P_N(k+l)=P_N(P_N(k)+P_N(l)), and the analogous product law. Equality of phases is equivalent to equality of all future weighted sieve responses. This equivalence is the precise minimality claim: any identification preserving every future response must preserve phase.

## No-go closure

- **Proposed closure:** successor of C_N(k) determined by C_N(k).
- **Killing mechanism:** indistinguishable units 1 and L_N−1 have distinguishable successors at every N≥3, even after arbitrary trans-horizon translation.
- **Positive survivor:** complete future observations are exactly residue phases modulo L_N; the phase retains deterministic addition and multiplication.
- **Status:** dependency-closed paper proof, original-source Lean audit, and all 11 public axiom closures passed without warnings; the exact positive survivor is formalized. Do not count the negative and positive parts separately.

## Corpus novelty boundary

Both hybrid searches returned useful partial results (deadline-limited retrieval). Prior `sieve_successor_representable_iff` classifies when a translated scalar response can be represented by another divisor weight; its update is linear in the divisor-response space. This package instead rules out every nonlinear update on the complete present observation state and identifies the exact future-equivalence relation. Prior true-lag predictors and additive orbit projections concern coefficients/averaged pairings, not this pointwise observer-state classification. Exhaustive source checks of both field directories found no equivalent classifier. No external-priority claim.

## Scope

Owned leaf: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/SuccessorStateObstructionAndPhaseRefinement.lean`. Package 001 remains unchanged. Field README is read-only; other agents' work is preserved. No hgtl7, RH claim, computations, added axioms, full builds or heartbeat increases. update_plan unavailable; this card is the persistent plan.

## Final verification

Original-source audit passed without warnings using `lake --old env lean` with the leaf as input and its `.olean`/`.ilean` outputs. All 11 public declarations have exactly the standard axioms propext, Classical.choice, Quot.sound. Every public API row and the single umbrella import were verified. Index refresh succeeded.

Evidence: `logs/thim-primary-002-audit.json` and `logs/thim-primary-002-axioms.txt`. Global lint exits 1 on two concurrent foreign RHTower omissions and the pre-existing ArithmeticPositivityTheory/TransHorizonIncidenceMechanics package-root area-registration diagnostics. No proof-debt finding concerns this leaf. No full or umbrella build was run.

The user cleared the research goal during the final audit. This already-written package was closed out; no further research is authorized by the cleared goal.
