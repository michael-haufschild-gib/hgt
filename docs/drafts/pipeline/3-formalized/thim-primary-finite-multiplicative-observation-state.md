# Finite multiplicative observation states beyond every horizon

- **ID:** thim-primary-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The lcm of active divisors completely classifies all fixed-horizon sieve observations, admits exact multiplicative evolution, and has cofinal representatives.

## Goal

Develop fixed-horizon mathematics valid for arbitrarily large observation integers. This contribution concerns arithmetic information retained by the sieve, with no RH claim. Target remains 100 significant contributions; this card counts as one only after proof and audit.

## Plan

1. Search current corpus and check novelty against additive gcd-orbit projection and rough absorption.
2. Prove the complete observation-state classification, multiplicative transition, and cofinal recurrence.
3. Formalize one leaf, audit its original source and all public axiom closures, wire umbrella, run lint/index, record crisp facts.

## Paper theorem and proof [PROVED HERE]

Let A_N(k)={d:1≤d≤N,d|k}, C_N(k)=lcm A_N(k), and L_N=lcm[1,N]. Empty lcm is 1.

* C_N(k)|k and C_N(k)|L_N. For 1≤d≤N, d|C_N(k) iff d|k. Thus every sieve value at k equals its value at C_N(k).
* Equality for every real weight implies equality of every divisor indicator by testing delta weights. This implies equality of A_N, hence C_N; the converse follows from the preceding identity.
* For d|kr, d divides gcd(d,k)gcd(d,r). Each gcd is a positive divisor ≤d, hence an active divisor at its respective factor. Therefore d|C_N(k)C_N(r). The converse follows from C_N(k)|k and C_N(r)|r. Consequently C_N(kr)=C_N(C_N(k)C_N(r)).
* Since every active d divides L_N, A_N(k+tL_N)=A_N(k). Positivity of L_N gives representatives above every prescribed bound. Finite state reduction does not force the observation integer below the horizon.

All entries of [1,N] are positive, so L_N is positive even for N=0 (empty lcm is 1). Since C_N(k)|L_N, the states lie in the finite interval [1,L_N]. Equality of states therefore gives an exact finite multiplicative quotient. Every observation-equivalent integer is divisible by C_N(k), so C_N(k) is also the least positive representative. At k=0 the active set is the entire interval and C_N(0)=L_N; the same proofs apply. At N=0 the sole state is 1 and all sieve responses vanish.

For every B, choose m=k+(N+B+1)L_N. Then m>N+B and every multiplicative context r and every real weight c satisfy sieveSeq_N(c,mr)=sieveSeq_N(c,kr). This is a statement about arbitrarily remote trans-horizon observations, not an assumption that the actual observation window is short.

## Novelty boundary

Existing `sieveGcdProjection` transports coefficients under additive orbit averaging; this candidate classifies observation integers under all weights and gives multiplicative evolution. Existing rough absorption is a special case of state 1. Existing complementary-quotient laws evaluate bands; they do not classify these observation states. Searches are evidence of corpus novelty, not an external priority claim.

## Gates

- [x] Corpus searches executed; existing band work left untouched.
- [x] Dependency-closed paper proof, including zero and empty-horizon cases.
- [x] Complete scratch implementation and API check passed without warnings.
- [x] Original Lean leaf audited without warnings, raised heartbeats or computational examples.
- [x] All 16 public declaration axiom closures checked: exactly propext, Classical.choice, Quot.sound.
- [x] Umbrella wired, index refreshed, every public API row verified, lint run; global lint caveats below. Ledger finalized and owned scratch files cleaned.

## Scope and ownership

Owned leaf: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FiniteMultiplicativeObservationState.lean`.
Owned ledger: `logs/thim-primary-knowledge.md`. README is read-only. Concurrent untracked complementary-quotient work is not owned or counted here. `update_plan` is unavailable; this card is the persistent plan.

Serena rejects this Lean path as ignored; symbol retrieval was attempted and file patches are the fallback.

## Evidence and limits

The first hybrid search completed with full source inventory but mostly pending/stale compiler metadata. The second hybrid search timed out with partial lexical hits; those hits identify the existing additive projection work. A field-scoped lexical search plus exhaustive source-text checks found no equivalent state classifier. Actual applicability is established by Lean, not the search metadata. External mathematical priority is not claimed.

This package does not prove quantitative cancellation, additive successor closure, or a window-uniform error bound as N grows. Those remain separate mathematical questions.

## Formal audit

Original-source command passed without output or warnings:

```text
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/TransHorizonIncidenceMechanics/FiniteMultiplicativeObservationState.olean -i .lake/build/lib/lean/GaloisForLFunctions/TransHorizonIncidenceMechanics/FiniteMultiplicativeObservationState.ilean GaloisForLFunctions/TransHorizonIncidenceMechanics/FiniteMultiplicativeObservationState.lean
```

All 16 public declarations are indexed and audited in `logs/thim-primary-001-axioms.txt`; machine-readable audit is `logs/thim-primary-001-audit.json`. No full or umbrella build was run.

Final global lint exits 1: seven concurrent foreign umbrella omissions, plus two pre-existing package-root/area-registration diagnostics for ArithmeticPositivityTheory and TransHorizonIncidenceMechanics. These were not changed outside task scope. The new leaf has no proof-debt finding. Source and axiom audits pass independently; this does not claim a clean repository-wide lint gate.
