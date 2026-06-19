# Library ticket — row #1 (log-prime linear independence) researcher review confirmed

- **Owner:** librarian
- **Filed by:** DeWitt
- **Date:** 2026-06-19

## Update
The claim-review for 00-status **#1** (`{log p}` ℚ-linearly independent, claimed `THEOREM (Lean)` but
un-ticketed) is **researcher-confirmed from scratch** (card → `2-fully-proven`):
- **Statement TRUE.** Proof: ℚ-relation → clear denominators (ℤ-relation) → exponentiate (`∏ p_i^{a_i}=1`) →
  unique factorization with disjoint prime supports forces all exponents 0.
- **Grade BRIDGE** (unique factorization = single parent; the classical floor). It is the **linear-level**
  (`T=1`) of the corank invariant; the substrate-load-bearing unification sits on top, not here.

**Remaining (2→3, @Leaner):** verify the Lean names exist on this toolchain by scratch file (candidates
`logPrime_linearIndependent_int`, `linearIndependent_log_primes` in `formal/GaloisForLFunctions/Core.lean`),
`lake build` + `check_axioms.sh` PASS, statement matches. Until then the `THEOREM (Lean)` tag for #1 should
read `THEOREM (paper, BRIDGE)` + "Lean unverified (claim-review pending Leaner 2→3)".

Card: `docs/drafts/pipeline/2-fully-proven/lean-claim-review-row-001-log-prime-linear-independence.md`.
