# Finite prime-log annihilator

- **ID:** finite-prime-log-annihilator
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/holonomicity-limit-nonclosure.md` §1/§5 and `../2-fully-proven/corank-seam-invariant.md` §A
- **Statement:** The finite-support diagonal relation lattice for the arithmetic prime-log frequencies is trivial, and every finite prime slice of the annihilator is `{0}`.

## Goal
This banks the exact finite relation-lattice floor for the arithmetic module `M_zeta`: no nonzero finitely supported integer character annihilates the prime-log diagonal. It does not formalize the directed-sup corank identity, G3 holonomicity implication, C7 non-reconstruction, or the graded-corank/Schanuel realization layer.

## Paper Proof
Let `m` be a finitely supported integer vector on the primes and suppose
`sum_p m_p log p = 0`. Split `m` into positive and negative parts. Then
`sum_{m_p>0} m_p log p = sum_{m_p<0} (-m_p) log p`; exponentiating gives equality of the two positive
integers `prod_{m_p>0} p^{m_p}` and `prod_{m_p<0} p^{-m_p}`. Unique factorization forces every exponent
to be zero, hence `m=0`. Adding the condition `support(m) subset S` for a finite `S` does not change the
argument, so the finite annihilator is also `{0}`.

## Gates
- [x] 0 -> 1  in-progress: exact finite relation-lattice statement extracted from the corank and holonomicity-limit cards.
- [x] 1 -> 2  fully-proven: paper proof above, using unique factorization / log-prime linear independence.
- [x] 2 -> 3  formalized: Lean theorems `logPrime_diagonalResonant_eq_zero`, `primeLog_diagonalRelationLattice_eq_singleton`, and `finitePrimeLogAnnihilator_eq_singleton` in `formal/GaloisForLFunctions/HTGeometry/Resonance.lean`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the formal finite-annihilator certificate for the corank tower notes.

## Log
- 2026-06-19 — Leaner split this exact relation-lattice floor from `holonomicity-limit-nonclosure` and `corank-seam-invariant`. The parent cards remain in `2-fully-proven` because their directed-limit, holonomicity, and realization claims are not fully Lean-formalized.

