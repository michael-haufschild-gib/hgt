# Prime-log height bound

- **ID:** prime-log-height-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/zero-estimate-uniformity.md` part (b), and reused by
  `../2-fully-proven/friable-dirichlet-auxiliary.md`.
- **Statement:** For every nonzero finite integer prime-exponent vector `m`, the prime-log frequency obeys
  the S-free lower bound `H(m)^-1 <= |sum_p m_p log p|`, where `H(m)=prod_p p^|m_p|`.

## Goal

This banks the exact Lean-formalized height core used by the diagonal zero-estimate card. It does not claim
the Vandermonde determinant product estimate, the Bohr-polynomial/support wrapper, the PNT/Rosser-Schoenfeld
conversion `P_S -> |S|`, or the fixed-degree canonical-exhaustion uniformity bookkeeping.

## Paper Proof

Write `m=m_+-m_-` with nonnegative finite prime-exponent vectors. Set
`a=prod_{m_p>0} p^{m_p}` and `b=prod_{m_p<0} p^{-m_p}`. Then
`sum_p m_p log p = log a - log b = log(a/b)`.

If this frequency were zero, then `a=b`, so unique factorization would give `m_+=m_-` and hence `m=0`,
contrary to hypothesis. Thus `a != b`. If `a>b`, then
`log(a/b) >= 1/(ab)` by the elementary estimate `1-x^-1 <= log x` applied to `x=a/b`; if `b>a`, the same
argument applies to `b/a` and absolute values. Since `H(m)=ab`, this gives
`H(m)^-1 <= |sum_p m_p log p|`.

## Gates

- [x] 0 -> 1  in-progress: exact S-free height inequality extracted from the broader zero-estimate card.
- [x] 1 -> 2  fully-proven: paper proof above by unique factorization and the elementary logarithm estimate.
- [x] 2 -> 3  formalized: Lean definitions/theorems `primeLogHeight`,
  `logPrime_int_sum_eq_log_pos_sub_log_neg`, and `logPrime_height_bound` in
  `formal/GaloisForLFunctions/RHTower/ZeroEstimate.lean`; names checked by scratch file; `#print axioms` uses only
  the allowed standard subset `[propext, Classical.choice, Quot.sound]`; `lake build` green;
  `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the size-bound lemma inside the G2 zero-estimate note.

## Door Passport

Door-2 strips this to unique factorization plus an elementary real-log inequality, so it is BRIDGE. Its value
is as the Lean-certified S-free height input for the zero-estimate pillar.

## Log

- 2026-06-19 - Leaner split this exact height-bound lemma from `zero-estimate-uniformity`. The parent card
  remains in `2-fully-proven` because the determinant product size estimate, Bohr support wrapper, and
  canonical-exhaustion/PNT uniformity bookkeeping are not fully Lean-formalized.
