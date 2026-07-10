# Local Euler factor q-difference equation

- **ID:** local-euler-factor-q-difference
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/c6-specialization-functors.md` §0/§1 and reused by `../2-fully-proven/multiplier-dichotomy-theorem.md`
- **Statement:** The local Euler factor `f(x)=(1-x)^{-1}` satisfies the first-order dilation equation `f(qx)=((1-x)/(1-qx))*f(x)` away from its poles; in particular, for the prime lane `q=p^{-1}`, each Euler factor satisfies its own first-order `q`-difference equation.

## Goal
This banks the exact per-prime holonomic floor used by the C6 finite-border recovery and multiplier-dichotomy Source-B discussion. It does not formalize Picard-Vessiot theory, the specialization functors, inverse limits, or the G1 non-holonomicity strict-extension theorem.

## Paper Proof
Let `f(x)=(1-x)^{-1}` and assume `x != 1` and `qx != 1`. Then
`(1-qx)f(qx)=1` and `(1-x)f(x)=1`, so `(1-qx)f(qx)=(1-x)f(x)`. Since `1-qx != 0`, divide by `1-qx` to get
`f(qx)=((1-x)/(1-qx))*f(x)`. Substituting `q=p^{-1}` gives the prime-lane form.

## Gates
- [x] 0 -> 1  in-progress: exact one-factor q-difference identity extracted from the C6 finite-border and Source-B multiplier cards.
- [x] 1 -> 2  fully-proven: paper proof above, using only the inverse identity away from the two poles.
- [x] 2 -> 3  formalized: Lean theorems `localEulerFactor_dilation_relation`, `localEulerFactor_q_difference`, and `localEulerFactor_prime_dilation_difference` in `formal/GaloisForLFunctions/MultiQDifference.lean`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the formal local-factor certificate for the finite-border recovery note.

## Log
- 2026-06-19 — Leaner split this exact local Euler-factor identity from `c6-specialization-functors` and `multiplier-dichotomy-theorem`. The parent cards remain in `2-fully-proven` because their functor/PV/category and dichotomy imports are not fully Lean-formalized.

