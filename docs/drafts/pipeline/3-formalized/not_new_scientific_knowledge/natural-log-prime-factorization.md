# Natural logarithm prime factorization

- **ID:** natural-log-prime-factorization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/corank-transcendence-continuation-bridge.md` §2
- **Statement:** For every nonzero natural number `n`, `log n` is the finite sum of its prime factorization exponents times the corresponding prime logarithms.

## Goal
This banks the elementary feeding identity used to express Stieltjes-block terms through the prime-log generators. It does not formalize Lindemann-Weierstrass, transcendence-degree infrastructure, continuation fields, or the corank-transcendence identity.

## Paper Proof
Write the unique prime factorization `n=prod_p p^{v_p(n)}`. Taking the logarithm of the finite product gives
`log n = sum_p log(p^{v_p(n)}) = sum_p v_p(n) log p`, with only finitely many nonzero exponents.

## Gates
- [x] 0 -> 1  in-progress: exact prime-log feeding identity extracted from the continuation block card.
- [x] 1 -> 2  fully-proven: paper proof above, using unique factorization and logarithm of a finite product.
- [x] 2 -> 3  formalized: Lean theorem `log_nat_eq_sum_factorization` in `formal/GaloisForLFunctions/RHTower/SmoothNumbers.lean`; name checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the finite prime-log feeding lemma in the continuation/transcendence note.

## Log
- 2026-06-19 — Leaner split this exact feeding identity from `corank-transcendence-continuation-bridge`. The parent card remains in `2-fully-proven` because Lindemann/transcendence-degree/corank infrastructure is not fully Lean-formalized.

