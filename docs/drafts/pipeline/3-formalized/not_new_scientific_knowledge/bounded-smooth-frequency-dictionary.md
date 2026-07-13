# Bounded smooth frequency dictionary

- **ID:** bounded-smooth-frequency-dictionary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/friable-dirichlet-auxiliary.md` §1
- **Statement:** Bounded exponent vectors supported on a finite prime set `S` are equivalent to positive integers whose prime factorization is supported in `S` with all exponents bounded by `N`.

## Goal
This banks the finite unique-factorization dictionary behind the friable Dirichlet auxiliary space. It does not formalize Bombieri-Vaaler, zero-estimate uniformity, the `s=1` lower-bound race, or any Schanuel-type obstruction.

## Paper Proof
Map an exponent vector `m` to the prime product `n_m = prod_p p^{m_p}`. Unique factorization gives
`v_p(n_m)=m_p`, so if `m` is supported in `S` and each `m_p<=N`, then `n_m` is a positive `S`-smooth integer
with all exponents bounded by `N`.

Conversely, map a positive integer `n` to its prime-exponent vector `p |-> v_p(n)`. If the factorization of
`n` is supported in `S` and each exponent is at most `N`, then this vector is supported in `S` and bounded by
`N`. The two constructions are inverse by unique factorization.

## Gates
- [x] 0 -> 1  in-progress: exact finite smooth-number dictionary extracted from the friable auxiliary object.
- [x] 1 -> 2  fully-proven: paper proof above, using unique factorization.
- [x] 2 -> 3  formalized: Lean definitions/theorems `boundedExponentVectorEquivSmooth` and `primeProduct_isBoundedSmooth_iff` in `formal/GaloisForLFunctions/RHTower/SmoothNumbers.lean`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the finite support/frequency dictionary for the auxiliary-space note.

## Log
- 2026-06-19 — Leaner split this exact unique-factorization dictionary from `friable-dirichlet-auxiliary`. The parent card remains in `2-fully-proven` because its auxiliary-space race and obstruction-C reduction are not fully Lean-formalized.

