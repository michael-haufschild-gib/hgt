# Exponential-sum order bound

- **ID:** exponential-sum-order-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/zero-estimate-uniformity.md` part (a)
- **Statement:** A nonzero finite exponential sum with `n` distinct frequencies has a nonzero derivative of order `< n` at every base point.

## Goal
This banks the exact Lean-formalized vanishing-order core used by the diagonal zero-estimate card. It does not claim the Bohr-polynomial support wrapper, determinant size estimate, or fixed-degree polynomial uniformity along the canonical prime exhaustion.

## Paper Proof
Let `F(s)=sum_j c_j exp(s mu_j)` with the `mu_j` distinct and not all `c_j` zero. Fix `s0` and set
`c0_j = c_j exp(s0 mu_j)`. Since `exp(s0 mu_j) != 0`, the vector `c0` is still nonzero.

If all derivatives `F^(k)(s0)` vanished for `k=0,...,n-1`, then
`sum_j c0_j mu_j^k = 0` for `k=0,...,n-1`. This is a Vandermonde system at distinct nodes `mu_j`, hence all
`c0_j=0`, contradiction. Therefore some derivative of order `< n` is nonzero at `s0`.

## Gates
- [x] 0 -> 1  in-progress: exact finite exponential-sum order statement extracted from the broader zero-estimate card.
- [x] 1 -> 2  fully-proven: paper proof above, using the Vandermonde initial-moment argument.
- [x] 2 -> 3  formalized: Lean theorem `exponentialSum_has_nonzero_iteratedDeriv_lt_card` in `formal/GaloisForLFunctions/RHTower/ZeroEstimateOrder.lean`; name checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the order-bound lemma inside the G2 zero-estimate note.

## Log
- 2026-06-19 — Leaner split this exact order-bound lemma from `zero-estimate-uniformity`. The parent card remains in `2-fully-proven` because its Bohr-polynomial/support wrapper, determinant product size estimate, and PNT bookkeeping are not fully Lean-formalized.

