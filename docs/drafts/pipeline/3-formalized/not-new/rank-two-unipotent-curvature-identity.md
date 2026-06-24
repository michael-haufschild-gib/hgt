# Rank-two unipotent curvature identity

- **ID:** rank-two-unipotent-curvature-identity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/cross-prime-curvature-reducibility.md` §1
- **Statement:** For square-zero upper-unipotent matrices `I+aE`, multiplication adds coefficients and the rank-two curvature product has coefficient `bp + sp_bq - bq - sq_bp`.

## Goal
This banks the exact nilpotent matrix computation used by the cross-prime curvature card. It does not formalize semilinear prime actions, Fourier support, the coboundary/trivializability equivalence, or the RH-blind A1/A2 verdict.

## Paper Proof
Work over a commutative ring `R` and set
`U(a) = [[1,a],[0,1]] = I+aE`, where `E^2=0`. Direct multiplication gives
`U(a)U(b) = I+(a+b)E = U(a+b)`.

Therefore
`U(-bq) U(-sq_bp) U(bp) U(sp_bq)`
has coefficient
`-bq - sq_bp + bp + sp_bq = (bp + sp_bq) - (bq + sq_bp)`.
Thus the curvature product is
`U((bp + sp_bq) - (bq + sq_bp))`, which is the displayed discrete-curl coefficient in the parent card.

## Gates
- [x] 0 -> 1  in-progress: square-zero upper-unipotent matrix computation extracted.
- [x] 1 -> 2  fully-proven: paper proof above, by direct multiplication in a commutative ring.
- [x] 2 -> 3  formalized: Lean theorems `upperUnipotentE_mul` and `upperUnipotentE_curvature_eq` in `formal/GaloisForLFunctions/CrossPrimeCurvature.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the algebraic computation inside the curvature-reducibility note.

## Log
- 2026-06-19 — Leaner split this exact nilpotent curvature computation from `cross-prime-curvature-reducibility`. The parent card remains in `2-fully-proven` because its semilinear, Fourier, coboundary, and RH-blind structural layers are not fully Lean-formalized.
