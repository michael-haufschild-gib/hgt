# The sign index of the heated slice is quantized and antitone in the heat

- **ID:** heated-slice-sign-index
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/wd-la-sign-producer-loop-2026-10-25.md`, row 27
- **Statement:** Let `V_t(λ)` be the number of strict sign changes of `n ↦ T_{2n}(λ, 0, t)`.
  For `0 ≤ λ ≤ λ'`, `V_t(λ') ≤ V_t(λ)`. There is `C > 0` such that for `0 < λ ≤ 1`, `V_t(λ)` is
  even and at most `⌈C/λ⌉`, and `V_t(λ) = 0` iff every heated coefficient `T_n(λ, 0, t)` is `≥ 0`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 `RHTower/XiSliceHeatSignIndex`, standard axioms, wired into `RHTower.lean`
- [ ] 3 → 4

## Paper proof
With `a_n = (2n)! T_{2n}` the heat shift is `a_n(λ') = Σ_j c^j/j! · a_{n+j}(λ)`, `c = (λ'−λ)/2`,
absolutely convergent (domination by the central height). This is `e^{cS}`, `S` the left shift,
the pointwise limit of `(1 + (c/N)S)^N`. One step `f_n + ε f_{n+1}` (`ε ≥ 0`) creates no strict
sign change: a nonzero value has the strict sign of `f_n` or `f_{n+1}`, and the chosen witnesses
increase strictly. Strict alternation persists under pointwise limits. Positive rescaling preserves
sign changes. `T_0(λ, 0, t) > 0` for `λ > 0` and `T_{2n} > 0` for `n ≥ C/λ` (order-uniform
positivity) give the range bound and let an odd chain be extended at its negative end.

## Lean
`HasSignChanges`, `hasSignChanges_of_bidiag`, `hasSignChanges_of_expShift`,
`hasSignChanges_xiSliceHeat_of_le`, `le_of_hasSignChanges_of_pos`, `hasSignChanges_succ_of_odd`,
`exists_xiSliceHeat_signIndex_bounds`, `not_hasSignChanges_one_iff`.

## Position
The LA endpoint at `(λ, t)` is `V_t(λ) = 0`, and quantization makes `V_t(λ) < 2` sufficient. The
only finite source bound is `⌈C/λ⌉`, which diverges as `λ → 0`. The moment kernel is totally
positive, so `V_t(λ)` is also bounded by the sign changes of the fibre transform, but those number
about `(t/π) log(t/2π)`.

## Log
- 2026-10-25 — proved and formalized.
