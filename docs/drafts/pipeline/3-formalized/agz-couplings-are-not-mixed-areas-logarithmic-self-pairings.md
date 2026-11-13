# Realization of a window: the couplings are not mixed areas; the index forces logarithmic self-pairings

- **ID:** agz-realization-self-pairings
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.13 (first question; milestone M1), §2.14; programme `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ` (README question 4)
- **Statement:** Let `(R, R + J]`, `J ≤ R`, be a window and `G_d` the symmetric matrix with the
  neutral part `N(a, b)` off the diagonal and arbitrary self-pairings `d(a)` on it. If `G_d` has at
  most one negative square, then of any two runs of `m` blocks that are at least `m` blocks apart
  one has `Σ d(a) ≥ m log m − 2m`. Hence no completion with `d ≤ 0` has index `≤ 1` once
  `R, J ≥ 24`; and the window's own self-pairings have `Σ N(a, a) ≤ m log m + m/2` on every run of
  `m` blocks of `(3m, 6m]`.

## Goal

§2.13 asks for a configuration with one member per block whose pairing matrix is `−N`, and first:
are the couplings `w(a, b) = −N(a, b)`, `a ≠ b`, of a dyadic window the mixed areas of planar
convex bodies with areas `≥ −N(a, a)`? The theorem answers **no** at every block count `≥ 24`, for
every class of objects with nonnegative self-pairing and the Hodge index inequality (planar convex
bodies with mixed areas, nef classes on a surface, vectors of the closed forward cone). It also
gives the positive law behind the obstruction: the index bounds the self-pairings of a realization
from above by `−(log m − 2)` per block, and the window attains this rate up to `5/2` per block.

Not a proof of any index statement: the index of the true window is an input (ratio `≤ 103/50`),
not an output.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `sum_selfPairing_ge_of_hermNegIndex_le_one`, `two_le_hermNegIndex_neg_of_couplings`, `sum_neutralBlock_self_le`

## Proof

`D(n)` = second difference of `n log n` (`xLogXDiff`), `D(0) = 0`, `0 < D(n) ≤ 2/n`;
`J(a, b) = ½(D(a + b + 1) + D(b − a))` the jet; for `a < b`: `N(a, b) = −J(a, b) − C_Q(a, b)`
with the contact `C_Q ≥ 0`, and `C_Q(a, b) = 0` when `b < 2a`.

**1. Inside a run (exact rate).** For blocks `A, …, A + m − 1` and `j ≠ l`:
`N(A + j, A + l) ≤ −½ D(|j − l|)`. For fixed `j < m`,
`Σ_{l<m} D(|j − l|) = s(j) + s(m − 1 − j)` with `s(n) = (n+1) log(n+1) − n log n`
(telescoping, `Σ_{k ≤ n} D(k) = s(n)`), and `Σ_{j<m} s(j) = m log m`. So

  `Σ_{j≠l<m} N(A + j, A + l) ≤ −m log m`,

with no condition on `A`, `m`, `Q`. For the flat packet `x` of the run:
`G_d(x, x) ≤ Σ_j d(A + j) − m log m`.

**2. Between two runs.** Let `A + 2m ≤ B` and `B + m ≤ 2A`. For `j, l < m` the blocks
`a = A + j`, `b = B + l` have `b − a ≥ m + 1` and `b < 2a`, so `N(a, b) = −J(a, b)` and
`0 < J(a, b) ≤ 2/(b − a) ≤ 2/m`. For the flat packets `x, y` of the two runs:
`−2m ≤ G_d(x, y) ≤ 0`.

**3. The law of two runs.** Window `(R, R + J]`, `J ≤ R`, runs at offsets `p`, `q` with
`p + 2m ≤ q`, `q + m ≤ J`; then `A = R + p`, `B = R + q` satisfy step 2. Suppose both
`Σ d < m log m − 2m`. By step 1, `G_d(x, x) < −2m` and `G_d(y, y) < −2m`; by step 2,
`G_d(x, y)² ≤ 4m² < G_d(x, x) G_d(y, y)`. Two vectors with `G(x, x) < 0` and
`G(x, y)² < G(x, x) G(y, y)` span a negative definite plane, so the index is `≥ 2`
(`two_le_hermNegIndex_of_unbound_pair`). ∎

**4. Constant self-pairing.** `d ≡ c` with index `≤ 1` and `3m ≤ J ≤ R` gives `c ≥ log m − 2`:
the second largest eigenvalue of the matrix of the couplings of a window of `J` blocks is at least
`log⌊J/3⌋ − 2`.

**5. No nonnegative self-pairings.** If `d ≤ 0` and `R, J ≥ 24`: the first `24` blocks form a
principal submatrix (the index does not decrease with `J`), and `m = 8`, `p = 0`, `q = 16` gives
`Σ d ≤ 0 < 8 log 8 − 16` (`log 8 = 3 log 2 > 2`), so the index is `≥ 2`. Matrix form: a symmetric
`M` with `M_{ab} = w(a, b)` off the diagonal and `M_{aa} ≥ 0` has two positive squares.

Planar convex bodies: for bodies `K_a` the mixed area is bilinear on Minkowski sums and
`V(K, L)² ≥ V(K, K) V(L, L)` (Minkowski). With `K = Σ_{run 1} K_a`, `L = Σ_{run 2} K_b` and
`V(K_a, K_b) = w(a, b)` this reads `(Σ w(a, b))² ≥ (Σ areas + Σ_{a≠a'} w)(…) ≥ (m log m)²`,
against `Σ w(a, b) ≤ 2m` (steps 1, 2). The same for nef classes and the Hodge index theorem.
Minkowski's inequality is classical and not formalized; the Lean statement is the matrix form.

**6. The rate is attained.** For `a ≥ 1`: `N(a, a) = ϱ(a) − J(a, a) ≤ ϱ(a) = s(a) − γ − log 2π`
and `s(a) ≤ log(a + 1) + 1`. If `A ≥ 1` and `A + m ≤ 6m`: `log(a + 1) ≤ log 6 + log m` on the run,
`log 6 ≤ log 2π`, `γ > ½`, so `Σ_{j<m} N(A + j, A + j) ≤ m log m + m/2`. The window `(3m, 6m]` is
dyadic, its neutral part is the completion by its own diagonal and has index `≤ 1`
(`hermNegIndex_neutralWindow_le_one`). So the bound of step 3 cannot be raised above
`m log m + m/2`.

## No-go closure
- **Exact killing mechanism:** Minkowski's inequality for the Minkowski sums of two far runs:
  inside a run the couplings sum to `≥ m log m`, between the runs to `≤ 2m`.
- **Strongest positive survivor:** the law of two runs (step 3) with its attained rate (step 6):
  in every realization with the Hodge index inequality the self-pairings are `≤ −(log m − 2)` per
  block on one of any two far runs; the window itself has `≥ −(log m + ½)`.
- **New insight:** the logarithmic density `ϱ(a) ≈ log a` on the diagonal of `N` is forced, up to a
  bounded amount per block, by the jets and the index alone. A realization must consist of
  classes of negative self-pairing of logarithmic depth in the number of blocks (curves outside
  the nef cone), not of convex bodies.
- **Status:** paper proof dependency-closed (steps 1–6); formalized, see "Lean".

## Lean

Module `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean`
(wired into the umbrella `AbsoluteGeometryOfSpecZ.lean`).

| Step | Declaration |
|---|---|
| completion `G_d`, flat packet of a run | `neutralWithDiagonal`, `blockRun`, `bilin_windowMatrix_blockRun` |
| 1 | `neutralBlock_le_neg_xLogXDiff`, `sum_sum_xLogXDiff_max_sub_min`, `sum_neutralWithDiagonal_run_le` |
| 2 | `neg_two_div_le_neutralBlock`, `abs_sum_neutralWithDiagonal_runs_le` |
| 3 | `sum_selfPairing_ge_of_hermNegIndex_le_one` |
| 4 | `log_sub_two_le_of_hermNegIndex_le_one` |
| 5 | `two_le_hermNegIndex_of_selfPairing_nonpos`, `two_le_hermNegIndex_neg_of_couplings` (matrix form) |
| 6 | `neutralBlock_self_le`, `sum_neutralBlock_self_le`, `hermNegIndex_neutralWithDiagonal_self_le_one` |

## What stays open
- A realization of the dyadic windows by curves (M1): which surface, and which classes of
  self-pairing `−N(a, a)`.
- The sharp constant: estimate (not proved) `W − W' ≈ m log m − 0.25m` for the end thirds against
  the true `Σ N(a, a) ≈ m log m − 0.17m` on the lower third of `(3m, 6m]`.
- Windows with contacts (`J > R`) between the two runs: step 2 needs the contact of `2`.

## Log
- 2026-11-13 — created in 1-in-progress with the paper proof.
- 2026-11-13 — formalized; the module compiles with `lake --old env lean`; moved to 3-formalized.
