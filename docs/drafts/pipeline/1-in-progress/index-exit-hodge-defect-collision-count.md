# The index exit: an independent count for the Hodge defect (opening C)

- **ID:** index-exit-hodge-defect-collision-count
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for the exact laws; CONJECTURE for the forcing step
- **Source:** `docs/reports/review-2410/fable.md` §2.3 C
- **Statement:** The Hodge defect `D` of the scaling surface (distinct zeros right of the line) has a
  second formula as a count of de Bruijn–Newman collisions: for small `t > 0`,
  `Σ_{s > t} C(s) = 2D + 2E`, `C(s)` the number of nonreal zeros landing on the real axis at time `s`,
  `E = Σ_{Re ρ > ½} (m_ρ − 1) ≥ 0`.

## Goal
Realise the opening: an integer that is a count, nonnegative by construction, with an exact identity
`count = (Hodge defect) + (explicit nonnegative term)`; the first rung (a fixed bound on the count)
in receiver coordinates; the quantization of the index.

Correction to the review: a fixed bound on the defect is RH above a finite height
(`FiniteOffLine`). It implies quasi-RH but is far stronger than it.

The review's logical form (`h ≥ 0`, `h = D + N`, `N ≥ 0`) does not force `D = 0`. What forces it
is an upper bound on the count, computed without the zeros, below the first quantum.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (the exact laws below; the forcing step is open)
- [x] 2 → 3  formalized: both modules compiled with `lake --old env lean`, wired into
  `RHTower.lean` and `ArithmeticOrientationGeometry.lean`
- [ ] 3 → 4  publication-ready

## Results (Lean)
`RHTower/DeBruijnCollisionJumpLaw.lean` (namespace `RHTower.DeBruijn`):
- `exists_nonreal_zeros_backward`, `exists_ball_nonreal_count_backward`: just before `t`, a real
  zero of order `k` of `H_t` has exactly `k − k mod 2` nonreal zeros of `H_s` near it (the roots of
  `P_k = e^{D²}σ^k` are `i√2·(roots of Heₖ)`; conjugate pairing gives the upper bound).
- `exists_left_nonrealZeroCount`: jump law `N(s) = N(t) + collisionMass t` just before `t ≤ 1/8`.
- `exists_collisionMass_eq_zero_near`, `finite_collisionTimes`: collision times are isolated and
  finitely many after any `t > 0`.
- `nonrealZeroCount_eq_sum_collisionMass`, `nonrealZeroCount_eq_collisionMassAfter`: global law.
- `riemannHypothesis_iff_forall_collisionMass_eq_zero`.

`ArithmeticOrientationGeometry/TheIndexExit.lean`:
- `encard_offLineCopies` (`#off-line copies = 2·#right copies`), `card_rightCopies_eq_sum`.
- `eventually_collisionMassAfter_eq`, `eventually_collisionMassAfter_eq_hodgeDefect`: the second
  formula; `tendsto_collisionMassAfter_atTop` when `D = ∞`.
- `index_exit_first_rung_tfae`: `D < ∞` ⇔ `FiniteOffLine` ⇔ bounded `N(t)` ⇔ bounded collision
  mass ⇔ all zeros above a height on the line ⇔ bounded horizontal collision charge.
- `zetaZeroAbscissa_lt_one_of_finite_rightZeros`,
  `moebius_and_prime_powerWindowSaving_of_finite_rightZeros`.
- `even_ncard_rightZeros`, `riemannHypothesis_iff_encard_rightZeros_lt_two`.

## Open core
An upper bound on the collision mass of the flow after `t`, uniform as `t → 0⁺`, obtained without the
zeros. Any fixed bound is the first rung (RH above a height); a bound below `2` is RH. No count of
successor incidences (Bézout seeds, shells, prefix lattice, Witt ghosts) is known to bound `D` or
the collision mass; the opening's arithmetic `h⁰` remains unconstructed.

## Log
- 2026-10-24 — created; corpus survey; collision law and index-exit synthesis formalized.
