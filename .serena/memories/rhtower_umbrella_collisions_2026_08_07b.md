# Area-umbrella audit, 2026-08-07 (late session)

Ran the final audit the loop's rules ask for (`lake build <area umbrella>`). It found three things that
`lake env lean` cannot see, plus two blockers owned elsewhere.

## MY collision — fixed

`RHTower.Sieve.antitoneOn_rpow_neg` was declared BOTH in my new
`Sieve/PrimeAbscissaSumBound.lean` and in the existing `Sieve/ZetaRealBound.lean`
(theirs: `Icc (a:ℝ) (b:ℝ)` with ℕ endpoints; mine: `Ici (1:ℝ)` — genuinely different statements).
Renamed mine to **`antitoneOn_rpow_neg_Ici`**. Per-module `lake env lean` had passed all along; only the
umbrella catches this. Lesson (third time in this corpus): after adding modules, build the AREA, not just
the files.

**Verification of my own work:** a scratch file importing all 17 modules I added this session elaborates
cleanly, so they are mutually collision-free and collision-free against everything they import.

## A committed duplicate — fixed

`RHTower.integral_Ioc_ofReal_cpow` was declared in both `ZetaUnitIntervalIntegrals.lean`
(`(ha : 0 < a) (hab : a ≤ b)`) and `BurnolSoninDividedShift.lean` (`(hpq : p ≤ q) {z : ℂ}`) — different
lemmas, same name, both files committed and clean. Renamed the `BurnolSoninDividedShift` one to
`integral_Ioc_ofReal_cpow_of_le` (2 occurrences, same file).

## Pre-existing drift, NOT mine

- `RHTower/ZetaCriticalLineNotSquareIntegrable.lean` (committed, clean) used the nonexistent
  `Complex.log_ofReal_of_pos`; I replaced it with `← Complex.ofReal_log hpos.le, Real.log_exp`. Three
  further `rw` pattern failures remain in that file (lines ~123, 146, 163) — genuine simp/rw normal-form
  drift in someone else's proof. Left for its owner; the RHTower umbrella cannot go green until they are
  fixed.
- `HTGeometry/SegreDiagonalRing.lean` is modified in the working tree by another session and currently
  fails (`typeclass instance problem is stuck`), so the HTGeometry umbrella is blocked there.

## Standing lesson

Both area umbrellas are currently red for reasons unrelated to new work. Verify new modules with a
synthetic all-imports file plus per-module `lake build`; treat the umbrella as a shared resource whose
state depends on every session.
