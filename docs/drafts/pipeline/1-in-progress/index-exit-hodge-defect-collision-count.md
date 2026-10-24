# The index exit: an independent count for the Hodge defect (opening C)

- **ID:** index-exit-hodge-defect-collision-count
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for the exact laws; CONJECTURE for the forcing step
- **Source:** `docs/reports/review-2410/fable.md` §2.3 C
- **Statement:** The Hodge defect of the scaling surface (the number of zeros right of the line)
  has a second, independent formula as a count: half the right limit at heat `0⁺` of the
  nonreal-zero count of the de Bruijn–Newman flow, which is the total mass of the collisions of
  the flow; each collision at a real zero of multiplicity `m` carries exactly `2⌊m/2⌋` units.

## Goal
Realise the opening literally: an integer `h` that is a count, `h ≥ 0` by construction, and an
exact identity `h = (Hodge defect) + (explicit nonnegative term)`; prove the first rung (a fixed
bound on the count) in receiver coordinates; prove the quantization of the index.

Correction to the review. "A count that bounds the defect by a fixed integer" gives finiteness of
the right zeros, which is RH above a finite height (`FiniteOffLine`); this implies quasi-RH but is
far stronger than it, so the first rung of the index exit is not at quasi-RH strength.

The logical form in the review (`h ≥ 0`, `h = D + N` with `N ≥ 0`) does not force `D = 0`; what
forces it is an upper bound `h < first quantum` computed independently of the zeros. The laws
below make every term exact; the upper bound is the open core.

## Gates
- [x] 0 → 1  in-progress: well-posed, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Plan
1. `RHTower/DeBruijnCollisionJumpLaw.lean`: backward local zero count at a real zero of order `m`
   (exactly `m mod 2` real zeros nearby just before), the exact jump of the nonreal count
   `N(t⁻) − N(t) = Σ_{x real} 2⌊m_t(x)/2⌋`, and the global law `N(t) = Σ_{s>t}` (collision mass).
2. `ArithmeticOrientationGeometry/TheIndexExit.lean`: the index of `ζ` in four coordinates
   (Hodge defect, off-line copies, heat count, collision charge, eventual line) — first-rung TFAE;
   the identity `lim N = 2(D + E)` with `E` the multiplicity excess; quasi-RH and the short-window
   power savings from a bounded index; parity of the Hodge defect and `RH ⇔ D < 2`.

## Status
- Corpus survey done: Pontryagin law (`zeta_hodgeDefect_iff`), collision charge endpoint, KKL
  finiteness, antitone count, right limit, collision criterion, backward/forward local models.

## Log
- 2026-10-24 — created.
