# The odd-window strip-Harnack route to Weil positivity

- **ID:** aip-odd-window-strip-harnack-route
- **Stage:** 5-failed
- **Type:** FALSIFIED (as a route to RH; the proved windows stand as theorems)
- **Source:** AIP card `1-in-progress/arithmetic-incidence-positivity-2026-10-20.md`, contributions C11–C25, C27, C28
- **Statement:** prove `J_M(u) + V_μ(u) ≥ 0` (positivity of the zero form on odd tests) on growing support windows by
  folding the archimedean surplus and paying each prime atom from the surplus of its own reflection strip.

## Goal
RH ⟺ positivity of the odd zero form at every support (`riemannHypothesis_iff_forall_odd_fullZeroForm_nonneg`). The route
aimed at pushing the proved window upward, with the prime atoms paid strip by strip through their odd parts.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  — not applicable: the route cannot reach the RH target (see no-go closure)

## Approach
Exact fold of the jump form (killing + surplus), ground-state transform with polynomial gauges, Schur lending, and for
each atom `n` a micro-fold of `S_n × S_n` paying `2Λ(n)/√n ∫ α²_n` (sharp, wide, harmonic folds), with the even part
of each atom kept as a gain.

## No-go closure
- **Exact killing theorem/mechanism:**
  - single atom near `log 2`: `not_forall_oddPart_le_stripSurplus_logTwo` (`FirstPrimeOddPartPaymentWall`) — on
    `[p, log 2 − p]`, `0 < p ≤ 1/400`, no fold of `S₂ × S₂` bounding the odd part alone pays the atom of 2 (linear
    profile, quotient ≤ `12 − 16 log 2 + a²/24 + a³/15 ≈ 0.952 < √2 log 2`);
  - many atoms at large `r` (sibling contributions): `exists_edgeTent_oddPart_sharing_fails`,
    `stripBoxEnergy_edgeTent_lt_sum_oddPart` — the surplus is a logarithmic energy and pays the odd parts only in the
    light cone `η ≲ e^{−r}`;
  - finiteness: each window involves finitely many atoms; no uniform mechanism carries a window to the next.
- **Strongest positive survivor:**
  - odd-form positivity on `[−181/500, 181/500]`, `Ẑ ≥ (1/1000)∫F²` (`SchurLendingOddWindowThreeHundredSixtyTwoThousandths`);
  - selectivity: `ζ(s−a)ζ(s+a)` fails at support `13/125` (`ShiftedPairHankelSelectivity`);
  - Harnack across prime shifts: every prime power on its own strip to `½ log n + 1/12` (`SharpMicroFoldHarnack`), even
    parts kept (`PrimePowerEvenPartHarnack`), the whole prime side for `r = 23/40` (`OverlappingPrimeStripsTwentyThreeFortieths`);
  - the exact quotient bound of the linear profile and the regional-eigenvalue decomposition `2 − 6J`, `J = (8 log 2 − 5)/3`.
- **New insight:** odd-part payment from strip surplus is bounded both locally (first atom, before `log 2`) and globally
  (thin band at large `r`). Any allocation must use the cancellation of odd against even parts across atoms — the
  global incidence allocation condition, which is equivalent to RH (`riemannHypothesis_iff_globalIncidenceAllocation`,
  sibling C26). The route therefore reduces RH to an RH-equivalent statement and supplies no independent premise.
- **Status:** all cited theorems are in Lean, axioms `propext, Classical.choice, Quot.sound`, wired into the
  `ArithmeticIncidencePositivity` umbrella. Hand estimates (not formalized): linear-profile quotient crosses `√2 log 2`
  near `r ≈ 0.68`; separable payment of 2 and 3 fails near `0.665`; the harmonic fold with a linear gauge reaches
  `≈ 0.58–0.59`.

## Log
- 2026-10-21 — created in 5-failed when the odd-window support lane was closed at user request.
