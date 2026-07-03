# R3b + R5 results (2026-07-03) — [MEASURED]

Engines: `computations/mwm/engine2.py` (R3b pencil), `computations/mwm/engine3.py` (R5
complex-c path). Pod: 30 workers, dps 18 (winding = integer certificate); raw outputs
`r3b.out`, `r5.out` here. All boxes returned `ok: true` (no flagged/unresolved contours).

## R3b — FE-minimum replication, window 2 (t ∈ [150,200))

Pre-registered (05-task-board.md): minimum again at the FE fiber k = κ ≈ 0.28408; floor
count = 2 (the window's D–H zeros at t ≈ 167, 177); linear plateau scaling replicates.

Measured (k-scan 0.24–0.33, step 0.005; defect boxes in σ ∈ (σ₀, 1.2)):

| σ₀ | floor | plateau (count = 2) | width | width/(σ₀−½) |
|------|-------|---------------------|-------|--------------|
| 0.53 | 2 | [≤0.24, 0.325] | ≥ 0.085 (left edge beyond scan) | — |
| 0.52 | 2 | [≤0.24, 0.31] | ≥ 0.07 (left edge beyond scan) | — |
| 0.51 | 2 | [0.255, 0.295] | 0.04 | 4.0 |
| 0.505| 2 | [0.27, 0.29] | 0.02 | 4.0 |

**All three pre-registrations CONFIRMED.** Floor = 2 with the defect boxes exactly at
[166,168] and [176,178]; κ lies inside every plateau; width coefficient 4.0 replicates
window 1's 3–4.5. The FE fiber is a regular transversal minimizer in the second window —
the R3 finding is not a window artifact.

## R5 — Euler-approach profile (complex-c path, σ₀ = 0.51, t ∈ [2,200))

Path: c(u) = (1−u)·c_DH + u, c_DH = (1−iκ)/2; u = 0 is Davenport–Heilbronn (FE holds,
no Euler product), u = 1 is pure L(s,χ) (Euler product; expected clean in range).
Pre-registered: count decreases to 0 at u = 1; the SHAPE near u = 1 (linear vanishing vs
threshold) is the observable; any defect surviving to near u = 1 is a major anomaly.

Measured profile (defect count n(u), 21 steps):

```
u:  0.00 0.05 0.10 0.15 0.20 0.25 0.30 0.35 0.40 0.45 0.50
n:     4    4    7   14   22   25   27   28   28   28   28
u:  0.55 0.60 0.65 0.70 0.75 0.80 0.85 0.90 0.95 1.00
n:    27   29   29   28   26   24   19   13    6    0
```

Findings:
1. **CONFIRMED: n(1) = 0 exactly** — no defect survives at the Euler point; anomaly gate
   passed; the family picture stands.
2. **Two-minimizer geometry, computed.** The profile has a local minimum at the FE point
   (n = 4) and its global minimum at the Euler point (n = 0), with a hump (n ≈ 29) in the
   mid-segment where NEITHER constraint holds. Both constraints are defect suppressors;
   the Euler cut is exact (floor 0), the FE cut transversal (floor > 0) — the "Euler cut
   as the second, deeper minimizer" reading, now measured.
3. **Linear flux law near the Euler point.** Over the whole final fifth the decay is
   linear: n ≈ 120·(1−u) (values 24, 19, 13, 6, 0 at steps of 0.05; per-step decrements
   5, 6, 7, 6). Zeros exit the band through the σ = 0.51 wall at an (approximately)
   constant rate in u — linear vanishing, NOT a threshold. [CONJECTURE] the constant ~120
   is a mobility integral of the window's on-line zeros under the perturbation
   (1−u)(L(χ̄)−L(χ)); connects to R3's measured defect velocity dσ/dk ≈ 0.2–0.35.
4. **Euler-resistance order (pinning in the c-plane).** Last survivors before the Euler
   point (u = 0.95): boxes at t ≈ 24, 70, 98, 116, 178, 196 — a concrete "most
   Euler-resistant zeros" ranking, the c-plane analogue of R3c's pinning order.

Opened: R5b (refine u ∈ [0.9, 1] with fine steps + per-zero wall-crossing u*, testing the
linear law and extracting the mobility distribution); cross with R3c pinning order.

## R5b — fine near-Euler scan (u ∈ [0.90, 1.00], step 0.005; σ₀ = 0.51, t ≤ 200)

Pre-registered: linear law n ≈ 120·(1−u) persists; n(0.995) ∈ {0,1,2}; n(1) = 0; crossings
roughly uniform (no staircase clustering). Raw: `r5b.out` (all boxes ok, no flags).

Measured:

```
u:  0.900 0.905 0.910 0.915 0.920 0.925 0.930 0.935 0.940 0.945 0.950
n:     13    11    11    10    10     9     9     8     7     7     6
u:  0.955 0.960 0.965 0.970 0.975 0.980 0.985 0.990 0.995 1.000
n:      6     4     1     1     1     0     0     0     0     0
```

Verdict vs pre-registration: n(0.995) = 0 ✓ (inside the registered set); n(1) = 0 ✓;
the LINEAR LAW HOLDS ONLY TO u ≈ 0.955 (within ±1 of 120(1−u)) and the "uniform
crossings" clause is REFUTED at the tail — wall-crossings cluster in u ∈ [0.955, 0.975]
and then stop entirely.

**Main find — the Euler moat.** For u ∈ [0.980, 1.000] the band σ ∈ (0.51, 1.2), t ≤ 200
is completely defect-free: the Euler point is not the endpoint of a continuous decay but
sits INSIDE an open zero-free basin of the c-pencil, of width ≈ 0.025 along this segment
(at this window/band). Contrast with the FE point: R3/R3b show defects AT the FE fiber
(transversal minimizer, floor > 0). Geometry reading [CONJECTURE]: Euler positivity is an
OPEN condition in the family (a basin), the FE a thin/codimension-one one (a fiber floor).

Euler-resistance ranking (last-seen u* per box): t≈178 (0.975) ≫ t≈70, 98, 116 (0.960) >
t≈24, 196 (0.955) > t≈160 (0.945) > t≈34 (0.935) > t≈8 (0.930) > t≈144 (0.920) >
t≈106 (0.910) > t≈88, 134 (≤0.900). Banked for the R3c pinning cross-check.

Opened: **R5c — moat scaling.** Measure the last-crossing u*_max as a function of window
height (t ≤ 200 / 500 / 1000) and band σ₀. [CONJECTURE] the moat shrinks as T grows
(slowest zeros get slower; u*_max ↑ 1), plausibly like 1 − u*_max ~ c/log T; whether
inf_T (moat width) > 0 at fixed σ₀ is the sharp question — a positive answer would be a
strong (and suspicious — attack it) family-picture statement.
