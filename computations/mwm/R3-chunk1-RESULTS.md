# R3 chunk 1 — pencil deformation through the FE fiber (2026-07-03)

Engine: engine2.py `pencil` (30 workers, dps 18). Family: f_k = (1−ik)/2·L(s,χ) + (1+ik)/2·L(s,χ̄),
χ mod 5 with χ(2)=i — real Dirichlet coefficients [1, k, −k, −1, 0] for every k; the functional
equation holds exactly at k = κ = (√(10−2√5)−2)/(√5−1) ≈ 0.28408 (the Davenport–Heilbronn point).
Window: t ∈ [84, 118), boxes σ ∈ (0.51, 1.2) of height 2; k ∈ [0, 0.57] in 13 steps (step 0.0475;
k = 0.285 is the closest grid point to κ). Raw: pod /root/mwm/pencil-k-084-118.out.

## Pre-registered vs observed

Pre-registered (03-computation-campaign.md §R3): defects move continuously, collide (winding 2) at
isolated parameters, charge mod 2 conserved between collisions. NOT pre-registered: any special
behavior of the defect COUNT at the FE fiber.

Observed off-line zero count in the window (sum of windings over defect boxes):

| k | 0.000 | 0.048 | 0.095 | 0.143 | 0.190 | 0.238 | **0.285≈κ** | 0.333 | 0.380 | 0.428 | 0.475 | 0.523 | 0.570 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| count | 11 | 11 | 11 | 10 | 9 | 5 | **2** | 9 | 10 | 11 | 11 | 11 | 11 |

1. **Sharp minimum of the off-line defect count exactly at the FE fiber.** The count collapses
   from ~11 to 2 at k ≈ κ and rebounds on both sides. The two survivors are D–H's genuine
   off-line zeros (boxes [84,86) and [114,116) — the banked zero t≈85.699 and its known
   companion). `[FINDING — not pre-registered]`
2. All defects odd (w=1) except transient w=2 boxes (e.g. [116,118) at small k; [96,98) and
   [102,104) at k ≳ 0.38) — pair coalescence/splitting visible exactly as pre-registered;
   no charge anomalies; every winding a clean integer, zero unresolved segments.
3. Defect trajectories move continuously with k (boxes shift by one 2-unit slot per ~0.05 in k).

## Reading (register-marked)

- `[KNOWN-ADJACENT mechanism, post hoc]`: at k = κ the FE + reality pins most zeros ONTO the
  critical line (they leave the σ > 0.51 boxes); away from the FE fiber the line is not
  distinguished and the strip zeros spread. Qualitatively expected once seen.
- `[FINDING]`: the measured curve is the first quantitative **defect-vs-constraint profile** in
  this family: the FE fiber is a sharp local MINIMIZER of off-line defect count — the computed,
  one-constraint-down instance of the banked B7 shape ("ζ is a critical point of the RH-defect
  functional; RH = minimality", door bucket X5 §3). The FE removes ~80% of the window's off-line
  charge; the residual 2 defects are exactly what the missing Euler cut (A) leaves behind.
- Instrument value: "defect count per window as a function of the deformation parameter" is a
  working observable. Next probes: (i) resolve k near κ finely (is the minimum exactly at κ? width?);
  (ii) same profile in a second window (t ∈ [160,180) — two more banked-adjacent defects);
  (iii) does the residual-2 floor persist in ALL windows (it should: those are D–H's zeros).

Verdict line: **lead + encouragement** (family picture's constraint-pinning made measurable);
no early fail.
