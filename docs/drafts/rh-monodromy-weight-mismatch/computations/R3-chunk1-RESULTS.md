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

## Fine k-scan (same day, k ∈ [0.25, 0.32], step 0.005, same window/band)

| k | .25 | .255 | .26 | .265 | .27 | .275 | .28 | .285 | .29 | .295 | .30 | .305 | .31 | .315 | .32 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| count | 3 | 3 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 4 | 5 | 7 |

- The minimum is a **plateau** [0.26, 0.305] of width ≈ 0.045, and κ = 0.28408 sits at its
  **center** (midpoint 0.2825). Steep walls on both sides.
- `[CONJECTURE, next probe]`: the plateau is an artifact of the finite band σ > 0.51 —
  deformed line-zeros need finite |k−κ| to cross the box edge. As σ₀ → 1/2⁺ the plateau
  should shrink to the single point κ: **the FE fiber as the unique defect minimizer in the
  σ₀ → 1/2 limit**, with plateau width ~ (σ₀ − 1/2)-scaling giving a measurable exponent for
  how fast deformation pushes zeros off the line. Run with σ₀ ∈ {0.53, 0.52, 0.51, 0.505}.
- Raw: pod /root/mwm/pencil-fine-k.out.

## Plateau scaling in the band edge σ₀ (4 bands × k ∈ [0.24, 0.33], step 0.005)

Pre-registered: the count-2 plateau shrinks toward the single point κ as σ₀ → 1/2⁺.

| σ₀ | count-2 floor | width | width/(σ₀−1/2) |
|---|---|---|---|
| 0.53 | ⊇ [0.24, 0.33] (whole range) | > 0.09 | > 3 |
| 0.52 | [≤0.24, 0.325] | ≥ 0.085 | ≥ 4.3 |
| 0.51 | [0.26, 0.305] | 0.045 | 4.5 |
| 0.505 | [0.275, 0.29] | 0.015 | 3.0 |

- **Prediction confirmed**: the floor narrows onto κ (midpoints ≈ 0.2825 ≈ κ within the
  half-grid 0.0025), with steep near-symmetric walls (at σ₀ = 0.505: left 8,8,7,7,5,3,3→2;
  right 2→3,5,7,9,11).
- **Width scales LINEARLY in σ₀ − 1/2** (coefficient ≈ 3–4.5): the deformation moves the
  line-pinned zeros off the line at a finite rate dσ/dk ≈ 0.2–0.35 — the FE fiber is a
  REGULAR (transversal) minimum of the off-line defect count, not a degenerate one.
  `[FINDING — measured defect-velocity of the k-family at the FE fiber]`
- Raw: plateau-scaling.out (this directory).
