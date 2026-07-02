# rho-curve reconnaissance — results (task #30, 2026-07-02)

Scripts: scan.py (ring verdict map), band_probe.py (modulus-3 band), lens_probe.py (dead route),
square_probe.py (the instrument), lobe_probe.py (lobe identification), grid_design.py (grid data).

## Findings

1. **Sharp one-step viability (upgrades #37 to trivial).** D(0,1) ↦ D(b,1) has min modulus
   ‖b‖−1 > xStar(‖b‖) ⟺ ‖b‖ > 2+√2 — so K_b ∩ D̄ = ∅ for ALL directions above the sharp
   threshold, and with the P1 obstruction at −(2+√2): **ρ(π) = 2+√2 exactly, two-sided.**

2. **The obstructed set in the ring 2 < ‖b‖ ≤ 2+√2 is multi-lobed:**
   - P1 lobe around arg π (fixed-point pattern, condition |s−3||s+1| ≤ 4 in s-coords, s²=1−4b);
   - a mid-angle lobe (arg ≈ 75°–130°, radii ≈ 2.0–2.5) driven by PERIOD-3 patterns and deeper
     preimages (beam witnesses at modulus < 1; e.g. (2.2, 90°) beam=0.9823, genuinely obstructed
     — square-tree rightly fails there). P1/P2 do NOT fire in this lobe.
   - [CONJECTURE] complement of the viability set 𝒱 = {b : K_b ∩ D̄(0,1) = ∅} in the Cantor
     regime is the union of preperiodic pattern regions (density of preperiodic points).

3. **Positive ray viable to the inner edge**: square-tree certificates at b = 2.001 (36 leaves).
   Empirically ρ(0) = 2.

4. **Modulus-3 slice**: viable (square-tree) through 155.5° (272 leaves, chain depth 6);
   P1 crosses 1 at ≈ 155.7°; rational-s obstructed point found at arg 155.94°.
   **Bracket target: [155.5°, 155.94°] — under half a degree.**

5. **Instrument = square subdivision** (exact splits, zero inflation, outside-unit pruning,
   leaf = enclosing disk D(c, h√2) + plain chain past xStar). Certificate sizes at modulus 3:
   22–272 leaves, chain depth ≤ 6, split depth ≤ 11; dyadic-exact square data; rounded rational
   chain data re-verified exactly (3-digit numerators). LENS-CLIP CHAINS ARE A DEAD ROUTE
   (single enclosing disk of the lens loses too much; certifies only near the sharp threshold).

## Grid design for the slice (feeds #34/#35)

Obstructed (rational-s trick, b = (1−s²)/4, P1 check |s−3|²|s+1)|² ≤ 16 exact):
  s = 7/2 − 11/16 i  → b = −2759/1024 + 77/64 i   (arg 155.94°, |b|² = 8.707, P1² = 14.98)
  s = 57/16 − 9/16 i → b = −91/32 + 513/512 i     (arg 160.59°)
  s = 57/16 − 7/16 i → b = −23/8 + 399/512 i      (arg 164.83°)
  s = 57/16 − 5/16 i → b = −371/128 + 285/512 i   (arg 169.13°)
  s = 29/8 − 1/8 i   → b = −97/32 + 29/128 i      (arg 175.73°)
  s = 29/8           → b = −777/256               (arg 180°)

Viable (Gaussian-rational b near modulus 3; square-tree certs, rounded rational chains):
  args ≈ 0°, 60°, 90°, 120°, 140°, 150°, 153°, 155°, 155.5° — pick simple rationals per angle
  (e.g. b = −13/5 + 3/2 i at 150.02°, 82 leaves); the 155–155.5° points are the bracket side
  (choose after re-running square_probe at the exact rational parameters).

Certificate encodings for Lean (#32): leaf squares are exact dyadics from halving (0,0,1);
chain steps carry (rounded Gaussian-rational centers, rational radii, rational norm bounds
N_i ≥ ‖c_i‖, drift bounds D ≥ ‖exact−rounded‖, final M ≤ ‖c_last‖ and X ≥ xStar(‖b‖) via
S² ≥ 1+4·Nb, Nb ≥ ‖b‖). All checks are rational-arithmetic (norm_num-shaped).
