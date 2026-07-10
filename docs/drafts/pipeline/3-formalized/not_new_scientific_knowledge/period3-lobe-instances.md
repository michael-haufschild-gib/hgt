# The obstructed set is multi-lobed: period-3 parameterization + mid-angle instances

- **ID:** period3-lobe-instances
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) + [CONJECTURE tail] - grade **BRIDGE**
- **Source:** the mid-angle lobe of the critical-curve program (`critical-curve-slice`); the
  general preperiodic-entry theorem generalizing the P1/P2 patterns.
- **Statement:** The parameter-plane obstructed set `𝒪 = {b : K_b ∩ D̄(0,1) ≠ ∅}` carries
  obstruction structure away from the fixed-point (P1) lobe at `arg b = π`: a genuine period-3
  obstruction at `arg b ≈ 111.8°` and a 2-cycle obstruction inside the window ring
  `2 < ‖b‖ ≤ 2+√2` at `arg b ≈ 126.9°`, with a radial bracket of `∂𝒱` across that ray.

## The new object: exact period-3 parameterization

Derived (Lagrange resolvent on the cyclic order-3 automorphism, NOT a literature formula) and
machine-verified in sympy: a 3-cycle of `z² + b` with trace `σ = γ₀+γ₁+γ₂` exists iff
  **b = −(σ² + σ + 2)**,
the cycle points being the roots of `Q(z) = z³ − σz² − (σ²+2σ+3)z + (σ³+2σ²+3σ+1)`
(verified `f_b³ ≡ 0 (mod Q)`, `gcd(f_b−z, Q) = 1`).  The marked-point curve `X₁(3)` is a plane
cubic with a rational singular point at infinity `[1:1:0]`; projecting slope-1 lines gives the
genus-0 parameterization by `t`:
  `r(t) = (t³−2t²+3t−1)/(2t(t−1))`, `b(t) = −(t⁶−2t⁵+4t⁴−8t³+9t²−4t+1)/(4t²(t−1)²)`,
an on-demand generator of exact Gaussian-rational 3-cycles for `t ∈ ℚ(i)`.
(`computations/p3_lobe_recon/`.)

## Lean surface

- `U0ObstructionPatterns.filledJulia_of_preperiodic` — preperiodicity (`f^[k+n] y = f^[k] y`,
  `n ≥ 1`) implies a bounded orbit, hence `y ∈ K_b`.  The structural core: in the Cantor regime
  the only bounded orbits are preperiodic.
- `U0ObstructionPatterns.filledJulia_meets_unit_disk_preperiodic` — the general entry theorem:
  preperiodic `y` with `‖y − b‖ ≤ 1` gives an obstruction witness `√(y−b)` in the disk.
  **Subsumes P1** (`k=1,n=1`) and **P2** (`k=0,n=2`); re-derivations
  `filledJulia_meets_unit_disk_P1_via_prep` / `..._P2_via_prep` certify the subsumption.
- `U0LobeInstances.lobe_obstructed_112` — period-3 at `arg b ≈ 111.8°` (`b = −1/4 + 5i/8`,
  `k=0,n=3`), cycle `−1/4+3i/4 → −3/4+i/4 → 1/4+i/4`.
- `U0LobeInstances.lobe_obstructed_ring_127` — 2-cycle at `arg b ≈ 126.9°`,
  `‖b‖ = 11/5 ∈ (2, 2+√2)` (Pythagorean `γ = −8/5 + 4i/5`, `‖γ+1‖ = 1`).
- `U0LobeInstances.lobe_radial_bracket` — obstructed at `‖b‖ = 11/5`, viable at `‖b‖ = 22/5`,
  colinear ray (`bv = 2·bo`): the radial companion of the angular `critical_curve_bracket`.
- Cards: `FullyProvenNewTargets.lobe_radial_bracket_card`, `lobe_period3_card`.
- Files: `formal/GaloisForLFunctions/U0/U0ObstructionPatterns.lean` (general theorem),
  `U0LobeInstances.lean`.

## Proof shape

General theorem: preperiodicity forces the forward orbit into the finite set `{f^[j] y : j < k+n}`
(strong induction reducing `m` by the period `n` once `m ≥ k`), hence bounded; the entry point is
`x₀ = √(y−b)` with `f(x₀) = y`, and `x₀ ∈ K_b ⇔ y ∈ K_b` (`mem_filledJulia_iff_quadratic_mem`),
`‖x₀‖ ≤ 1 ⇔ ‖y−b‖ ≤ 1`.  Instances discharge the finite periodicity identity and the entry-norm
bound by exact rational arithmetic (`Complex.ext_iff` + `norm_num`).  Viable side of the bracket:
`viable_of_gt_sharp` (every direction above `2+√2`), colinearity is exact (proportional literals).

## Open

- **Deep mid-angle lobe (the located open core).**  Direct 3-cycle entry (`‖γ − b‖ ≤ 1`) forces
  `‖b‖ < 1.6`; the numerically-obstructed ring interior (e.g. `‖b‖ ≈ 2.2`, `arg ≈ 90°`, where
  P1/P2 verified NOT to fire) is obstructed by a **deep preimage** of a 3-cycle.  An exact
  Gaussian-rational deep-preimage certificate there is open (each preimage step needs a square in
  ℚ(i)).  This is the precise obstacle to a fully-rational deep-lobe instance.
- Feeds `[CONJECTURE] ∂𝒪 = closure(pattern regions)` (see `dV-pattern-closure`,
  `1-in-progress`): the mid-angle lobe is a pattern region of period ≥ 3.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (proofs carried directly in Lean)
- [x] 2 → 3  formalized: axiom set `[propext, Classical.choice, Quot.sound]`; build + lint green
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — period-3 parameterization derived + verified; general preperiodic-entry theorem
  (subsuming P1/P2); mid-angle period-3 + ring 2-cycle instances + radial bracket banked.
