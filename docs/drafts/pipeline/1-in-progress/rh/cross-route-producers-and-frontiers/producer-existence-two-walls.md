# Producer existence: the two walls (consolidated map, L313–L357)

- **ID:** producer-existence-two-walls
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (open core) + collected theorems
- **Source:** `hf-positive-hodge-attack/krein-producer-loops.md`, L313–L357 (2026-10-03)
- **Statement:** A producer (an integer-supported, full-cone, Weil-positive `lam` for ζ's datum) exists ⟺ PBAP ⟺ `σ_prod = ½`. Every constructive route found so far meets one of two walls:
  - **(W1)** Dirichlet-class rigidity: Hamburger, Theorem A / C329, L325.
  - **(W2)** low-frequency negativity of the archimedean density, `θ′ < 0` on `|t| < r* ≈ 2π`, which only the full multi-period tiling of `log ℕ` can absorb.

## Goal
Prove PBAP (gives a producer whether or not RH holds; a non-Λ one if RH fails), or show PBAP ⇒ RH (then the producer is Λ and the problem is RH).

## Established (this session)
- `σ_prod ≥ ½`, attained [Lean `RHTower.CarlsonFloor.not_isHalfPlaneProducer_of_lt_half`]. Producers are exactly critical.
- Nonnegative prime-blind tests are Weil-positive [P, L349]. Inputs: Riesz rearrangement, Lévy–Khintchine form of ψ, and window positivity (external: Zhu).
- Dilation-free sets have measure `≤ log 2` [Lean `RHTower.DilationFree.volume_le_log_two_of_dilationFree`].
- Multi-tiling characterization and anti-concentration `sup Φ̂ ≤ (log 2/2π)‖Φ̂‖₁` [P, L350/L354].
- Nyquist identification: the Connes–Consani window is the Nyquist window of the band `A < 0` [P, L350].
- Polar PBAP ⟺ the Poincaré inequality `D(g) ≥ 5.3721‖g‖²` on the prime-blind variety [P, L352].
- Function-field analogue: PBAP holds by total blindness. The ℚ obstruction is (W2) alone [P, L356].
- Kurasov–Sarnak dictionary for atomic producers: `e^{iθ}` is not inner on `|t| < 2π` [P, L357].

## Falsified / dead routes
- C350 folding (L351).
- Frequency splitting (L353): robustness `√R` against gain `log R`.
- Relaxed producers (L344a): a quasi-RH ladder.
- Finite-period tiling (L356): sparse-support theorem.
- Second-moment, ζ-mass and universality kills of anti-Selberg twins (L341–L342).

## Open
- C351: signed positivity on dilation-free sets. Reduced to one two-interval family, with a hand-estimated margin of about 0.08.
- Overlapping-support cancellation. Needs coherence of the prime-weighted defects (explicit formula of the high part).
- Detection: rigidity of the zero sequence modulo the periods `2π/log n` (L354).
- C329: decisive Gram-twin coefficient test queued (needs a runpod go-ahead).

## Gates
- [x] 0 → 1
- [ ] 1 → 2

## Log
- 2026-10-03 — created as a consolidated map.
