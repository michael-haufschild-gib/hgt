# WP3 aperture-face contribution loop (ACT, APT, OWU)

- **ID:** wp3-aperture-1020
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** docs/reports/work-packages.md §WP3
- **Statement:** Prove `μ(A) ≥ 0` for all profiles at apertures beyond the present one, and pass from
  the critical factorial family to the compact receiver tests without the archimedean gain `log M`.

## Goal
100 significant contributions in the sense of WP3: aperture increase for all profiles; compact
critical approximants with truncation-stable, `log M`-free margin; complete payment of the odd sector
(reflected prime, cosh pole, negative sinh moment) at a stated aperture class; a realization theorem
naming Hilbert space and Schatten class of the prime modification; selectivity against
`ζ(s−a)ζ(s+a)`.

## Gates
- [x] 0 → 1  in-progress: loop started 2026-10-20
- [ ] 1 → 2  per contribution
- [ ] 2 → 3  per contribution (Lean module, `lake env lean` audit, axioms standard, lint)

## Rules in force
Unconditional Lean statements only; one foreground Lean process; `lake env lean` audit and
`lake --old env lean -j 1 -o … -i …` for oleans; wire modules into umbrellas; no full or umbrella
builds; no numerical experiments; corpus search tool first; READMEs are mathematics only.
Knowledge ledger: `logs/wp3-aperture-face-knowledge.md`.

## Starting frontier (2026-10-20)
- Full zero form on all profiles: `Ẑ ≥ (1/30)∫F²` on `[−21/200, 21/200]` (ACT C27/C32), limited by
  the Z-type threshold `log ρ ≈ 0.2812` of the density `ω − 2cosh(t/2)` and crude constants.
- Pole-vanishing tests: corpus certificate `μ₀ ≥ 1/20` through `(log 2 + 1/50)/2`.
- APT: compact doubly collared critical sources positive on high blocks (C20–C22), margin from
  `log M`.

## Conjecture queue
1. Markov window past the plastic threshold (absorb the negative density on `(t₀, 2R]`): aperture
   `29/200`.
2. Curved even gauges (ground-state transform with `M = 1 − β x²/R²`): aperture ≈ 0.18–0.2.
3. Odd sector folded Z-type form; pointwise potential `A₀ + Ω(R−s) + 2Ω(s) − Ω(R+s)` minimal near
   `s = R/φ`; odd aperture ≈ 0.29; then past `log 2/2` with the reflected prime 2 paid by the edge
   killing (criterion 3).
4. APT: `log M`-free margin from the sign of the critical prime channel plus low-band exclusion.

## Contribution ledger (append-only)
- **C1 · Markov window past the plastic threshold: all-profile aperture 21/200 → 29/200** —
  `ArithmeticCriticalityTheory/MarkovWindowPastPlasticThreshold.lean` (compiled, olean, standard
  axioms, wired, lint clean for this module). `two_mul_cosh_le_archLevyDensity_of_le_plastic`
  (`ω ≥ 2cosh(t/2)` on `(0, 0.28]` via `a⁴ + a⁶ ≥ 1`, `a = e^{−t/2}`),
  `two_mul_cosh_sub_archLevyDensity_le` (negative density ≤ 0.07 on `(0, 0.292]`),
  `gaugeJumpProfile_le_four_mul_integral_sq`, sharp constants `log π < 1.1449`, `γ + log π < 1.722116`.
  Capstones `fullZeroForm_ge_of_support_le_pastPlastic` (`Ẑ(F) ≥ (1/125)∫F²` on `[−29/200, 29/200]`),
  `zetaZeroConfig_re_W_ge_of_support_le_pastPlastic`, `one_div_125_le_ccmRestrictedWeilGroundEnergy`
  (`μ(A) ≥ 1/125` for `A ≤ 29/200`), `lt_of_ccmRestrictedWeilGroundEnergy_nonpos_pastPlastic` (contact
  apertures exceed `29/200`). Criterion 1. Insight: the Z-type threshold `log ρ` is not a barrier for
  the aperture; the negative pole-minus-Lévy density beyond it is small and is paid by the potential.
  The binding constraint is the centre value of the window potential (exact limit ≈ 0.1526).
  Selectivity: archimedean (prime-free window); the same argument holds for `ζ(s−a)ζ(s+a)` at small
  `a` with modified constants — nonselective, as every prime-free window statement.

## Log
- 2026-10-20 — loop started; frontier read (ACT/APT READMEs, ACT/APT ledgers, frontier map).
- 2026-10-20 — overlap: another agent (WP1/AIP) is building the odd-sector folded plateau result
  `AIP/OddPlateauFoldedWindowPositivity` (`[−7/25, 7/25]`, golden point); WP3 leaves the odd sector to
  it and works on the even sector (the all-profile bottleneck), APT criterion 2 and realization.
