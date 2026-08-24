# Source-normal extension cocycle canonicality

- **ID:** RH-SOURCE-NORMAL-COCYCLE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** BV--Wold source gauge plus extension-cocycle parent theory
- **Statement:** Normalized relative-gauge displacement along every linear right splitting of vertical quotient is the same cocycle `c ↦ (a : ℂ)c`; this cocycle is zero at `a=0` and injective at every `a≠0`.

## Goal

Falsify or validate whether source-pointed normal jet depends on chosen splitting.

## Gates

- [x] 0 → 1: exact source-pure claim and torsor no-selector falsifier
- [x] 1 → 2: dependency-closed proof
- [x] 2 → 3: Lean theorems `primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse`, `_splitting_independent`, `_injective_iff`, and `_eq_zero_iff`
- [ ] 3 → 4: publication-ready

## Approach

Write `P_i > 0` for normalized source potential and `q(z₁,z₂)=z₂`. For any linear
`s` with `q ∘ s = id`, one has `(s c)₂=c`. The exact shear formula gives
`L_a(s c)-s c=(a P_i c,0)`. Division of first coordinate by `P_i` yields
`(a:ℂ)c`, independent of `s`, prime, and depth.

## Log

- 2026-08-24 — `[PAPER-PROVED]`; parent mechanism is standard extension-cocycle theory, exact BV--Wold application `[NOVELTY UNVERIFIED]`.
- 2026-08-24 — `[LEAN-PROVED]`; targeted module build passed; new theorem axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.
