# The producer abscissa σ_prod

- **ID:** producer-abscissa
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + CONJECTURE
- **Source:** `hf-positive-hodge-attack/krein-producer-loops.md`, L346.
- **Statement:** `σ_prod := inf{σ₀ : ∃ lam, Ψ₀ − Σlam(n)n^{−s}` is Carathéodory on `σ > σ₀}` satisfies `½ ≤ σ_prod ≤ Θ`, and the infimum is attained.
  - Theorem: `σ_prod ≥ ½`.
  - Conjecture: `σ_prod = Θ`.

## Goal
- PBAP ⟺ `σ_prod = ½` (attained), so a producer exists iff the abscissa reaches its unconditional floor.
- The conjecture `σ_prod = Θ` implies detection: PBAP ⇒ RH.
- The problem becomes a one-parameter family. Above `½`, on-line zeros give positive slack, so the problem might be attacked first at `σ₀` close to `1`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (theorem part; L346, constants made explicit in the Lean proof)
- [x] 2 → 3  formalized (theorem part): `RHTower.CarlsonFloor.not_isHalfPlaneProducer_of_lt_half` in `RHTower/CarlsonHalfPlaneProducerFloor.lean`, standard axioms. The conjecture part stays open.

## Approach
- Theorem: Carlson-type mechanism (L346 steps 1–4).
- Conjecture: prime-blind tests at abscissa `σ₀`, where complex amplification `e^{(β−σ₀)τ}` competes with the Poisson slack `log γ/2π`. First test case: a hypothetical single zero with `β > σ₀ ≥ ¾`.
- Example to keep in view: gap-weighted primes `D_gap` (holomorphic to `0.525` unconditionally; growth `t^{β−σ}` at zeros).

## Log
- 2026-10-03 — created from L346.
- 2026-10-03 — theorem part formalized (L347): Carlson floor plus Harnack, abstract log-growth `Ψ`.
