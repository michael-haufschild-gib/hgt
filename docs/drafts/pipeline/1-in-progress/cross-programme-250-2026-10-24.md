# Cross-programme contributions to the twelve positivity programmes

- **ID:** cross-programme-250-2026-10-24
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** user `/goal` of 2026-10-24 (twelve programme READMEs).
- **Statement:** 250 significant unconditional Lean contributions answering open questions of the
  programmes, building their missing tools, or proving cross-programme theorems.

## Gates
- [x] 0 → 1  READMEs read; counting rule fixed (log: `logs/cross-programme-250-contributions-2026-10-24.md`)
- [ ] per contribution: paper proof → Lean (`lake --old env lean`, clean axioms) → umbrella wiring

## Active conjecture

**C1 (ACompT §8 topic 7, ACCE pillar 11 over 𝔽_q).** For the curve model with eigenvalues
`αᵢ`, `‖αᵢ‖ ≤ q`, and damping `ε > 0`, `ρ₀ = q^{−ε}`: the receiver is admitted at `ε` iff for every
`a` with `‖a‖ ≥ √q q^ε`, `mult(a) ≤ mult(ρ₀a) + [a = q]` (zero chains). Consequences: admission at
every small damping iff all `‖αᵢ‖ ≤ √q` (eigenvalues `≠ q`); isolated admitted dampings below the
width occur exactly at chain resonances.

Proof. `G·(1−u)²(1−qu)E = N := P·((1−ρ₀u)(1−qρ₀u) − δE)`, `E = Π(1−ρ₀αᵢu)`. Necessity: a root
`1/β`, `β = ρ₀a`, `|β|² ≥ q`, of higher order in `A` than in `N` gives
`G·(1−βu)^j A₁ = N₁/(1−βu)`, `N₁(1/β) ≠ 0`; the left side stays in the weighted `ℓ²` of the energy,
the right side has coefficients `βⁿN₁(1/β)`. Sufficiency: the multiset matching
`ρ₀·Bad ≤ S + {ρ₀q}` cancels every bad pole of `P·R`; the centring tail lemma and two prefix sums
give coefficients `O(n^k τⁿ)`, `τ < √q`.

## Log
- 2026-10-24 — created; C1 paper proof complete.
