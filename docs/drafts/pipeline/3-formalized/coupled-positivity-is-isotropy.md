# Coupled positivity is isotropy, not blindness (Q2 / B3.17, wall 14.10)

- **ID:** coupled-positivity-is-isotropy
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-2510/hard-obstacles-summary.md` Q2, B3.17; walls-ledger 14.10.
- **Statement:** On the Meyer source, positivity of a multiplier-coupled trace form on a
  point-stable carrier is equivalent, at each off-line pair `{ρ, ρ*}`, to orthogonality of the two
  fibres for the coupling matrix `K_ρ(a,b) = m_ρ conj τ_ab(ρ*) + m_ρ* τ_ba(ρ)`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
`S(g,h) = Σ_q ĝ(ρ_q) conj ĥ(ρ_q*)` (trace degree of `g ⋆ h♯`); `tr = Re S`. If `ĝ` vanishes on the
divisor outside a finite `s`, `S(g,h) = Σ_{σ∈s} m_σ ĝ(σ) conj ĥ(σ*)`.

For `g, g' ∈ M` and `α ∈ ℂ` put `u_a = α (g_a ⋆ δ_ρ) + g'_a ⋆ δ_ρ*` (in `M` by point stability).
Its values are `α x` at `ρ`, `y` at `ρ*`, `0` elsewhere (`x = ĝ(ρ)`, `y = ĝ'(ρ*)`), and
`Q(u) = Re(α Z)`, `Z = Σ_ab x_a conj(y_b) K_ρ(a,b)` (only cross terms survive since `ρ* ≠ ρ`).
`α = −conj Z` gives `−|Z|² ≥ 0`, so `Z = 0`.

Corollaries.
- All tuples positive ⇒ `K_ρ = 0` at every off-line `ρ` (test unit vectors).
- One channel, identity coupling: `K = m_ρ + m_ρ* > 0`, so a positive convolution ideal is blind
  at `ρ` or at `ρ*`; with `♯` both (maximality theorem recovered).
- `J_left = {ĝ = 0 left of the line}`: each term of `S(g,g)` is `0` or `|ĝ(σ)|²`, so positive; it
  equals `{g : tr(Φ_c g, h) bounded for c ≤ 0, ∀h}` (`|e^{c(σ−½)}| ≤ 1` right of the line; the
  point source at `σ*` reads `m e^{c(σ−½)} ĝ(σ)`, unbounded left of the line). `J_left = ⊤ ⇔ RH`,
  and `meyerTraceBoundedIdeal < J_left` unless RH.

## Insight
Positivity certifies isotropy of the visible fibres at off-line pairs, not blindness. A positive
carrier may see an off-line zero when it is blind to the reflected point along the coupling. The
exhaustion problem is unchanged: every such carrier is everything only under RH.

## Lean
`ArithmeticPositiveDuality/CoupledPositivityIsIsotropy.lean`, checked with `lake --old env lean`,
axioms `[propext, Classical.choice, Quot.sound]`: `coupled_isotropy`,
`coupling_vanishes_of_nonneg_on_all`, `positive_ideal_halfBlind`,
`le_meyerTraceBoundedIdeal_of_positive_sharp_ideal`, `meyerSourceTrace_nonneg_of_mem_leftBlindIdeal`,
`leftBlindIdeal_eq_top_iff`, `meyerTraceBoundedIdeal_lt_leftBlindIdeal`,
`mem_leftBlindIdeal_iff_backwardFlowBounded`.

## Open
Carriers without point stability (Rankin–Selberg sources, cones without convolution closure);
the dimension form of isotropy (`dim V_ρ + dim V_ρ* ≤ n` for invertible `K_ρ`).
