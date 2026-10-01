# Selberg completions with smooth-supported mollifiers are not Weil-positive

- **ID:** weil-cone-selberg-completion-floor-exclusion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** krein-producer-loops L3 (Conjecture SM), L214, L218, L220 · STATUS CANNOT-490
- **Statement:** If `w(1) > 0` and `w(d) = 0` for every `d ≥ 2` whose prime factors all exceed some `Y`, then `Λ_w = (μw)⋆log` is not full-cone Weil-positive for ζ's datum.

## Goal
HF's producer route took the level-`a` Krein completions `Λ_w` (`w = 1` on `[1, e^{2a}]`) and asked whether one of them is full-cone Weil-positive (L3, Conjecture SM). A positive answer at every level would give RH by closedness. The theorem refutes SM for every fixed `w` of finite or smooth support, unconditionally.

## Gates
- [x] 0 → 1  in-progress: well-posed; attack is the rough floor plus divisor resonance
- [x] 1 → 2  fully-proven: paper proof below
- [x] 2 → 3  formalized: `RHTower.SelbergCompletionFloor.not_weilPositiveFull_selbergWeightedVonMangoldt` (module `RHTower/WeilFullConeSelbergCompletionFloorExclusion.lean`). `lake env lean` is clean. `#print axioms` gives propext, Classical.choice, Quot.sound. The module is wired into the `RHTower` umbrella.
- [ ] 3 → 4  publication-ready

## Proof
1. **Rough floor.** For `n` whose prime factors all exceed `Y`, every divisor `d ≥ 2` has the same property, so `w(d) = 0`. Hence `Λ_w(n) = μ(1)w(1) log n = w(1) log n ≥ w(1) log 2` for `n ≥ 2`.
2. **Resonance** (corpus `floor_resonance_inequality`, from the multiplicative Toeplitz bound). Let `N = ∏_{p∈S} p` for a finite prime set `S`. If `lam ≥ c` on the divisors `≥ 2` of `N`, then `2c(Q_S − 1) ≤ log N + C₀`, where `Q_S = ∏_{p∈S}(1 + p^{−½}/2)`.
3. **Window.** Take `S` to be `⌊b²/(3 log b)⌋` primes in `(b², b³]` (Chebyshev), with `b ≥ Y`. Then:
   - every divisor of `N` is `Y`-rough;
   - `log N ≤ b²`;
   - `Q_S ≥ exp(|S| b^{−3/2}/4) ≥ b⁶`.
   So `2c(b⁶ − 1) ≤ b² + C₀`, which is false for large `b`.

## Classification beyond the Lean case [P]
For finitely supported `m ≢ 0` and any `a ∈ ℝ`, `aΛ + m⋆log ∉ W`. Use the complex resonator `c(bq) = s(b)χ(q)1_{q∣N}`, which the formal Toeplitz bound admits.
- `m(1) > 0`: the Lean case.
- `m(1) = 0`: the real two-point resonator `s = e₁ ± e_{b₁}` with `(1⋆m)(b₁) ≠ 0`.
- `m(1) < 0`: `χ(p) = e^{iα}`, with the phase fixed by the intermediate value theorem.

Details are in L220.

## No-go closure
- **Exact killing mechanism:** finite-range multipliers of `ζ'` leave the constant term `m(1)` as a floor `m(1) log n` on rough integers. Rough-window divisor resonance, a factor `≥ b⁶` against `log N ≤ b²`, excludes the floor.
- **Strongest positive survivor:** the classification `(span Λ ⊕ {m⋆log : m finite}) ∩ W ⊆ {Λ}`. It has a complete paper proof. Lean covers `m(1) > 0`, which includes every Selberg completion. The `m(1) = 0` case is next: it needs only a real resonator.
- **New insight:** the completion freedom at composite frequencies beyond `e^{2a}` (invisible to the level-`a` form) is exactly where rough-window resonance lives. A full-cone completion must have no positive floor on any rough squarefree window.
- **Status:** Lean for the Selberg family; paper for the general classification.

## Log
- 2026-09-30 — created at stage 3 (Lean module compiled; axioms standard)
