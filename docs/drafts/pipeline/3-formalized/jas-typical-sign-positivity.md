# Typical real sign patterns are JAS-positive, uniformly in the prime set

- **ID:** jas-typical-sign-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** JAS ledger row 172 (`1-in-progress/jas-goal-loop-2026-10-09.md`); STATUS MUST-1352
- **Statement:** For every level `σ ≥ 1` and every `ε > 0` there is `X` such that for every finite set `P` of primes `p > X`, at most `ε·2^{|P|}` sign patterns `ε ∈ {±1}^P` give `Re Σ_ρ ∏_{p∈P}(1 + ε_p p^{−σ}cosh((ρ−½) log p))/(ρ(1−ρ)) < 0`.

## Goal
This is an unconditional partial producer for the real JAS family. With zeros approaching the line,
positivity of **all** sign patterns at `σ = 1` is RH (`R:JointAncestryRealAmplitudeVertex`). This card shows
that all but a vanishing proportion of patterns are positive, for every finite large-prime set at
once, with no budget restriction.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below)
- [x] 2 → 3  formalized: `exists_card_jasRealSign_re_neg_le` in `RHTower/JointAncestryRealSignTypical.lean`, built with `lake build --old`, `#print axioms` = standard three
- [ ] 3 → 4  publication-ready

## Proof
1. **Mean.** Each factor averages to `1` over its sign, so `Σ_{S⊆P} K_S(s) = 2^{|P|}`.
2. **Variance.** By the parallelogram law, `‖1+c‖² + ‖1−c‖² = 2(1+‖c‖²)`. Hence
   `Σ_S ‖K_S − 1‖² = 2^{|P|}(∏_P(1 + ‖c_p‖²) − 1)`, where `c_p = p^{−σ}cosh((s−½) log p)`.
3. **Second moments at a zero.** `‖c_p(ρ)‖² ≤ p^{−s_ρ}`, where `s_ρ = 2 − 2|Re ρ − ½| > 1` when `σ ≥ 1`.
4. **Uniformity in `P`.**
   - Euler product: `∏_P(1+p^{−s}) ≤ ∏_P(1−p^{−s})^{−1} ≤ Σ n^{−s} ≤ 1 + 1/(s−1)`.
   - High zeros (`|Im ρ| > H`): the classical region `|Re ρ − ½| ≤ ½ − 1/(100 log|Im ρ|)` gives `1/(s_ρ−1) ≤ 50 log(2+|Im ρ|)`. Since `Σ|w_ρ| log(2+|Im ρ|) < ∞`, their total is small.
   - Low zeros: their exponents are bounded away from `1`, so `∏_P(1+p^{−s}) ≤ exp(Σ_{n>X} n^{−s₀}) → 1`.
   - So `V_P = Σ_ρ |w_ρ|(∏_P(1+p^{−s_ρ}) − 1) → 0` uniformly in `P` as `X → ∞`.
5. **Count.** `Re A_S < 0` forces `‖A_S − Φ(0)‖ ≥ Φ(0)`, with `Φ(0) = 2+γ−log 4π`. By the weighted Cauchy–Schwarz inequality,
   `#bad · Φ(0)² ≤ W · 2^{|P|} V_P`, where `W = Σ|w_ρ|`.

## Approach / insight
- Uniform random **signs** average every non-empty Walsh monomial to `0`; uniform random **subsets**
  average to the amplitude-`½` test itself. So signs, unlike subsets, have a diagonal mean, which is
  what makes typical-positivity producers possible for the real family.
- The level `σ = 1` is exactly where `Σ_p p^{−2σ+2|Re ρ−½|}` converges for every zero.
- Compared with the complex random-phase count (`R:JointAncestryRandomPhasePositivity`): that count
  bounds the proportion by `O(Σ_P 1/p)`, using the worst case `|A_p| ≤ p^{½−σ}`. The per-zero bound plus
  the zero-free region removes the dependence on `P`.
- The exceptional patterns are the resonant ones (`ε_p` correlated with `cos(γ log p)` for an
  off-line zero). They carry the RH content and remain uncontrolled.

## Log
- 2026-10-13 — conjectured, proved, formalized (row 172); STATUS MUST-1352.
- 2026-10-13 — complex phase version (row 175): `exists_card_jasPhaseAggregate_re_neg_le` in `RHTower/JointAncestryRandomPhaseUniform.lean`; STATUS MUST-1354.
- 2026-10-13 — half-plane version (row 179): `exists_card_jasRealSign_re_neg_le_of_halfPlane` (typical positivity at every `σ > ½ + α`), general-exponent count `card_jasRealSign_re_neg_le_of_exponent`; STATUS MUST-1357.
- 2026-10-13 — deterministic vertical-translate version (row 183): `exists_volume_cosineTranslate_re_neg_le` in `RHTower/JointAncestryCosineTranslateTypical.lean` (almost every translate of the corpus cosine test is positive, uniformly in `P`); STATUS MUST-1359.
