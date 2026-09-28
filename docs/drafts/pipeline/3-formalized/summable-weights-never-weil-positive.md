# Summable prime weights are never Weil-positive

- **ID:** summable-weights-never-weil-positive
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** HF card `krein-producer-loops.md`, L54 (Weil cone) and L55
- **Statement:** If `Σ_{n≥2} |λ(n)| n^{−1/2} < ∞`, then for some level `a` and some polar-constrained `C²` test `f` supported in `[−a, a]`, `∫ |h_f|² S_{λ, ⌊e^{2a}⌋} < 0`. Here `S` is the finite-atom Weil symbol with `ζ`'s archimedean term.

## Goal
Weil positivity with `ζ`'s gamma factor cannot hold for any absolutely summable weight system. That includes every finite truncation `Λ·1_{n ≤ N}` and the prime-free system `λ = 0`.

Together with MUST-357 (`Λ + w` with `w` summable forces `w = 0`), this says:
- the Weil-positive set `W` meets `ℓ¹(n^{−1/2}) ∪ (Λ + ℓ¹(n^{−1/2}))` at most in `{Λ}`;
- positivity needs weights that diverge on the critical line (the pole of `D_λ` at `s = 1`).

## Gates
- [x] 0 → 1 in-progress: well-posed, attack idea
- [x] 1 → 2 fully-proven: paper proof below (all inputs classical or in the corpus)
- [x] 2 → 3 formalized: `RHTower.summable_weights_weilAtomSymbol_not_nonneg` (module `RHTower/WeilPositivitySummableWeightsObstruction.lean`, built, wired; axioms propext/Classical.choice/Quot.sound)
- [ ] 3 → 4 publication-ready

## Paper proof
Notation:
- `A(τ) = Re ψ(¼ + iτ/2) − log π` (`= archimedeanWeilSymbol(τ/2π)`).
- `F = paperFT f`, and `k = f ⋆ f̃`, so that `∫ |F|² cos(τy) dτ = π(k(y) + k(−y))`.

1. **Symbol.** `S(τ) = A(τ) − 2Σ_{n≥2} λ(n) n^{−1/2} cos(τ log n)`.
   - `S` is continuous, and `|S(τ)| ≤ C(1 + |τ|)`.
   - `|S_N − S| ≤ ε_N := 2Σ_{n>N} |λ(n)| n^{−1/2} → 0`, where `S_N` is the level symbol with atoms `n ≤ N`.
2. **Negativity somewhere.** Take a real `C²` test `g` supported in `[−b, b]` with `2b < log 2`.
   - `∫ |G|² cos(τ log n) = 0` for all `n ≥ 2` (corpus `integral_normSq_paperFT_mul_cos_eq_zero`), so `∫ |G|² S = ∫ |G|² A` by Fubini (summability).
   - **x-space formula.** Gauss gives `A(τ) = ψ(¼) − log π + ∫_0^∞ w(t)(1 − cos(τt/2)) dt` with `w(t) = e^{−t/4}/(1 − e^{−t})`. By Tonelli,
     `∫ |G|² A = 2π[(ψ(¼) − log π) k(0) + ∫_0^∞ w(t)(k(0) − k(t/2)) dt]`.
   - Choose `g = σ((b − x)/(δb)) σ((b + x)/(δb))`, with `σ` the smooth transition. Then `g` is `C^∞`, `0 ≤ g ≤ 1`, `g = 1` on `[−(1−δ)b, (1−δ)b]`, and `supp g ⊆ [−b, b]`. Hence:
     - `k(0) ≥ 2(1−δ)b`, and `k(t/2) = 0` for `t > 4b`;
     - `k(0) − k(x) = ½∫(g(y) − g(y − x))² dy ≤ 2δb + |x|` for all `x`;
     - `k(0) − k(x) ≤ 2δb L² x²` for `|x| < δb`, where `L = sup|g'|`.
   - With `w(t) ≤ e^{−t/4}(1/t + 1)`, `ψ(¼) = −γ − π/2 − 3log 2`, `γ > ½` and `4b → log 4`:
     - the far part is `k(0)∫_{4b}^∞ w ≤ k(0)(4e^{−b} + (4/5)e^{−5b}/(1 − e^{−4b})) ≤ 3.02 k(0)`;
     - the near part is `≤ 1.17 + O(δ log(1/δ)) + O(δ)`, with `L ≍ 1/(δb)`;
     - the total is `≤ 2π[−(5.29 − 3.02)·2(1−δ)b + 1.17 + O(δ log 1/δ)] < 0` for small `δ`.
   - Hence `∫ |G|² S < 0`, and `S(τ₁) < 0` for some `τ₁`.
3. **Concentration.** Take `f = κ₂ ⋆ q_S`: `κ₂` is the polar-free bump (transform vanishes at `±i/2`), and `q_S` is the twist probe at `τ₀` near `τ₁` with `κ̂₂(τ₀) ≠ 0`, scale `S`.
   - The L52 lemma `concentrated_integral_lower` gives `∫ |F|² S ≤ −c S + O(S^{−2})`.
   - The truncation error is `≤ ε_N ∫|F|² = ε_N · O(S)`, with `N = ⌊e^{2(S+1)}⌋`.
   - So the energy is negative for large `S`. ∎

## Log
- 2026-09-28 — created (L55); paper proof complete; Lean in progress in `formal/tmp/l55/`.
- 2026-09-28 — **Formalized.** Module `RHTower/WeilPositivitySummableWeightsObstruction.lean` (~1100 lines). Built and wired into `RHTower.lean`.
  - `integral_normSq_mul_arch_eq_jump`: the x-space archimedean energy, from Gauss's integral and a Tonelli swap. Reusable for any `C²` test.
  - `integral_normSq_paperFT_fejerTest_mul_arch_neg`: `∫ |h|² A < 0` for the flat-top test with `b = 17/50`, `d = 17/1000`.
    - The margin is `≈ 0.15` (times `2π`).
    - Inputs: `γ > ½`, `π > 3.14`, `log 2 > 0.693`, `log π > 1`, and `e^x ≥ 1 + x + x²/2`.
  - `flatBumpCorr_sub_le`: `R(0) − R(y) ≤ y`, via the monotone envelope. There is no derivative or total-variation argument.
  - `summable_weights_weilAtomSymbol_not_nonneg`: the theorem. Concentration reuses L52's `twistTest` at `α = 0`, and the level is chosen last.
