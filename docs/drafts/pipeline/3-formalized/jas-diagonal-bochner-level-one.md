# Diagonal Bochner bound: level-1 product positivity forces RH

- **ID:** jas-diagonal-bochner-level-one
- **Stage:** 3-formalized
- **Type:** THEOREM → Lean
- **Source:** JAS goal loop, row 119 (`jas-goal-loop-2026-10-09.md`)
- **Statement:** If `JasProductPositiveAbove X σ` with `σ ≥ 0`, then every zero satisfies `|Re ρ − ½| ≤ max(0, σ − 1)`. In particular product positivity at level 1 (or at any level `≤ 1`) implies RH, with no quasi-RH hypothesis. This closes [B].

## Proof (paper)
Notation: `Φ(L) = Σ_ρ w_ρ e^{(ρ−½)L}`, `w_ρ = 1/(ρ(1−ρ))`, `W = Σ|w_ρ|`, `Φ(0) = poleSharpConstant`, `α = sup|Re ρ − ½| = Θ − ½`.

1. **Diagonal test.** Fix `u`, a window of primes `P ⊂ [e^u, e^{u+h}]` (all `> X`), `r ∈ (0,1]`, `s = r/(1+r²)`, and set `z_p = r e^{−iθ}`. The Bernoulli factor is `(1+r²)(1 + s p^{−σ}(b_p e^{iθ} + b_p^{−1}e^{−iθ}))` with `b_p = p^{ρ−½}`. So `T(θ) = Σ_ρ w_ρ ∏_p (1 + a_p(b_p e^{iθ} + b_p^{−1}e^{−iθ}))`, with `a_p = s p^{−σ}`, has `Re T(θ) ≥ 0` for every `θ`.
2. **Coefficients.** Let `ĉ_n` be the discrete Fourier coefficients over `N > 2|P|+2` equally spaced `θ_j`. With weights `1 + Re(ζ ω^{−j}) ≥ 0` (`|ζ| ≤ 1`): `Re ĉ_0 + ½ Re(ζ(ĉ_1 + conj ĉ_{−1})) ≥ 0`, hence `|ĉ_1 + conj ĉ_{−1}| ≤ 2 Re ĉ_0`.
3. **Per-zero coefficients.** For one zero, write `b_p = B β_p` with `B = e^{(ρ−½)u}` and `|β_p^{±1}| ≤ e^{h/2}`. The coefficient recursion `c'(n) = c(n) + a x c(n−1) + a y c(n+1)` gives the weighted ℓ¹ bound `Σ_n |r(n)| |B|^{−n} ≤ M − 1 − 2D`, where `r` is the coefficient minus `δ_0 + δ_1 λ₊ + δ_{−1} λ₋`, `M = ∏(1 + 2a'_p)`, `D = Σ a'_p` and `a' = a e^{h/2}`. Hence:
   - `ĉ_0(ρ) = 1 + O(T)`;
   - `ĉ_1(ρ) = Σ_p a_p b_p + O(|B| T)`;
   - `ĉ_{−1}(ρ) = Σ_p a_p b_p^{−1} + O(|B|^{−1} T)`;

   where `T = M − 1 − 2D ≤ K² e^K/2` and `K = 2D`.
4. **Aggregate.** Summing over zeros gives (★): `|Σ_p a_p Φ(log p)| ≤ Φ(0) + W(e^K − 1) + W e^{αu} K² e^K`.
5. **Coherence.** `|Φ(L) − Φ(u)| ≤ e^{αu}·2e^{½}[(½ + T₁) y W + 80(C + log(3T₁+4))/T₁]` for `y = L − u ∈ [0, h]`. This uses `|e^z − 1| ≤ 2e^{|Re z|} min(1, |z|)` and the corpus tail `tsum_indicator_abs_im_gt_weight_le`. With `T₁ = h^{−1/2}` this is `O(e^{αu} h^{1/2} log(1/h))`.
6. **Window.** Huxley (`exists_theta_window_lower_seven_twelfths`) with `h = e^{−δu}`, `0 < δ < 5/12`: the window has `Σ_P p^{−σ} ≥ e^{(1−δ−σ)u}/(C u)`. For `c > max(0, σ − 1 + δ)` this is `≥ e^{−cu}` for large `u`. Choose `r = e^{−cu}/M_P`, so `Σ a_p ∈ [e^{−cu}/2, e^{−cu}]` and `K ≤ 4e^{−cu}`.
7. **Bound on Φ.** `|Φ(u)| ≤ C(e^{cu} + e^{(α−c)u} + u e^{(α−δ/2)u})` for all large `u`.
8. **Growth criterion** (`re_le_half_add_of_weilLagFunctionReal_le_exp`): `α ≤ max(c, α − c, α − δ/2) + η`. Hence `α ≤ c + η`. Letting `c ↓ max(0, σ−1)` gives `α ≤ max(0, σ − 1)`.

Consistency: at `σ ∈ [1, 3/2]` this is the known abscissa law `Θ ≤ σ − ½`, now with no chain or quasi hypothesis. At `σ = 3/2` it is trivial, matching unconditional positivity there. Discreteness enters only through the growth criterion (poles of the lag pole series). A continuous off-line "zero measure" would satisfy positivity, so the argument is genuinely global.

## Lean plan
- [x] Stage 1: `RHTower/DiagonalLaurentCoefficients.lean` — `laurentCoef`, `diagFourier_diagProd_eq` (discrete extraction), `tsum_laurentRem_le`/`norm_laurentRem_le` (weighted remainder), `norm_diagFourier_one_add_conj_le` (Bochner on the discrete circle).
- [x] Stage 2: `RHTower/JointAncestryDiagonalBochner.lean` — `abs_sum_weilLagFunctionReal_le_of_jasProductPositiveAbove` (★).
- [x] Stage 3: `abs_weilLagFunctionReal_add_sub_le` (coherence from the weight tail).
- [x] Stage 4: `exists_window` (Huxley window with weight), `abs_weilLagFunctionReal_le_of_window`.
- [x] Stage 5: `exists_abs_weilLagFunctionReal_le_exp_of_jasProductPositiveAbove`, `abs_re_sub_half_le_of_jasProductPositiveAbove`, `riemannHypothesis_iff_exists_jasProductPositiveAbove_one`, `xiZeroHalfPlaneBound_of_jasProductPositiveAbove` (all in `RHTower/JointAncestryDiagonalBochnerLevel.lean`). Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-12: paper proof written; Lean stage 1 started.
- 2026-10-12: stages 1–2 compile (not yet wired; no sorry).
- 2026-10-12: stages 3–5 compiled; wired into the RHTower umbrella; moved to 3-formalized. [B] is closed: RH ⟺ ∃X, JasProductPositiveAbove X 1.
- 2026-10-12: side-condition-free capstones in R:JointAncestryLevelOneCapstones (dressed PSD, large-prime PSD, cosine kernel, Weil–Euler, PSD at infinity).
