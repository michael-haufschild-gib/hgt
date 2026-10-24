# AIP Open Problem 6: Complete Resolution of the Shared Surplus Between the Light Cone and the Thin Band

- **ID:** aip-open-problem-6-complete-2026-10-24
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md` §7 Open Problem 6 (a), (b), (c)
- **Statement:** Complete, unconditional resolution of all three parts of Open Problem 6: (a) universal telescoping chain lower bound and two-sided logarithmic capacity law `Θ(log(1/ε))` for nested strips wider than `ε`; (b) Brun–Titchmarsh/Selberg-sieve widening of the light cone to the exact square-root scale `δ ≍ e^{−r}` (removing the `1/r` loss) and unconditional cofinal refutation (`∃ᶠ r in atTop`) at width `δ = C e^{−r}` via scale-invariant box energy and IVT dyadic PNT pigeonhole; (c) unconditional refutation of the signed thin-band inequality `Σ_{thinBand r} 2Λ(n)/√n ∫ F F(· + log n) ≤ T(0, r)` for all large `r` via the bipolar edge-dipole witness `bipolarEdgeTentOdd`, and exact cross-band Chebyshev compensation law.

## Goal
Resolve Open Problem 6 of `ArithmeticIncidencePositivity` completely and unconditionally in Lean 4, formalizing all consequences and corollaries (including the upgraded global shared-surplus allocation at the square-root scale `δ ≍ e^{−r}`).

## Gates
- [x] 0 → 1  in-progress: well-posed, corpus searched, attack ideas verified
- [x] 1 → 2  fully-proven: complete paper proofs of (a), (b), (c) with no open dependencies
- [ ] 2 → 3  formalized: Lean module `LightConeSquareRootScaleAndSignedBandObstruction.lean` checked with `lake --old env lean`, wired into `ArithmeticIncidencePositivity.lean`
- [ ] 3 → 4  README updated crisply

## Approach
1. **Part (a) — Universal Telescoping Chain & Two-Sided Logarithmic Capacity (`IsPayableOddPartFamily`):**
   - Prove the scale-invariant shell ratio `(r − p')/(p' − L/2) ≤ 2ρ/(1 − 2ρ)` for nested strips of half-widths `η' ≤ ρ η` (`0 < ρ < 1/2`).
   - At `ρ = 1/6`, prove that the geometric chain `L_j = 2(r − η_0 / 6^j)` (`0 < η_0 ≤ 1/12`, `r ≥ 7/6`) has shell fold constant `≥ 3/4` at every layer and telescopes to `∑_{j=0}^K (3/4) ∫_{S_j} α_{L_j}² ≤ T(L_0 − r, r) ≤ T(0, r)` for all continuous Lipschitz tests `F`.
   - Combine with `stripBoxEnergy_edgeTent_lt_sum_oddPart` to establish the two-sided logarithmic capacity sandwich `(2/5) log(1/(12ε)) ≤ Capacity(r, ε) ≤ 2 log(4/ε) + 84`.
2. **Part (b) — Exact Square-Root Width `δ ≍ e^{−r}` of the Light Cone:**
   - **Positive (Brun–Titchmarsh/Selberg Sieve Widening):** Use `RHTower.Sieve.card_prime_Ioc_le` at sieve level `Y = z = ⌊e^{r/3}⌋₊` together with exponent-injectivity of proper prime powers in short intervals (`n₂ − n₁ > 2 e^{r−δ}` for same-exponent proper prime powers `p₁^k < p₂^k`, `k ≥ 2`) to bound the prime-power count in `lightConeBand r δ` by `O(δ e^{2r} / r)`. The `1/r` cancels the `2r` atom numerator, yielding `∑_{lightConeBand r δ} 2Λ(n)/√n ≤ 16/10` and `sum_primeShift_le_lightCone` / `tsum_primeShift_le_globalAllocation` for `0 < δ ≤ c₀ e^{−r}` (`r ≥ 2`, and `c₀ = 1/60` for large `r`).
   - **Negative (Scale-Invariant Box Energy & Cofinal Square-Root Refutation):** Prove `stripBoxEnergy (edgeTentOdd r (δ/2)) (r − 2δ) r ≤ (3/2) δ³`. Since each odd part in `lightConeOuterHalf r δ` (`2r − 2δ ≤ log n ≤ 2r − δ`) carries `≥ δ³/512`, `δ³` cancels identically. Using the Intermediate Value Theorem on `g(r) = 2r − C e^{−r}` to tile `[2R, 2R + 1]` and the Prime Number Theorem (`tendsto_sum_vonMangoldt_div`), prove that for `C ≥ 8000` there exist arbitrarily large `r` (`∃ᶠ r in atTop`) where `T(r − 2 C e^{−r}, r)` fails to pay the odd parts at width `δ = C e^{−r}` (and similarly `T(0, r)` fails cofinally at width `δ = C r e^{−r}`).
3. **Part (c) — Bipolar Edge-Dipole Witness & Signed Band Refutation:**
   - Construct `bipolarEdgeTentOdd r x = edgeTentOdd r (1/48) x − edgeTentOdd (r − 1/12) (1/12) x`.
   - Prove that for every `L ∈ [2r − 1/6, 2r − 1/24]` (`thinBand r`), both self-pairings `F₊(x)F₊(x+L)` and `F₋(x)F₋(x+L)` vanish identically on `ℝ`, while both cross-pairings `−F₊(x)F₋(x+L)` and `−F₋(x)F₊(x+L)` are nonnegative everywhere on `ℝ`.
   - On the core sub-band `2r − 7/48 ≤ log n ≤ 2r − 1/8` (`⊆ thinBand r`), prove `∫ F(x) F(x + log n) dx ≥ 1/884736`, while `stripBoxEnergy F 0 r ≤ 3 r`.
   - Conclude by PNT that for all large `r`, `stripBoxEnergy F 0 r < ∑_{n ∈ thinBand r} 2Λ(n)/√n ∫ F(x) F(x + log n) dx` (even though every atom in `thinBand r` has `∫ F(x) F(x + log n) dx ≥ 0` and is individually paid by its own strip).
   - Prove the exact cross-band Chebyshev decomposition showing how the signed `thinBand r` charge is balanced in `reflectedPrimePolarCost F r` by the complementary shifts `relevantShifts r \ thinBand r` and `poleCharge F`.

## Log
- 2026-10-24 — created in 1-in-progress; paper proofs of 6(a), 6(b), 6(c) completed.
