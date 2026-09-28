# Weil positivity bounds the multiplicative Toeplitz matrix of the prime weights

- **ID:** weil-toeplitz-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** HF card `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, loop L57; facts HF-F53, HF-F54; STATUS MUST-498
- **Statement:** If the finite-atom Weil symbol with weights `lam` and ζ's archimedean term is nonnegative on every polar-constrained `C²` test at every level, then `2Σ_{2≤n≤N} lam(n)n^{−½} Re Σ_m c(nm)conj c(m) ≤ (log N + C₀)Σ_m|c(m)|²` for every `c` supported in `[1,N]`, with an absolute constant `C₀`.

## Goal
Find a universal constraint on all Weil-positive weight systems, not just perturbations of `Λ`. The constraint is sharp at `Λ`: the top eigenvalue of the multiplicative Toeplitz matrix of `lam(n)n^{−½}` is at most `log N + O(1)`, and the log-density is at most 1.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below)
- [x] 2 → 3  formalized: `RHTower.weil_multiplicativeToeplitz_bound`, `RHTower.weil_twisted_density_bound`, `RHTower.weil_log_density_le` in `RHTower/WeilPositivityMultiplicativeToeplitzBound.lean`; `lake build` green; axioms propext, Classical.choice, Quot.sound.
- [ ] 3 → 4  publication-ready

## Proof
1. **Resonator test.** Fix `N`, `w = 1/(N+1)`, and a smooth bump `ψ` supported in `(−¼,¼)`. Set `ψ_w(x) = ψ(x/w)` and `g_w = ψ_w'' − ψ_w/4`, so `ĝ_w(z) = −(z²+¼)ψ̂_w(z)` vanishes at `±i/2`.
   The test is `f = Σ_{m≤N} c(m) g_w(x − log m + ½log N)`: `C^∞`, supported in `[−a,a]` with `a = ½log N + w/4`, and polar-free.
2. **Exact prime side.** The autocorrelation is `k_f(y) = Σ_{m,m'} c(m)c̄(m')k_g(y − log m + log m')`, with `k_g = 0` for `|y| > w/2`.
   Distinct `log q`, `log m` with `m ≤ N` differ by at least `1/(N+1) > w/2`. So:
   - `k_f(log n) = k_g(0)Σ_{m'}c(nm')c̄(m')`;
   - `k_f(−log n)` is its conjugate;
   - `k_f(0) = k_g(0)Σ|c|²`.
3. **Archimedean side.** The vertical digamma bound gives `A(τ) = Re ψ(¼+iτ/2) − log π ≤ log(1+|τ|) + 4`. Then `log(1+|τ|) ≤ log(N+1) + w|τ|` and `w|τ| ≤ ½ + w²τ²/2`, so
   `∫|f̂|²A ≤ (log(N+1)+9/2)·2πk_g(0)Σ|c|² + (w²/2)·2πk_{g'}(0)Σ|c|²`, using `|f̂'|² = τ²|f̂|²` and Plancherel.
4. **Scale-free profile constant.** Integration by parts gives `∫ψ''ψ = −∫ψ'²`. Hence `‖g_w‖² ≥ w^{−3}‖ψ''‖²`, and `w²‖g_w'‖² ≤ w^{−3}(2‖ψ'''‖² + ‖ψ'‖²)` for `w ≤ 1`.
5. **Conclusion.** Weil positivity reads `0 ≤ ∫|f̂|²A − 2πΣ_n lam(n)n^{−½}Re(k_f(log n)+k_f(−log n))`. Divide by `2πk_g(0) > 0`.
6. **Corollaries.** Take `c(m) = χ(m)m^{−½}`, and use `Σ_{m≤N}1/m ≤ 1 + log N`.

## Position
- **New.** A universal, sharp necessary condition for Weil positivity in operator form: the multiplicative Toeplitz matrix is bounded by the archimedean scale `log N`. This yields the first upper-density law for arbitrary Weil-positive weights (the corpus had only `cΛ`, L52).
- **Limit.** Resonance is saturated by `Λ`, so density-only arguments cannot exclude smooth elements of the Weil cone with density in `[r*, 1]`.
- **For `Λ` itself** the bound is unconditional and elementary: the Schur test with `h(m)=m^{−½}` and `Σ_{d|m}Λ(d) = log m` plus Mertens. The law is a Mertens-level constraint on other weight systems, not a producer target.

## Log
- 2026-09-28: L57 conjectured, proved on paper, formalized and wired.
