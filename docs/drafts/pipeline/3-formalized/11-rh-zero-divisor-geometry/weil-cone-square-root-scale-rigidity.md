# Square-root-scale rigidity: pointwise `n^{−½}` deviations of any sign pattern are excluded

- **ID:** L162 / weil-cone-square-root-scale-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** hf-positive-hodge-attack/krein-producer-loops.md (L161 survivor, L162)
- **Statement:** If `lam` is full-cone Weil-positive and `|lam(n) − Λ(n)| ≤ C(1+log n)^B/√n` for all `n ≥ 2`, then `lam = Λ`.
- **Corollary:** RH ⟺ some Weil-positive system lies within `C(1+log n)^B/√n` of `Λ`.

## Goal
The exact-primes gate MUST-507 (L78) excludes deviations whose partial sums are `κ₁(x−1) + κ₂(√x−1) + E` with `Σ|E(n)|n^{−3/2} < ∞`, i.e. power-saving remainders. L64 excludes `ℓ¹(n^{−½})` deviations.

A deviation `a(n) = n^{−½}(log n)^B s(n)`, with `s` a sign pattern constant on slowly growing blocks, satisfies neither:
- its partial sums are `√x·f(log x)` with `f` oscillating, so the remainder is not power-saving;
- `Σ|a|/√n` diverges.

This theorem excludes it. It is the first rigidity result that reaches partial sums at the `√x` scale.

## Paper proof
- Positivity on zero-free windows is L160's `localized_deviation_nonneg`. Its hypothesis `Σ|v|(1+log n)^{−(B+2)} < ∞` holds because `|v(n)| ≤ C(1+log n)^B/n`.
- Mean values on `[T,2T]` use the integer kernel `κ(n,m) = 1/|log n − log m| + 1` (and `κ(m,m) = 1`).
- `|log n − log m| ≥ |n−m|/max(n,m)`, together with `m/(n(m−n)) = 1/n + 1/(m−n)`, gives the majorant `F(n)κ(n,m) ≤ [n=m] + F(n) + F(n−m)[n>m] + (F(n) + 1/(m−n))[n<m]`.
- Hence `Σ_n F(n)κ(n,m) ≤ 2 + 3ΣF + log m` (harmonic bound) for `F(n) = 1/(n(1+log n)³)`, which is summable by Cauchy condensation.
- With `c_n = v(n)B(η log n)` and `|B(x)| ≤ K_J(1+|x|)^{−J}`, `J = B+3`:
  - `|c_n| ≤ Kη^{−J}F(n)`;
  - the extraction error is at most `Kη^{−J}(2 + 3ΣF + log m)`;
  - the mean-square error is at most `K²η^{−2J}((2+3ΣF)ΣF + ΣF₂)`;
  - the diagonal satisfies `Σc_n² ≤ B(0)²Σv²` (finite, since `v(n)² ≲ F₂(n)`).
- The rest is L160's assembly on the bad set, with `T = η^{−(2J+1)}` and `η → 0`.

## Sharpness of the method
If `|a(n)| ≍ n^{−θ}` with `θ < ½`, the near-diagonal Schur sum `Σ_m|c_m| m^{½−θ}` diverges. So pointwise size `n^{−½+o(1)}` is exactly the reach of zero-free windows on the full support `ℕ`.

Evaporation-type second producers have `|a(p)| ≍ 1`, a factor `√p` beyond this.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3: `RHTower.eq_vonMangoldt_of_weilPositiveFull_of_sqrt_scale` and `RHTower.riemannHypothesis_iff_exists_weilPositiveFull_sqrt_scale` in `formal/GaloisForLFunctions/RHTower/WeilFullConeSquareRootScaleRigidity.lean`, wired after `WeilFullConeZeroFreeWindowRigidity`.
  - `lake build` is green.
  - Axioms: `[propext, Classical.choice, Quot.sound]`.
  - Lint reports nothing for the module, and the collision sweep over 21 names is clean.
- [ ] 3 → 4 (not pursued)

## Log
- 2026-09-30 — L162: reused the L160 infrastructure. New in this module:
  - the integer Schur bound;
  - generic mean-value lemmas with an arbitrary kernel majorant;
  - a generic assembly (`half_mul_abs_le_of_zeroFree_of_bounds`).
