# Log-weighted square-summable rigidity: polylogarithmic square mass, any positions

- **ID:** L163 / weil-cone-log-square-mass-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** hf-positive-hodge-attack/krein-producer-loops.md (L163)
- **Statement:** If `lam` is full-cone Weil-positive and `Σ_n (lam(n) − Λ(n))² / (1 + log n)^K < ∞` for some `K`, then `lam = Λ`.
- **Corollary:** RH ⟺ some Weil-positive system has log-weighted square-summable deviation from `Λ`.

## Goal
The hypothesis is equivalent to polylogarithmic square mass `Σ_{n≤N}(lam − Λ)² ≪ (log N)^{K'}`. It contains:
- L162 (`|lam − Λ| ≤ C(1+log n)^B/√n`, square mass `≪ (log N)^{2B+1}`);
- bounded deviations (or deviations of size `(log n)^{K/2}`) at arbitrary positions of any polylogarithmically sparse set, e.g. `{2^k, 2^k + 1}`. Their logarithms need no separation, so L160 does not apply.

## Paper proof
- Positivity on zero-free windows: L160's `localized_deviation_nonneg`. Its hypotheses hold because:
  - `v(n)² = (lam−Λ)²/n ≤ K! e · (lam−Λ)²/(1+log n)^K` (use `(1+log n)^K ≤ K! e n`), so `v` is bounded and in `ℓ²`;
  - `|v(n)|/(1+log n)^{K+2} ≤ ½[(lam−Λ)²/(1+log n)^K + 1/(n(1+log n)^{K+4})]` (AM-GM, the square `(X√n(1+log n)² − 1)² ≥ 0`).
- Mean values with `c_n = v(n)B(η log n)`, `|B(x)| ≤ K_J(1+|x|)^{−J}`, `J = K+2`:
  - `κ(n,m) ≤ 3 + N(n,m)` with `N(n,m) = (n+m)/|n−m|` for `n ≠ m` within a factor 2, else 0. Far pairs have `|log n − log m| ≥ log 2`, near pairs use `1/|log n − log m| ≤ max(n,m)/|n−m|`;
  - `Σ_n N(n,m) ≤ 5m(1+log m)` (two harmonic sums);
  - symmetric Schur: `Σ_m |c_m| Σ_n |c_n| N(n,m) ≤ Σ_m c_m² · 5m(1+log m)` (AM-GM on pairs, symmetry of `N`, exchange of the nonnegative double sum);
  - `c_m² · 5m(1+log m) ≤ 5K_p² (lam−Λ)(m)²/(1+log m)^K`, `K_p = K_J η^{−J}`, because `(1+log m)^{K+1} ≤ (1+log m)^{2J}`;
  - extraction error `≤ 3Σ|c| + K_p A_v · 5m(1+log m)`; mean-square error `≤ 3(Σ|c|)² + 5K_p² C_d`; all `O(η^{−2J})`.
- L160's assembly on the bad set with `T = η^{−(2J+1)}`, `η → 0`.

## Reach of the method
With polynomially decaying bump transforms the tail `Σ_{n > e^{1/η}}(lam−Λ)² B(η log n)²` stays polynomial in `1/η` exactly under polylogarithmic square mass. Faster-decaying bumps (Gevrey class) would reach `exp((log N)^{θ})` with `θ < ½`, still far below evaporation (`≍ N/log N`).

For dense supports this is L162's limit `|lam − Λ| ≲ n^{−½+o(1)}` on average. For sparse supports it removes L160's separation hypothesis.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3: `RHTower.eq_vonMangoldt_of_weilPositiveFull_of_log_square_summable` and `RHTower.riemannHypothesis_iff_exists_weilPositiveFull_log_square_summable` in `formal/GaloisForLFunctions/RHTower/WeilFullConeLogSquareMassRigidity.lean`, wired after `WeilFullConeSquareRootScaleRigidity`.
  - `lake build` of the module is green (42 s).
  - Axioms: `[propext, Classical.choice, Quot.sound]`.
  - Lint reports nothing for the module, and the collision sweep over 16 names is clean.
- [ ] 3 → 4 (not pursued)

## Log
- 2026-09-30 — L163. New reusable pieces:
  - `nearLogKernel` with `tsum_nearLogKernel_le`;
  - the symmetric Schur bound `tsum_abs_mul_tsum_nearLogKernel_le`, which exchanges a nonnegative double `tsum` via `summable_prod_of_nonneg` and `Summable.tsum_comm'`;
  - `windowCosSeries_meanValue_bounds_near`, generic mean-value bounds for bounded `ℓ¹` coefficients with `Σ c² n log n < ∞`.
  - Lean trap: the main theorem hit the 200k heartbeat limit until the mean-value block and the size arithmetic were moved into standalone lemmas.
