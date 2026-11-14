# Positive Weil floor on the first full two-prime window at aperture `log 2`

- **ID:** A140-two-prime-aperture-log-two
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1411/obstacles-summary.md` §2.21, §2.4
- **Statement:** On `[-log 2, log 2]` (ratio four, retaining prime-two and prime-three contacts), the actual Weil form satisfies `(1 / 10^13) ∫ F^2 ≤ weilQuad F` for every real `C²` test (`1 / 10^10` on the odd sector), `(1 / 10^13) ∫ ‖f‖^2 ≤ Re W(f, f)` for every complex `C²` test, and `1 / 10^13 ≤ ccmRestrictedWeilGroundEnergy ⟨log 2, _⟩ < 3 / 10^8`; consequently every step packet and neutral window `(R, R + J]` with `R + J < 4 R` (`Q ≥ 3`, `R ≥ 1`) has uniform gap `1 / 10^13` and (for `R ≤ J`) `hermNegIndex = 1`, and every ratio-three window (`R ≤ J ≤ 2 R`, `Q ≥ 2`, `R ≥ 1`) has `hermNegIndex = 1` with `levelAt 2 4 = 0`.

## Goal
Resolve §2.21 and §2.4 unconditionally in both directions:
1. Construct an explicit finite retained-charge positivity certificate at `A = log 2` dominating the complete quadratic form with proved analytic remainders, uniform under arbitrarily fine block refinement.
2. Exhibit an explicit smooth test `F_* ∈ C²_c([-log 2, log 2])` with `weilQuad F_* < (3 / 10^8) ∫ F_*^2` on which the degree-14 Gamma lower form (`gammaPolynomialLower14 (2 log 2)`) is strictly negative, establishing the sharp truncation boundary.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems checked with `lake --old env lean`, standard axioms only

## Approach
1. **18-digit arithmetic constants at `A = log 2`:** Rational enclosures of width `< 10⁻¹⁷` for `log 2`, `log 3`, `sqrt 2`, `sqrt 3`, `log π`, `eulerMascheroniConstant` (order-12 Euler–Maclaurin at `n = 24`), and `archLevyAntideriv (2 log 2)` (`N = 14` Laplace modes with exact `exp(-log 2) = 1/2`).
2. **Gamma kernel and pole comparison on `(0, 7/5]`:** Lower-bound `retainedGammaRemainderWeight t` on `(0, 7/5]` (`2 log 2 < 7/5`) by three odd lag powers (`7 t³/5760 - 31 t⁵/967680 + 127 t⁷/154828800`) plus an even degree-22 polynomial `∑_{q=0}^{11} α_q t^{2q}` with pointwise error `< 3 × 10⁻¹⁴`. Expand even lag powers exactly into Legendre moments of degree `≤ 22`. Decompose odd lag powers `t, t³, t⁵, t⁷` via iterated antiderivatives `J_{q+1} G(z) = (1/q!) ∫_z^1 (x - z)^q G(x) dx`, exact Fubini polynomial projection on `lowProjection G M`, and `(q+1)`-fold Dirichlet–Wirtinger bounds on the orthogonal remainder.
3. **Fiberwise Schur / completion-of-squares certificate (`K = 12` even, `K = 11` odd):** Partition `[0, 1]` into the 4-vertex path fiber `s ∈ [0, 1 - d₃/2]` (`(s, 1-s, a+s, 2-d₃-s)`, `d₃ = log 3 / log 2`, `a = d₃ - 1`) and the 2-vertex pair fiber `u ∈ [2 - d₃, 1/2]` (`(u, 1-u)`). Use `{2, 3}`-smooth shifted odd-order Taylor lower bounds for `-log(1 - x²)/2`, piecewise rational degree-6 polynomial witnesses on rational subintervals, zero witnesses on rational-irrational boundary slivers of width `< 10⁻¹⁶`, and exact `12 × 12` / `11 × 11` rational `L D Lᵀ` congruences.
4. **Continuum, block-matrix, and Green-ladder corollaries:** Transfer `WeilFloor (log 2) (1 / 10^13)` to real/complex tests, `ccmRestrictedWeilGroundEnergy`, `packetForm`, `blockMatrix`, `neutralWindow`, `dressedMiddle`, `schurStepExcess`, `levelAt`, `globalTowerLevel`, and `(R, 3 R]`.

## Log
- 2026-11-14 — created in 1-in-progress
