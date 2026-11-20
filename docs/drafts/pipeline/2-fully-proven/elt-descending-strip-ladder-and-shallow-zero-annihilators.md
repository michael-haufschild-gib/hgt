# Descending strip-gap ladder, shallow-preserving Dirichlet zero annihilators, and Lehmer-quartet moment obstruction

- **ID:** elt-descending-strip-ladder-and-shallow-zero-annihilators
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1911/todo.md` #17 · `formal/GaloisForLFunctions/ExceptionalLayerTheory/`
- **Statement:** On any `ZeroConfig` violating `LandingLaw`, the off-line real parts right of `1 / 2` form a strictly decreasing sequence `1 / 2 + δ_n → 1 / 2` separated by open all-height zero-free vertical strips `(1 / 2 + δ_{n+1}, 1 / 2 + δ_n)` on each of which `topRightOrdinate` is constant; under `ZerosApproachLine`, finite Dirichlet polynomials `∏_{ρ ∈ L} (1 - 2^{ρ - s})` clear all zeros with `Re ρ ≥ 1 / 2 + ε / 2` while bounded away from zero on `Re s ≤ 1 / 2 + ε / 4`; the Ki–Kim–Lee saddle stays strictly inside `(1 / 2, 1)` on the healing window; and any off-line quartet `(±γ ± iδ)` (`δ ≠ 0`) matching the quadratic moment of a real Lehmer pair `(±(γ̄ ± η))` has root-product residual `+4 (γ̄^2 + δ^2)(η^2 + δ^2) > 0` and fourth-moment residual `-16 (γ̄^2 + δ^2)(η^2 + δ^2) < 0`.

## Goal
Establish the discrete strip-gap geometry of `¬ LandingLaw`, construct entire Dirichlet-polynomial multipliers that clear deep off-line zeros under `ZerosApproachLine` without disturbing shallow zeros, verify critical-strip confinement of the Ki–Kim–Lee Gaussian saddle, and prove the exact quartic Newton obstruction separating any off-line quartet from a real Lehmer pair.

## Gates
- [x] 0 → 1  in-progress: exact configuration, Hadamard-threshold, and Dirichlet-multiplier interfaces isolated
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `TheDescendingStripLadderAndShallowZeroAnnihilators.lean`, `lake --old env lean` green, standard axioms only

## Paper Proof (`[PROVED HERE]`)

1. **Strict descending strip-gap ladder under `¬ LandingLaw Z`.**
   - Unfolding `LandingLaw Z` gives `ApproachesLine Z` and `¬ (rightOf Z 0).Finite`.
   - Given any `δ > 0`, let `S(δ) = {ρ ∈ rightOf Z 0 | Re ρ < 1 / 2 + δ}`. If `S(δ)` were empty, then `rightOf Z 0 ⊆ rightOf Z (δ / 2)`, which is finite by `ApproachesLine Z`, contradicting `¬ (rightOf Z 0).Finite`.
   - Pick `ρ₀ ∈ S(δ)` and set `η = (Re ρ₀ - 1 / 2) / 2 > 0`. The subset `F = {ρ ∈ S(δ) | 1 / 2 + η < Re ρ}` contains `ρ₀` and lies inside the finite set `rightOf Z η`, so `Re` attains its maximum `1 / 2 + δ'` (`0 < δ' < δ`) on `F` at some `ρ₁ ∈ F`, which maximizes `Re` on all of `S(δ)`. Hence `Z` has no zeros at any height in the open vertical strip `1 / 2 + δ' < Re s < 1 / 2 + δ`.
   - Starting from `δ_{-1} = 1` (since `Re z ≤ 1 < 3 / 2` for all `z ∈ Z`) and iterating yields `δ : ℕ → ℝ` and `ρ : ℕ → ℂ` with `StrictAnti δ`, `0 < δ_n`, `ρ_n ∈ rightOf Z 0`, `Re ρ_n = 1 / 2 + δ_n`, `Re z ≤ 1 / 2 + δ_0` on `Z`, and zero-freeness on `(1 / 2 + δ_{n+1}, 1 / 2 + δ_n)`.
   - If `δ_n` did not tend to `0`, monotonicity would give `ε > 0` with `δ_n ≥ ε` for all `n`, placing the injective sequence `ρ_n` inside the finite set `rightOf Z (ε / 2)`. Finally, for any `z ∈ rightOf Z 0`, the least `k` with `δ_k < Re z - 1 / 2` satisfies `k = n + 1` (by `Re z ≤ 1 / 2 + δ_0`) and `1 / 2 + δ_{n+1} < Re z ≤ 1 / 2 + δ_n`, forcing `Re z = 1 / 2 + δ_n`.
   - For `Z = zetaZeroConfig`, every `q : XiZeroCopy` satisfies `q.1 ∈ zetaZeroConfig.carrier`, so `{q | σ < Re q.1} = {q | b ≤ Re q.1}` for all `σ ∈ [a, b)` whenever `(a, b)` is zero-free; thus `topRightOrdinate` is constant on `[1 / 2 + δ_{n+1}, 1 / 2 + δ_n)`.

2. **Shallow-preserving Dirichlet-polynomial zero annihilator under `ZerosApproachLine`.**
   - For `L : List ℂ`, set `M_L(s) = ∏_{ρ ∈ L} (1 - exp((log 2)(ρ - s))) = ∏_{ρ ∈ L} (1 - 2^{ρ - s})`. Each factor is entire, vanishes at `s = ρ`, has modulus `≤ 1 + 2^{Re ρ - σ₀}` on `Re s ≥ σ₀`, and satisfies `|1 - 2^{Re ρ - Re s}| ≥ 2^{Re ρ - Re s} - 1 ≥ 2^{σ₂ - σ₁} - 1 > 0` when `Re s ≤ σ₁ < σ₂ ≤ Re ρ`.
   - Under `ZerosApproachLine`, `F_ε = rightOf zetaZeroConfig (ε / 3)` is finite for every `ε > 0` and contains every zero `ρ ∈ zetaZeroConfig.carrier` with `Re ρ ≥ 1 / 2 + ε / 2`. Enumerating `{ρ ∈ F_ε | 1 / 2 + ε / 2 ≤ Re ρ}` into `L` produces an entire Dirichlet polynomial vanishing on all zeros with `Re ρ ≥ 1 / 2 + ε / 2` and satisfying `‖M_L(s)‖ ≥ (2^{ε / 4} - 1)^{|L|} > 0` on `Re s ≤ 1 / 2 + ε / 4`.

3. **Ki–Kim–Lee saddle confinement.**
   - When `0 < C`, `0 < t ≤ C δ^2`, `2π < X`, and `δ^2 log(X / (2π)) < 1 / (2C)`, positivity of `log(X / (2π))` gives `1 / 2 < 1 / 2 + t log(X / (2π)) ≤ 1 / 2 + C δ^2 log(X / (2π)) < 1`.

4. **Exact quartic Newton obstruction between a real Lehmer pair and an off-line quartet.**
   - Under `(γ̄ + η)^2 + (γ̄ - η)^2 = 2(γ^2 - δ^2)`, we have `γ^2 = γ̄^2 + η^2 + δ^2`, whence
     $$(γ^2 + δ^2)^2 - (γ̄ + η)^2 (γ̄ - η)^2 = (γ̄^2 + η^2 + 2δ^2)^2 - (γ̄^2 - η^2)^2 = 4(γ̄^2 + δ^2)(η^2 + δ^2)$$
     and `4(γ^4 - 6γ^2 δ^2 + δ^4) - 2((γ̄ + η)^4 + (γ̄ - η)^4) = -16(γ̄^2 + δ^2)(η^2 + δ^2)`. Whenever `δ ≠ 0`, `(γ̄^2 + δ^2)(η^2 + δ^2) ≥ δ^4 > 0`.

## Log
- 2026-11-20 — complete paper proof recorded in `2-fully-proven`.
