# Lacunary rigidity: no Weil-positive system deviates from Λ only on a sparse set

- **ID:** L158 / weil-cone-lacunary-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** hf-positive-hodge-attack/krein-producer-loops.md (L158)
- **Statement:** Let `lam` be full-cone Weil-positive and equal to `Λ` off a set `n_0 < n_1 < ⋯` with `n_0 ≥ 3` and `n_{i+1} ≥ 3n_i`. Then `lam = Λ`. The values on the set are unrestricted: any sign, any size within the Weil box, no summability.
- **Corollary:** For `p ≥ 3`, no Weil-positive system differs from `Λ` only at the powers of `p`.

## Goal
The corpus already had uniqueness for:
- the regular class (L78: partial sums `κ₁(n−1) + κ₂(√n−1) + E` with `Σ|E|/(n√n) < ∞`);
- `ℓ¹(n^{−½})` deviations (L64);
- one-sided deviations (L156/L157).

A lacunary deviation up to the box size `√n log n` has non-summable partial-sum remainders, so it falls outside all of these. This result covers that sparse, sign-changing, non-summable class.

## Gates
- [x] 0 → 1
- [x] 1 → 2 (paper proof below)
- [x] 2 → 3: `RHTower.eq_vonMangoldt_of_weilPositiveFull_of_lacunary` and `…_of_powers`, in `formal/GaloisForLFunctions/RHTower/WeilFullConeLacunaryRigidity.lean`.
  - `lake build` is green.
  - Axioms: `[propext, Classical.choice, Quot.sound]`.
  - Lint-clean, wired into `RHTower.lean`, and the collision sweep over 36 names is clean.
- [ ] 3 → 4 (not pursued)

## Paper proof
1. **Test.** Take the pair `f = Φχ_L + εΦχ_L(·−log n_j)`.
   - Its autocorrelation is `2K_L(y) + ε(K_L(y+c) + K_L(y−c))`.
   - Its zero side is at most `(1+e^{c/2})²·(near-radical energy) → 0`.
2. **Positivity at one atom.** Write `v = (Λ−lam)/√n` and choose `ε = −sgn v(n_j)`. Positivity gives
   `2|v_j|K(0) ≤ Σ_i|v_i|(4K(log n_i) + 2K(log n_i + log n_j)) + 2Σ_{i≠j}|v_i|K(|log n_i − log n_j|)`,
   after letting `L → ∞`.
3. **Decay.** `(1+D)K(D) ≤ 4.0804 e^{3D}e^{−π(e^D−1)}K(0)` for `D ≥ log 2`.
   - This comes from the L156 shift law together with `R(x) ≤ 4x²e^{−π(x−1)}` and `1 + D ≤ e^D`.
   - At `D = k log 3` the bound is at most `0.2177·1000^{1−k}`.
   - Summed over a 3-lacunary set, each family contributes at most `0.218`, and the off-diagonal family at most `0.436`.
4. **Weights.** Use `w_i = 1 + log n_i`.
   - `w_i ≤ w_j(1 + |log n_i − log n_j|)`.
   - The Weil box bound gives `|v_i| ≤ B·w_i`, so `M = sup|v_i|/w_i < ∞`.
   - Step 2 then yields `|v_j| ≤ (1.746/2)·M·w_j`.
   - Hence `M ≤ 0.873M`, so `M = 0`.

## What is new
Diagonal dominance of Riemann's kernel autocorrelation over separated log-lattices pins every sparse deviation, whatever its sign or size.

The method reaches exactly the separated sets. Two-generator sets `{p^a q^b}` have log-differences that accumulate at 0, so they escape.

This fits L148: producers need dense support. So sparse deviations are excluded, and dense deviations are exactly where the kernel method has no grip.

## Log
- 2026-09-30 — L158: conjecture, paper proof and Lean module in one cycle.
