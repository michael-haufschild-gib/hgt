# A Weil-positive system with summable deficit below Λ is Λ

- **ID:** L157 / weil-cone-summable-deficit-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** hf-positive-hodge-attack/krein-producer-loops.md (L157)
- **Statement:** If `lam` is full-cone Weil-positive and `Σ_n (Λ(n) − lam(n))⁺ n^{−½} < ∞`, then `lam = Λ` on `n ≥ 2`. Nothing is assumed about the excess `(lam − Λ)⁺`.

## Goal
One theorem contains three earlier results as special cases:
- upward rigidity (zero deficit);
- eventual upward rigidity (finite deficit), which is new;
- summable rigidity L64 (both parts summable).

Together with L156 (downward rigidity), any producer `lam ≠ Λ` must have **infinite** deficit below `Λ` and also some excess above `Λ`.

Corollary: RH ⟺ some full-cone Weil-positive `lam` has summable deficit.

## Gates
- [x] 0 → 1
- [x] 1 → 2 (paper proof below)
- [x] 2 → 3: the following theorems are in `formal/GaloisForLFunctions/RHTower/WeilFullConeSummableDeficitRigidity.lean`:
  - `RHTower.eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit`
  - `…_of_eventually_ge`
  - `riemannHypothesis_iff_exists_weilPositiveFull_summable_deficit`

  `lake build` is green; the axioms are `[propext, Classical.choice, Quot.sound]`; the module is lint-clean and wired into `RHTower.lean`.
- [ ] 3 → 4 (not pursued)

## Paper proof
1. **Comb test.** Let `f = Σ_{j<M} Φχ_L(·−j)`.
   - Its transform is `(Σ_j e^{izj})û`, and the multiplier is at most `Me^{M/2}` on the strip. So `‖W(f,f)‖ ≤ (Me^{M/2})²·(near-radical energy of Φχ_L) → 0` as `L → ∞`.
   - Its autocorrelation is `k(y) = Σ_{i,j<M}K_L(y+j−i)`.
2. **Properties of `k`.**
   - `0 ≤ k(y) ≤ k(0)`, by AM–GM under the integral.
   - `k(0) ≤ 3CM`, from `K_L(y) ≤ Ce^{−2|y|}` and `Σ_{d∈ℤ}e^{−2|d|} ≤ 3`.
   - `k(y) ≥ (M−⌊y⌋)m²` for `y ≥ 0` and `L ≥ 2`. Keep the diagonal band `i − j = ⌊y⌋`, and use `K_L(z) ≥ m²` on `[0,1]` with `m = min_{[−1,1]}Φ`.
3. **Positivity.** Write `a = (lam−Λ)/√n = a⁺ − a⁻` and `D = Σ a⁻`. Positivity gives `Σ a(n)(k(log n)+k(−log n)) ≤ ‖W‖ ≤ 1`.
   - The excess terms are at least `Σ_{n<N} a⁺(n)k(log n) ≥ (N+1)m² Σ_{n<N} a⁺`, taking `M = 2N+2` so that `M − ⌊log n⌋ ≥ N+1`.
   - The deficit terms are at most `2k(0)D ≤ 6CMD`.
   - Hence `Σ_{n<N} a⁺ ≤ (1+12CD)/m²` for every `N`.
4. **Conclusion.** So `a⁺` is summable, and `lam − Λ ∈ ℓ¹(n^{−½})`. Summable rigidity (L64, via `weilPositive_of_weilPositiveFull`) then gives `lam = Λ`.

## What is new
The "triangle" comb of near-null tests turns Weil positivity into a one-sided ℓ¹ transfer: the excess of a Weil-positive system over `Λ` is bounded by a constant times its deficit.

The open core is now the other one-sided case: summable excess with infinite deficit (for example, eventually below `Λ` with finitely many exceptions). There the near-null regime allows an atom of the Weil measure at `t = 0` (the half-pole mechanism of L149).

## Log
- 2026-09-30 — L157: conjecture, paper proof and Lean module in one cycle; moved to 3-formalized.
