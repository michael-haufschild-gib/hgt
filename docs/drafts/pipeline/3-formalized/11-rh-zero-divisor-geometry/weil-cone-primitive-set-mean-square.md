# Weil positivity bounds the weights in mean square on primitive sets

- **ID:** weil-cone-primitive-set-mean-square
- **Stage:** 3-formalized (MUST-591)
- **Source:** MC conjecture loop, cycle 176.
- **Theorem** (`RHTower.WeilMeanSquare.exists_sum_sq_div_le_of_primitive`). There is an absolute `C₀` such that every Weil-positive `lam` (with `ζ`'s archimedean term) satisfies
  `Σ_{n∈S} lam(n)²/n ≤ (log N + C₀)²`
  for every `N ≥ 1` and every primitive `S ⊆ [2, N]`, i.e. no element of `S` is a proper multiple of another.
- **Corollaries [L].**
  - `exists_sum_sq_Ioc_le_of_weilPositiveFull`, dyadic mean square: `Σ_{N<n≤2N} lam(n)² ≤ 2N(log 2N + C₀)²`.
  - `exists_sum_sq_prime_div_le`, prime mean square: `Σ_{p≤N} lam(p)²/p ≤ (log N + C₀)²`. `Λ` has `(½ + o(1)) log²N`, so this is sharp up to a factor 2.
  - `summable_abs_div_rpow_of_weilPositiveFull`: `Σ |lam(n)| n^{−σ} < ∞` for every `σ > 1`. This is exactly the `summable` field of `HerglotzWeilPositive`, so that field holds automatically on the Weil cone.
  - Other primitive sets give the same bound: `{n ≤ N : Ω(n) = k}` for each `k`, and every primitive set (Erdős sense) inside `[2, N]`.

## Phase 1–4
- **Starting point.** The corpus's only size bound for cone members was the pointwise box `|lam(n)| ≤ √n(log n + C)`. HF's loop recorded that no universal upper density for Weil-positive weights was known ("the corpus had only cΛ", L52).
- **Mechanism: the star resonator.**
  - Take `c = δ₁ + t Σ_{n∈S} lam(n) n^{−1/2} δ_n`, a hub at `1` plus a primitive set of spokes.
  - Its multiplicative autocorrelation meets an atom `n ≥ 2` only through the pair `(n, 1)`. For `m ∈ S` the product `nm` is not in `S`, by primitivity, and `nm ≠ 1`.
  - So the multiplicative Toeplitz bound collapses to `2tQ ≤ (log N + C₀)(1 + t²Q)` with `Q = Σ_S lam(n)²/n`.
  - Optimizing over `t` gives `Q ≤ (log N + C₀)²`.
- **Kill attempts.**
  - *False?* No: `Λ` satisfies it, and the proof is complete.
  - *Circular?* No.
  - *Known?* The corpus has only signed bounds (pinning, Toeplitz density with `χ ≡ 1`) and the box. No mean-square bound for Weil-positive weights was found in the corpus search ("WeilPositive lam squared mean square dyadic bound primitive set"). The literature has no such notion.
  - *Insignificant?* No:
    - it is the first universal `ℓ²`/`ℓ¹` size law for the Weil cone;
    - it makes `Re s > 1` absolute convergence automatic;
    - it rules out large, dense composite deviations such as `|d(n)| ≍ n^θ` on sets of positive density.
- **Verdict.** SURVIVES.

## Phase 5 — paper proof
1. **Toeplitz inequality** (HF, `weil_multiplicativeToeplitz_bound`): `2Σ_{2≤n≤N} lam(n)n^{−1/2}Re Σ_m c(nm)c̄(m) ≤ (log N + C₀)Σ_m|c(m)|²` for `c` supported on `[1, N]`.
2. **Star resonator.** For `n ≥ 2`, `Σ_m c(nm)c̄(m) = c(n)`. The `m = 1` term gives `c(n)`. For `m ∈ S`, `c(nm) = 0` since `nm ∉ S ∪ {1}`. Other `m` have `c(m) = 0`. So the left side is `2tQ`, and `Σ|c|² = 1 + t²Q`.
3. **The constant `B = log N + C₀` is `≥ 0`.** Take `S = ∅`.
4. **Optimization.**
   - If `Q > 0` and `B > 0`: take `t = B/Q`. This gives `2B ≤ B + B³/Q`, hence `Q ≤ B²`.
   - If `B = 0`: taking `t = 1` gives `Q ≤ 0`.
5. **Dyadic mean square.** `(N, 2N]` is primitive. Then `Σ lam² ≤ 2N·Σ lam²/n`.
6. **Absolute convergence.**
   - On each block `(2^j, 2^{j+1}]`, AM–GM gives `2|x| ≤ x²/(L+1) + (L+1)`, so `Σ|lam| ≤ (3/2)2^j(L_j + 1)`.
   - Each block then contributes `≤ (3/2) r^j((j+1) log 2 + |C₀| + 1)`, with `r = 2^{1−σ} < 1`.
   - These bounds are summable, and the dyadic decomposition of `(1, 2^J]` finishes the proof. ∎

## Lean (formalized 2026-09-30)
Module `RHTower/WeilPrimitiveSetMeanSquare.lean`. It compiles clean under `lake env lean`, was built with `lake build --old`, `#print axioms` reports the standard three for all four headline theorems, it is wired into `RHTower.lean` after `WeilPrimeDeficitSetRigidity`, and the collision sweep is clean.
- `IsPrimitiveSet`, `exists_sum_sq_div_le_of_primitive`, `exists_sum_sq_Ioc_le`.
- `sum_abs_Ioc_le_of_sum_sq`, `sum_range_succ_eq_Ioc`, `summable_abs_div_rpow_of_weilPositive`.
- Full-cone corollaries: `summable_abs_div_rpow_of_weilPositiveFull`, `exists_sum_sq_prime_div_le`, `exists_sum_sq_Ioc_le_of_weilPositiveFull`.

## Significance
- **Every Weil-positive system is `Λ`-size in dyadic mean square, up to one logarithm.** `Σ_{n≤x} lam(n)² = O(x log² x)`, against `x log x` for `Λ`. Equivalently `Σ_{n≤x}|lam(n)| = O(x log x)`.
- **Consequences for (P2).** A second cone point's deviation obeys the same bounds. It cannot be large on a dense set, so the Ω core consists of `Λ`-size, sign-oscillating deviations, as HF's design space presumes. That presumption is now a theorem.
- **Consequence for the spectral programme.** The `summable` field of `HerglotzWeilPositive` is automatic. What remains open for a Lean proof of "Weil-positive ⇒ Herglotz" is only the continuation and positivity, i.e. Bochner–Schwartz.
- **Open refinement.** The dyadic bound is off by `log N` from `Λ`'s size. A hub larger than `{1}` might recover `Σ lam² ≪ N log N`.
