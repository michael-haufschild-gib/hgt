# Random discrete Weil-positive systems: the granularity threshold is exactly 1/4

- **ID:** weil-random-discrete-granularity-threshold
- **Stage:** 3-formalized for the two integer-relevant endpoints: existence at `κ = 2^{−26}` and almost-sure failure at `κ = 1`, the integer granularity. The sharp constant `1/4` (Theorem A for all `κ < 1/4`, Theorem B for all `κ > 1/4`) is paper only.
- **Type:** THEOREM (paper), two directions
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, entry L176. It sharpens the heuristic `κ < 1/8` of L131.
- **Lean.** Axioms of both theorems: `propext`, `Classical.choice`, `Quot.sound`.
  - Existence: `RHTower.RandomCellWeil.exists_cellSum_lt_archDensity`, in `RHTower/{JitteredCellWeilTerms, JitteredCellWeilHoeffding, JitteredDiscreteWeilPositive}`.
  - Supercriticality at `κ = 1`: `RHTower.RandomCellWeil.ae_exists_archDensity_lt_cellSum_one`, in `RHTower/{JitteredUnitCellIntegrals, JitteredUnitCellVariance, JitteredUnitCellLaplace, JitteredUnitCellPartition, JitteredUnitCellSupercritical}`.
- **Statement:** Put one uniformly random point in each cell of length `κ` of `(1, ∞)` and give each point mass `κ`, minus the L131 correction atom. For ζ's archimedean datum, the Weil density is almost surely positive at all large heights when `κ < 1/4`. It is almost surely negative at arbitrarily large heights when `κ > 1/4`. For `N` large, a configuration with `κ = 1/N` is Weil-positive at every height with probability close to one.

## Setting

- `N ∈ ℕ`, `κ = 1/N`. Cells `I_k = [a_k, a_k + κ)` with `a_k = 1 + κk`, `k ≥ 0`.
- `U_k` are i.i.d. uniform on `[0, 1]`, and `x_k = a_k + κU_k`.
- `λ_ω = κ Σ_k δ_{x_k} − c₀ δ_{x₀}`, with `c₀ = e^{1/20000}` and `x₀ = e^{1/10000}` (so `c₀ x₀^{−1/2} = 1`).
- `E λ_ω = 1_{(1,∞)} dx − c₀ δ_{x₀}` is exactly the L131 producer (MUST-523).

**Weil function.** For `Re s > 1`,
`D_ω(s) = κ Σ_k x_k^{−s} − c₀ x₀^{−s} = 1/(s−1) + F_ω(s) − c₀ x₀^{−s}`,
where
`F_ω(s) = Σ_k ∫_{I_k} (x_k^{−s} − x^{−s}) dx`.
Each term has modulus `≤ κ² |s| a_k^{−Re s − 1}` (mean value theorem on a cell of length `κ`), so `F_ω` is holomorphic on `Re s > 0`. Hence
`Φ_ω = G + 1/s + 1/(s−1) − D_ω = ½ψ(s/2 + 1) − ½ log π + c₀ x₀^{−s} − F_ω(s)`,
holomorphic on `Re s > 0`, where `G = ½ψ(s/2) − ½ log π` and `½ψ(s/2) + 1/s = ½ψ(s/2+1)`.

The Weil density on the critical line is `ρ_ω(t) = 2 Re Φ_ω(½ + it) = 2[d₀(t) − f_ω(t)]`, where:
- `d₀(t) = ½ Re ψ(5/4 + it/2) − ½ log π + cos(t/10⁴)`, which is `≥ 1/200` (Lean, L131) and `≥ ½ log(|t|/2) − 2` for `|t| ≥ 4800`;
- `f_ω(t) = Re F_ω(½ + it)`.

Weil positivity of `λ_ω` is `ρ_ω ≥ 0`, as in L131: the Weil functional of `φ = g ⋆ g̃` equals `(1/2π)∫ φ̂ ρ_ω` by the contour argument, since `Φ_ω` is holomorphic on `Re s > 0` with logarithmic growth. The spectrum is absolutely continuous, with a real-analytic density.

**Cell variables.** `f_ω(t) = Σ_k Y_k(t)`, where `Y_k(t) = κ Re x_k^{−s} − Re ∫_{I_k} x^{−s} dx` (`s = ½ + it`). The `Y_k(t)` are:
- independent in `k`;
- mean zero: `κ E x_k^{−s} = ∫_{I_k} x^{−s} dx` because `x_k` is uniform on `I_k`;
- bounded: `|Y_k(t)| ≤ r_k(t) := min(2κ a_k^{−1/2}, κ² |s| a_k^{−3/2})`.

Note that `Σ_k r_k(t) ≤ C √|s| < ∞`.

## Theorem A (subcritical: `κ < 1/4`)

**Statement.**
1. If `κ < 1/4`, then almost surely there is `T₀(ω)` with `ρ_ω(t) > 0` for all `|t| ≥ T₀`.
2. For every `ε > 0` there is `N₀` such that for `N ≥ N₀`: `P(ρ_ω(t) > 0 for all t ∈ ℝ) ≥ 1 − ε`.
3. In particular, there are Weil-positive systems for ζ's archimedean datum supported on a discrete subset of `(1, ∞)`, with one atom per cell of length `κ` plus one correction atom. Their Weil measure is absolutely continuous.

**Proof.**
1. *Variance.* Let `v_k = Var Y_k(t)`. For the uncentred second moment of the first term,
   `κ² E[x_k^{−1} cos²(t log x_k)] = (κ/2) log(1 + κ/a_k) + (κ/2) ∫_{I_k} cos(2t log x) dx/x`.
   The last integral telescopes over cells into `[sin(2t log x)/(2t)]`. Split the cells at `A = |t|/log|t|` and `B = κ|t|`:
   - `a_k ≤ A`: the sum is at most `(κ/2) log(1 + A) + 1/log|t|`;
   - `A < a_k ≤ B`: use `v_k ≤ κ²/a_k`, which gives at most `κ log⁺(κ log|t|) + κ`;
   - `a_k > B`: use `v_k ≤ κ⁴ |s|² a_k^{−3}`, which gives at most `κ`.

   Hence `σ²(t) := Σ_k v_k ≤ (κ/2) log|t| + κ log⁺(κ log|t|) + 2κ + 1/log|t|`.

   For the lower bound, subtract `m_k² ≤ 4(a_k + κ)/t²` on the cells `a_k ≤ A`, which costs at most `2A²/(κt²)`. So `σ²(t) ≥ (κ/2) log|t| − (κ/2) log log|t| − O(1/(κ log²|t|))`.
2. *Cumulants.* Write `E e^{λY} = 1 + λ²v/2 + R` with `|R| ≤ |λ|³ r v e^{|λ| r}/6` (use `|Y|³ ≤ rY²`). Then for `|λ| ≤ Λ₀`,
   `|log E e^{λ Y_k} − λ² v_k/2| ≤ C(Λ₀) (r_k v_k + v_k²)`.
   Moreover `Σ_k r_k v_k ≤ Σ r_k³ ≤ 16κ²` and `Σ_k v_k² ≤ Σ r_k⁴ ≤ 32κ³`. The series `f_ω` converges uniformly in `ω` (because `Σ r_k < ∞`), so dominated convergence gives `E e^{λ f(t)} = Π_k E e^{λ Y_k(t)}`, and
   `log E e^{λ f(t)} = λ² σ²(t)/2 + O_{Λ₀}(κ²)`.
3. *Chernoff.* Fix `t ∈ [T, 2T]`, `u = ½ log T − 4` and `λ = u/σ²(t) ≤ 2/κ`. Then
   `P(f(t) ≥ u) ≤ exp(−u²/(2σ²) + C_κ) ≤ C'_κ T^{−1/(4κ) + o(1)}`.
4. *Net.* The derivative `f'(t) = Σ_k Y_k'(t)` is again a sum of independent, mean-zero variables with `|Y_k'| ≤ r_k log(a_k + κ) + κ² a_k^{−3/2}`. Its Hoeffding proxy is `O(κ log³ T)`, so
   `P(|f'(t)| ≥ log³ T) ≤ 2 exp(−c log³ T/κ)`.
   The second derivative obeys the deterministic bound `|f''| ≤ C √T log² T` on `[T, 2T]`. A net of spacing `1/T` (`T²` points) therefore gives `sup_{[T,2T]} |f'| ≤ log³ T + 1` outside probability `T^{−ω(1)}`. A second net of spacing `1/(4 log³ T)` (`O(T log³ T)` points) then gives `sup_{[T,2T]} f ≤ max_net f + ½`.
5. *Union bound.* `P(sup_{[T,2T]} f ≥ ½ log T − 3) ≤ C T^{1 − 1/(4κ) + o(1)}`, which is summable over `T = 2^j` exactly when `κ < 1/4`. By Borel–Cantelli, almost surely `f(t) < ½ log|t| − 3 < d₀(t)` for all large `t > 0`. The same holds for `t < 0` because `f(−t) = f(t)`. This proves (1).
6. *All heights.* For `|t| ≤ N/1200`, the deterministic bound `|f(t)| ≤ Σ_k κ² |s| a_k^{−3/2} ≤ 3κ|s| ≤ 1/400` gives `ρ_ω(t) ≥ 1/100`. For `|t| ≥ N/1200`, the bound from step 5, summed over dyadic `T ≥ N/2400`, tends to `0` as `N → ∞`. For the existence claim it is simplest to replace step 3 by Hoeffding (proxy `Σ r_k² ≤ 4κ(2 + log|s|)`) with κ small. This proves (2), and (3) follows. ∎

## Theorem B (supercritical: `κ > 1/4`)

**Statement.** If `κ > 1/4`, then almost surely `limsup_{T→∞} (log T)^{−1} max_{t∈[T,2T]} f_ω(t) ≥ √κ`. Hence `ρ_ω(t) < 0` for arbitrarily large `t`: almost surely `λ_ω` is not Weil-positive, not even at large heights. Combined with the upper bound of Theorem A's proof, the growth is exactly `max_{[T,2T]} f_ω ~ √κ log T`.

**Proof.**
1. *Covariance.* Put `Δ = t − t'` and `S = t + t'`. The identity
   `κ² E[x^{−1} cos(t log x) cos(t' log x)] = (κ/2) ∫_{I_k} [cos(Δ log x) + cos(S log x)] dx/x`
   is exact on every cell. Summing over `a_k ≤ κT·C`:
   - the `Δ`-part telescopes to `(κ/2) sin(Δ log B′)/Δ`;
   - the `S`-part is `O(1/T)`;
   - `Σ |m_k m'_k| = O(κ)`, using `|m_k| ≤ min(κ a^{−1/2}, 2(a+κ)^{1/2}/|t|)`;
   - the smooth cells contribute `O(κ)`.

   Hence `|Cov(f(t), f(t'))| ≤ κ/(2|Δ|) + Cκ`, and `ρ(Δ) := Cov/σ² ≤ min(1, (|Δ| log T)^{−1} + C/log T)`.
2. *Partition functions.* Let `W_λ = ∫_T^{2T} e^{λ f(t)} dt` and `λ_c = 2/√κ`.
   - By step 2 of Theorem A (lower bounds included), `E W_λ = T exp(λ²σ²/2 + O(1))`, with `σ² = (κ/2) log T + O(log log T)`.
   - *Far pairs* `|Δ| ≥ 1`: the cumulant bound for `Y_k(t) + Y_k(t')` and step 1 give `E e^{λ(f(t)+f(t'))} ≤ K · E e^{λ f(t)} · E e^{λ f(t')}`.
   - *Near pairs* `|Δ| < 1`: use the truncation `W^{tr} = ∫ e^{λ f} 1{f ≤ v}` with `v = λσ²(1+ε)`. The bound `e^{λ(f+f')} 1{f, f' ≤ v} ≤ e^{λ'(f+f')} e^{2(λ−λ')v}` with the optimal `λ' = v/(σ²(1+ρ))` gives an excess factor `exp(λ²σ² ρ/(1+ρ))`. Integrated over `|Δ| < 1`, its total relative to `T²e^{λ²σ²}` is `O(T^{λ²κ/4 − 1})`, which tends to `0` for `λ < λ_c`.
   - *Truncation loss:* `E[∫ e^{λf} 1{f > v}] ≤ e^{−σ²λ²ε²/2} E W_λ`.
   - Hence `E(W^{tr})² ≤ K (E W^{tr})²`. Paley–Zygmund gives `P(W_λ ≥ ½ E W^{tr}_λ) ≥ 1/(16K)` for `λ < λ_c`.
3. *Two temperatures.* `λ ↦ log W_λ` is convex with derivative `≤ max f`. Take `λ₂ = (1−η)λ_c` and `λ₁ = λ₂ − σ^{−1}`. Use Paley–Zygmund at `λ₂` and Markov at `λ₁` (`P(W_{λ₁} > C' E W_{λ₁}) ≤ 1/C'`). With probability at least `1/(16K) − 1/C' > 0`,
   `max_{[T,2T]} f ≥ (log W_{λ₂} − log W_{λ₁})/(λ₂ − λ₁) ≥ λ₂ σ² − O(σ) = (1 − η)√κ log T − o(log T)`.
4. *Zero–one law.* Changing finitely many `U_k` changes `f` by a bounded function of `t`, because `|Y_k| ≤ 2κ a_k^{−1/2}`. So `{limsup (log T)^{−1} max_{[T,2T]} f ≥ (1−η)√κ}` is a tail event. It has probability `≥ limsup_T P(·) ≥ 1/(16K) − 1/C' > 0` by reverse Fatou, hence probability `1` by Kolmogorov's law. Let `η → 0`.
5. For `κ > 1/4` we have `√κ > ½`, so `f(t) > ½ log t + 3 > d₀(t)` for arbitrarily large `t`. ∎

## What is new

- **A sharp granularity threshold for Weil positivity.** For random discrete supports, positivity for ζ's archimedean datum at large heights holds exactly below `κ_c = 1/4`.
  - The constant is `(archimedean slope)² = (½)²`: the maximum of the fluctuation is `√κ log T` (a random-energy-model maximum over `≍ T log T` decorrelated heights, each with variance `(κ/2) log T`), and the ceiling is `θ'(t) ~ ½ log t`.
  - L131 conjectured `1/8` from a Hoeffding-type heuristic; the exact constant is `1/4`, and both directions are proved.
- **Discrete producers exist** (Theorem A(3)): the first atomic-support Weil-positive systems for ζ's datum.
  - They have *continuous* spectrum, so the analogue of Conjecture Ω fails on random discrete supports.
  - Any proof of Ω must use the arithmetic of ℕ, not only discreteness, unit mass density and the pole.
- **Integers sit at `κ = 1 = 4κ_c`.**
  - Generic discrete systems at integer granularity fail positivity almost surely (Theorem B), overshooting the ceiling by the factor `√κ/(½) = 2`.
  - Deterministic lattices fail for every `κ` through resonance: `κ^{1−s}ζ(s, ·)` has the large values of Hurwitz/Dirichlet L-functions.
  - `Λ` survives at granularity `log p` only through exact phase-locking: `Re(−ζ'/ζ)(½+it) = θ'(t)` off the zeros.
  - So producers at integer granularity are necessarily non-generic. This is a rigorous random-model form of the uniqueness heuristic (L131′, Ω).
- **Ω as derandomization at the `α ≥ 1` wall.** Theorem B is exactly what Ω asserts for integer supports, with the randomness over `ω` replaced by randomness over `t` (Bohr–Jessen). The only gap is effective equidistribution of `≍ T` frequencies at height `T`, which is the `α ≥ 1` wall.
- **Degree remark [heuristic].** For a datum with archimedean slope `d/2` (e.g. `Γ_ℝ(s)^d`) and pole weight one, the same proof gives `κ_c = d²/4`, provided that datum has a positive continuous baseline analogous to L131. Integer granularity would then be critical for `d = 2` and subcritical for `d ≥ 3`.

## Gates
- [x] 0 → 1: mechanism (one-sided large deviations of a random-energy-model field against the archimedean ceiling)
- [x] 1 → 2: paper proofs above (Theorem A via Chernoff with exact cumulants and a two-level net; Theorem B via truncated second moment, two temperatures and the zero–one law)
- [x] 2 → 3 (endpoints): Theorem B at `κ = 1` is formal (`ae_exists_archDensity_lt_cellSum_one`):
  - exact cell cumulants (`log_mgf_field_le/ge`, `log_mgf_field_pair_le`);
  - variance `½ log t + O(1)` (`fieldVar_ge/le`) and bounded covariance at separation `≥ 1` (`abs_fieldCov_le`);
  - discrete partition functions on the integer net, with second moment `≤ (C+1)(E W)²` (`integral_partW_sq_le`);
  - Paley–Zygmund and Markov at `λ = 6/5, 11/10`;
  - Kolmogorov's zero–one law on the clamped excess event (`measure_excessEvent`).

  Theorem A(3) is formal: `exists_cellSum_lt_archDensity`, with `N = 2^26`. The formal proof has four parts:
  - Hoeffding (`measureReal_sum_cellTerm_ge_le`) on `Measure.infinitePi` of uniform laws;
  - a variance proxy `4(b+5)/N` (`sum_radius_sq_le`);
  - nets of spacing `2^{−(4b+34)}` on the dyadic blocks `b ≥ 15`;
  - the union bound `≤ 1/2`.

  The finite sums are atoms minus Lebesgue measure (`sum_range_cellTerm_eq`). Theorem A(1) at the sharp constant and Theorem B are paper only (they need exact cumulant bounds, the truncated second moment and the zero–one law).

## Log
- 2026-09-30: L176. Card created with both proofs. Existence formalized (three modules, 1321 lines), wired into `RHTower`, standard axioms.
- 2026-09-30: L177. Almost-sure failure at integer granularity `κ = 1` formalized (five modules, about 2300 lines), wired into `RHTower`, standard axioms. Card moved to stage 3.
