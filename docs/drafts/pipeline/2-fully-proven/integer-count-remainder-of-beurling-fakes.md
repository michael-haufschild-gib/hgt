# Least integer-count remainder of discrete integer-norm Beurling fakes

- **ID:** integer-count-remainder-of-beurling-fakes
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1111/obstacles-summary.md` §4, Question B182 (wall Γ230)
- **Statement:** Complete determination of the integer-count remainder exponent regimes for discrete integer-norm Beurling fakes, together with their structural obstructions and arithmetic calibrations:
  1. **Unconditional existence on `(1/2, 1)` (`exists_integerNormFakeAt_of_half_lt`):** For every `β ∈ (1/2, 1)`, there exists a discrete integer-norm Beurling system `B = keptPrimeSystem S` (a deterministic subset of the rational primes) not norm-equivalent to `Nat.Primes`, with density `A > 0`, `|(B.countBall x : ℝ) - A * x| ≤ C * x ^ β` for all `x ≥ 1`, and a holomorphic continuation `G` of `(s - 1) ζ_B(s)` on `{s : ℂ | 1 / 5 < s.re}` vanishing at `ρ₀ ∈ (1/2, β)` (as well as infinitely many periodic ordinates `ρ₀ + 2πim / log M`) where `ζ(ρ₀) ≠ 0`. Consequently `sInf {β ≥ 0 | ∃ B, IsIntegerNormFakeAt B β} ≤ 1 / 2` unconditionally.
  2. **Crossing `< 1/2` and unconditional frontier / World-I dichotomies (`exists_integerNormFakeAt_lt_half_of_zeroFree`, `zetaZeroAbscissa_eq_one_or_exists_integerNormFakeAt_lt_half`, `asymptoticAbscissaLaw_or_exists_integerNormFakeAt_lt_half`):** Whenever `ζ` is zero-free on `Re s > Θ` for some `Θ < 1` (in particular under `[X]: Θ ≤ 7/8`, and under `¬AsymptoticAbscissaLaw` in World I), square-root prime thinning `B = keptPrimeSystem D.S` yields a discrete integer-norm fake with `β = 1 / 2 - (1 - max Θ (3 / 4)) / 64 < 1 / 2` (and under `RiemannHypothesis`, every `β ∈ (1 / 3, 1)` is realized). Unconditionally in ZFC, either `zetaZeroAbscissa = 1` (hence `AsymptoticAbscissaLaw`), or there exists `β < 1 / 2` and a discrete integer-norm fake `B` at exponent `β`.
  3. **Sharp structural obstructions and quadratic `L`-function calibration (`pos_density_of_integerNormFakeAt_le_half`, `no_fake_of_finite_edit`, `no_pure_addition_fake_le_half`, `isIntegerNormFakeAt_half_of_quadratic_LFunction_zero`):**
     - Every discrete integer-norm fake at exponent `β ≤ 1 / 2` has strictly positive linear density `A > 0`.
     - Deleting finitely many rational primes and adding finitely many integer norms `≥ 2` yields `N_B(x) = A x + O((log x + 1)^K)` (`A > 0`) and preserves the exact zero set of `(s - 1) ζ(s)` on `Re s > 0` (never a fake).
     - Retaining all rational primes (`e ≤ 0`) with `N_B(x) = A x + O(x^β)` (`β ≤ 1 / 2`) produces no fake zeros in `Re s > 1 / 2`; every fake at `β ≤ 1 / 2` omits infinitely many rational primes.
     - For every nonprincipal real quadratic Dirichlet character `χ` mod `N`, the discrete integer-norm system `B_χ` satisfies `|(B_χ.countBall x : ℝ) - (L(1, χ)).re * x| ≤ C * x ^ (1 / 2)` and `(s - 1) ζ_{B_χ}(s) = ((s - 1) ζ(s)) L(s, χ)`; thus absence of discrete integer-norm fakes at `β = 1 / 2` forces every zero of `L(s, χ)` in `Re s > 1 / 2` to be a zero of `ζ(s)`.

## Definitions

A discrete Beurling system `B : RHTower.BeurlingSystem` is an **integer-norm fake at exponent `β`** (`IsIntegerNormFakeAt B β`) if:
1. `HasIntegerNorms B` and `B.IsDiscrete`;
2. `B` is not norm-equivalent to the rational primes: `¬ Nonempty {e : B.Label ≃ {p : ℕ // p.Prime} // ∀ l, B.labelNorm l = ((e l : ℕ) : ℝ)}`;
3. `∃ A C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β`;
4. `∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧ (∀ s : ℂ, 1 < s.re → B.zetaSeriesC s = G s / (s - 1)) ∧ ∃ ρ₀ : ℂ, 1 / 2 < ρ₀.re ∧ G ρ₀ = 0 ∧ riemannZeta ρ₀ ≠ 0`.

## Proofs

### 1. Kept-prime systems and elementary Rankin floor bound
For `S : Set ℕ`, `keptPrimeSystem S` has label type `KeptPrime S = {p : ℕ // p.Prime ∧ p ∉ S}` with `labelNorm p = p`. Unique factorization identifies `Multiset (KeptPrime S)` norm-preservingly with `{n : ℕ // SFree S n}`, giving `(keptPrimeSystem S).countBall x = ∑_{n ≤ ⌊x⌋₊} sFreeR S n` and `(keptPrimeSystem S).zetaSeriesC s = LSeries sFreeInd s` on `Re s > 1`. Whenever `S` contains at least one prime `p₀`, no norm-preserving bijection to `{p : ℕ // p.Prime}` exists since `p₀` is omitted from `labelNorm`.

If `S` consists of primes and `∑_{p ∈ S} p^{-β} < ∞` with `0 < β < 1`, let `μ_S` be the Möbius function supported on squarefree `S`-smooth integers. Then `∑_{m=1}^∞ |μ_S(m)| m^{-β} ≤ exp(∑_{p ∈ S} p^{-β}) =: M_β < ∞`, and `sFreeR S = 1 ⋆ μ_S` yields
$$N_B(x) = \sum_{1 \le m \le \lfloor x \rfloor_+} \mu_S(m) \left\lfloor \frac{x}{m} \right\rfloor = A x - x \sum_{m > \lfloor x \rfloor_+} \frac{\mu_S(m)}{m} - \sum_{1 \le m \le \lfloor x \rfloor_+} \mu_S(m) \left\{\frac{x}{m}\right\}$$
with `A = ∑_{m=1}^∞ μ_S(m)/m = ∏_{p ∈ S} (1 - 1/p) > 0`. Using `1 ≤ (x/m)^β` for `m ≤ x` and `1/m ≤ x^{β-1} m^{-β}` for `m > x` gives `|N_B(x) - A x| ≤ 2 M_β x^β` for all `x ≥ 1`.

### 2. Unconditional construction on `(1/2, 1)` via Moreau necklaces and short prime intervals
Given `β ∈ (1/2, 1)`, choose `b ∈ ℕ` (`b ≥ 4`) large enough that `β₀ := log(b + 1) / (2 log b) ∈ (1/2, min(β, 3/5))`, and set `M := b^2 ≥ 16`, `a := b + 1 ≥ 5`, so `M^{β₀} = a`.

For `k ≥ 1`, `ZMod k` acts by index translation on `ZMod k → Fin a` (`card = a^k`). Partitioning words by minimal positive period `d ∣ k` (closed under `Nat.gcd` via Bézout), the set `Prim a k` of primitive words has free `ZMod k`-orbits, so `u(a, k) := (Prim a k).card / k` satisfies `k · u(a, k) = (Prim a k).card`, `1 ≤ u(a, k) ≤ a^k`, and `∑_{d ∣ m} d · u(a, d) = a^m` for every `m ≥ 1`. Hence for `|z| < 1/a`,
$$\sum_{k=1}^\infty u(a, k)\bigl(-\log(1 - z^k)\bigr) = \sum_{m=1}^\infty \frac{1}{m}\left(\sum_{d \mid m} d\,u(a, d)\right) z^m = \sum_{m=1}^\infty \frac{a^m}{m} z^m = -\log(1 - a z),$$
and substituting `z = M^{-s}` gives `∏_{k=1}^∞ (1 - M^{-ks})^{u(a, k)} = 1 - a M^{-s}` for `Re s > β₀`.

By `RHTower.exists_theta_window_lower_seventeenThirtieths` at exponent `29/50 ∈ (17/30, 3/5)`, for all `k ≥ k₀` the interval `(M^k, M^k + (M^k)^{3/5}]` contains at least `u(a, k) ≤ (M^k)^{β₀}` distinct primes; since `M ≥ 16`, these intervals are pairwise disjoint. Choosing `S_k` of cardinality `u(a, k)` inside `(M^k, M^k + (M^k)^{3/5}]` for `k ≥ k₀` and `∑_{k < k₀} u(a, k)` distinct unused primes above `M^{k₀}` outside those subsets for `k < k₀`, set `S = ⋃_{k ≥ 1} S_k`.

For `k ≥ k₀`, `p ∈ S_k`, and `Re s = σ > 1/5`, `|M^{-ks} - p^{-s}| ≤ |s| (M^k)^{3/5 - σ - 1}` and `|1 - M^{-ks}| ≥ 1 - 16^{-1/5} > 1/3`, so
$$\sum_{p \in S_k} \left|\frac{1 - p^{-s}}{1 - M^{-ks}} - 1\right| \le 3 |s| (M^k)^{\beta_0 - 2/5 - \sigma}.$$
Since `β₀ - 2/5 < 1/5`, `E(s) := ∏_{k ≥ 1} ∏_{p ∈ S_k} (1 - p^{-s})/(1 - M^{-ks})` converges locally uniformly to a holomorphic nonvanishing function on `{Re s > 1/5}`. On `Re s > 1`, `(keptPrimeSystem S).zetaSeriesC s = ζ(s) (1 - a M^{-s}) E(s)`, so `G(s) = ζ_u(s) (1 - a M^{-s}) E(s)` is holomorphic on `{Re s > 1/5}`, vanishes at `ρ₀ = β₀ ∈ (1/2, β)` where `ζ(β₀) ≠ 0`, and `∑_{p ∈ S} p^{-β} ≪ ∑_k (M^k)^{β₀ - β} < ∞` gives `|N_B(x) - A x| ≤ C x^β`.

### 3. Crossing `< 1/2` from any zero-free frontier `Θ < 1`
Let `Θ ∈ [1/2, 1)` satisfy `∀ z, Θ < z.re → ζ(z) ≠ 0`. Set `Θ' = max Θ (3/4) ∈ [3/4, 1)`, `d = (1 - Θ') / 16 ∈ (0, 1/64]`, `α = 1/2 + d`, `σ₀ = 1/2 - d`, and choose `D : DeletionData α`.
- On `Re s ≥ σ₀`, `Re s ≥ α/2 + 3/16` gives `|D.eFactor s| ≪_κ (|t| + 2)^κ`, and `Re(s + 1 - α) ≥ 1 - 2d = Θ' + 14d > Θ` gives `|qFactor α s| ≪_κ (|t| + 2)^κ` by `RHTower.exists_invZeta_shift_data_of_zeroFree`. Smoothed Perron on `D.mobS` yields `|∑_{n ≤ X} D.mobS n| ≤ C_M X^{σ₀ + τ}` (`τ = d / 16`) and `|∑_n D.mobS n g(n/M)| ≤ K_1 M^{σ₀} lineMass g σ₀ ε`.
- On `σ₀ ≤ Re s ≤ 3/2`, `Re(s + 1 - α) ≥ 1 - 2d ≥ 1/2`, so `RHTower.exists_norm_riemannZeta_le_subconvex` at `η = d / 16` bounds `|ζ(s + 1 - α)| ≪ |t|^{(1/6 + η)(2d + η)/(1/2 + η)} ≤ |t|^{4d/5}`, giving `|L(λ_S, σ₀ + it)| ≪ (|t| + 3)^ε` with `ε = 9d / 10`. Test-function Perron and `exists_saw_decomposition` yield the block bound
  $$\left|\sum_m \mu_S(m) F(m/M) \psi(x/m)\right| \le K \left(M^{\sigma_0} (x/M)^{1/2 + \varepsilon} \Delta^{-1/2 - 2\varepsilon} + \Delta^{1 - \varepsilon} M^\alpha\right).$$
- Splitting `N'(x) = ∑_{m ≤ x} μ_S(m) ⌊x/m⌋` at `M₁ = x^{1 - 3d}` and `M₂ = x^{1 - d}` with constant smoothing width `Δ = x^{-d}` on the collar `[M₁, M₂]`:
  - `m ≤ M₁`: Rankin (`D.sum_norm_mobS_le` at `α + τ`) gives `O(x^{(1 - 3d)(1/2 + 17d/16)}) = O(x^{1/2 - d/4})`;
  - `M₁ ≤ M ≤ M₂`: `O(log x)` dyadic blocks each bounded by `O(x^{1/2 - 3d/8})`;
  - `m > M₂`: hyperbola reversal + Abel summation against `|∑_{n ≤ u} μ_S(n)| ≪ u^{1/2 - 15d/16}` gives `O(x M₂^{-1/2 - 15d/16}) = O(x^{1/2 - d/4})`.
Thus `|(keptPrimeSystem D.S).countBall x - A x| ≤ C x^{1/2 - d/4}` with `1/2 - d/4 < 1/2`, while `D.perronNum` is holomorphic on `{Re s > σ₀}` (`⊃ {Re s > 1/2}`) and vanishes at `α ∈ (1/2, 1)` where `ζ(α) ≠ 0`. Combining with `zetaZeroAbscissa ≤ 1` and `asymptoticAbscissaLaw_of_zetaZeroAbscissa_eq_one` yields the unconditional dichotomies.

### 4. Obstructions and quadratic `L`-function calibration
- **Zero-density obstruction:** If `(B.countBall x : ℝ) ≤ C x^β` with `β ≤ 1/2`, partial summation gives `Summable (fun g => (B.intNorm g)^{-s.re})` on `Re s > β`, hence `B.moebiusSeriesC s * B.zetaSeriesC s = 1` and `B.zetaSeriesC s ≠ 0` on `Re s > 1/2`.
- **Finite edits:** Deleting `D : Finset Nat.Primes` and adding `M : Multiset {q : ℕ // 2 ≤ q}` multiplies `ζ(s)` by `(∏_{p ∈ D} (1 - p^{-s})) / (∏_{q ∈ M} (1 - q^{-s}))`, holomorphic and nonvanishing on `Re s > 0`, while inductively convolving `N(x) = A x + O((log x + 1)^k)` with `{q^j : j ≥ 0}` (`q ≥ 2`) shifts `(A, k) ↦ (A/(1 - 1/q), k + 1)`.
- **Pure additions:** `RHTower.IntegerBeurling.abscissaOfAbsConv_logCoeff_le` forces absolute convergence of `L(logCoeff e, s)` on `Re s > β`, making `ratio a s = K exp(L(logCoeff e, s))` nonvanishing on `Re s > 1/2` when `β ≤ 1/2`.
- **Quadratic character system `B_χ`:** For `χ : DirichletCharacter ℂ N` (`χ ≠ 1`) with `∀ n, χ n = -1 ∨ χ n = 0 ∨ χ n = 1`, define prime-indexed labels with `2` labels of norm `p` when `χ(p) = 1`, `1` label of norm `p` when `χ(p) = 0`, and `1` label of norm `p^2` when `χ(p) = -1`. Prime-power Euler factors satisfy `(1 - p^{-s})^{-1}(1 - χ(p) p^{-s})^{-1}` in every case, identifying `B_χ.intCount n` with `(1 ⋆ χ)(n) ≥ 0` and `B_χ.zetaSeriesC s` with `ζ(s) L(s, χ)` on `Re s > 1`. Hyperbola splitting `∑_{a b ≤ x} χ(b)` at `√x` with `|∑_{b ≤ Y} χ(b)| ≤ N` and Abel tail `|∑_{b > √x} χ(b)/b| ≤ 2 N x^{-1/2}` gives `|N_{B_χ}(x) - L(1, χ) x| ≤ C x^{1/2}`.
