# Multivariate parity-selective integer auxiliaries reach the prime-number-theorem main term by vanishing order alone

- **ID:** wl-multivariate-parity-producer-main-term
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3110/obstacles-summary.md` §2.5.4 (Route WL) · `docs/reports/researchlogs/big-pictures.md`
- **Statement:** Multivariate, parity-selective integer Hecke–factorial auxiliaries reach normalized vanishing-order slope `< 1 + ε` for every `ε > 0`, yielding `ψ(x) ≤ (1 + ε) x + C_ε (log x)^2` and `θ(x) ≤ (1 + ε) x + C_ε (log x)^2` unconditionally by `p`-adic vanishing order alone, with sharp infimum `inf ProducerSlopeSet = 1` (`1 ∉ ProducerSlopeSet`), strictly beating the univariate integer-Chebyshev ceiling (`> exp(-(87/100) n)` on `[0, 1]`), the single-prime Hecke ceiling (`≥ 2 log 2`), the universal finite-prime alphabet ceiling (`> 1 + 1 / ((P_S + 1)(P_S + 2))`), and the parity-blind multinomial ceiling (`> 31 / 30`).

## Goal
Resolve §2.5.4 of `obstacles-summary.md` completely and unconditionally in Lean 4, together with the exact hierarchy of obstructions separating univariate `[0, 1]` integer polynomials, single-prime Hecke auxiliaries, finite-prime multivariate Hecke auxiliaries, parity-blind multinomial auxiliaries, and general multivariate parity-selective integer auxiliaries.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean modules in `GaloisForLFunctions.ArithmeticKreinLangerTheory`, `lake --old env lean` green, `#print axioms` clean (`[propext, Classical.choice, Quot.sound]`)

## Mathematical Architecture and Proofs

### 1. Calibration of the Univariate and Cube Integer-Chebyshev Ceiling (A9) `[PROVED HERE]`

Define the Gorshkov–Wirsing rational map on `[0, 1]` by
$$R(u) = \frac{u(1 - u)}{1 - 3 u(1 - u)}$$
and the integer polynomial sequences `p_k, q_k, F_k ∈ ℤ[X]` by `p_0 = X`, `q_0 = 1`,
$$p_{k+1} = p_k (q_k - p_k), \qquad q_{k+1} = q_k^2 - 3 p_k (q_k - p_k), \qquad F_k = 2 p_k - q_k.$$

1. **Real iteration and inverse branches.** For `u ∈ [0, 1]`, `0 ≤ u(1 - u) ≤ 1/4`, so `1 - 3 u(1 - u) ≥ 1/4 > 0` and `R(u) ∈ [0, 1]`. By induction on `k`, `q_k(x) > 0`, `p_k(x) = R^{\circ k}(x) q_k(x)`, and `F_k(x) = (2 R^{\circ k}(x) - 1) q_k(x)` for all `x ∈ [0, 1]`. On `(0, 1)`, the two explicit branches
   $$L(y) = \frac{1}{2} - \sqrt{\frac{1 - y}{4(1 + 3 y)}} \in \Bigl(0, \frac{1}{2}\Bigr), \qquad U(y) = \frac{1}{2} + \sqrt{\frac{1 - y}{4(1 + 3 y)}} \in \Bigl(\frac{1}{2}, 1\Bigr)$$
   satisfy `R(L(y)) = R(U(y)) = y`, are injective, and have disjoint images. Setting `Z_0 = \{1/2\}` and `Z_{k+1} = L(Z_k) \cup U(Z_k)` gives `|Z_k| = 2^k` distinct roots of `F_k` in `(0, 1)`.
2. **Pairwise disjointness of root sets.** If `x ∈ [0, 1]` satisfies `R^{\circ k}(x) = 1/2`, then `R^{\circ (k+1)}(x) = R(1/2) = 1` and `R^{\circ m}(x) = 0 ≠ 1/2` for all `m ≥ k + 2`. Hence `Z_k \cap Z_m = \emptyset` for all `k ≠ m`.
3. **Degree and leading-coefficient growth.** By induction, `\deg p_k, \deg q_k \le 2^k`. Writing `p_k.\mathrm{coeff}(2^k) = -a_k` and `q_k.\mathrm{coeff}(2^k) = c_k` for `k ≥ 1` gives `(a_1, c_1) = (1, 3)` and `a_{k+1} = a_k(c_k + a_k)`, `c_{k+1} = c_k^2 + 3 a_k(c_k + a_k)`, with `|F_k.\mathrm{coeff}(2^k)| = b_k = 2 a_k + c_k` (`b_0 = 2, b_1 = 5, b_2 = 29, b_3 = 941`). Since `|Z_k| = 2^k` and `b_k > 0`, `F_k` has exact degree `2^k` and splits completely over `ℝ` with `Z_k` as its full root set. For `k ≥ 3`, `(a_3, c_3) = (100, 741)` satisfies `7 a_k ≤ c_k`, preserved inductively by `7 a_{k+1} = 7 a_k(c_k + a_k) ≤ c_k(c_k + a_k) ≤ c_{k+1}`, whence
   $$89 b_k^2 - 81 b_{k+1} = (c_k - 7 a_k)(8 c_k + 7 a_k) \ge 0.$$
   Therefore `\frac{89}{81} b_k \le (\frac{89}{81} b_3)^{2^{k-3}} < (2.382)^{2^k} < e^{(87/100) \cdot 2^k}`, so `b_k < e^{(87/100) \cdot 2^k}` for every `k ≥ 0`.
4. **Resultant pigeonhole lower bound.** Let `P ∈ ℤ[X] \setminus \{0\}` have `\deg P \le n` (`n ≥ 1`). Since `P` has at most `n` real roots and `Z_0, \dots, Z_n` are `n + 1` pairwise disjoint subsets of `(0, 1)`, some `k ≤ n` satisfies `Z_k \cap \mathrm{Roots}(P) = \emptyset`. By `Polynomial.resultant_map_map` and `Polynomial.resultant_eq_prod_eval`,
   $$1 \le |\mathrm{Res}_{2^k, n}(F_k, P)| = b_k^n \prod_{\alpha \in Z_k} |P(\alpha)| \le b_k^n \Bigl(\sup_{x \in [0, 1]} |P(x)|\Bigr)^{2^k},$$
   so `\sup_{x \in (0, 1)} |P(x)| \ge b_k^{-n / 2^k} > e^{-(87/100) n}`. Restricting `Q ∈ MvPolynomial σ ℤ` of total degree `\le n` to the diagonal `(t)_{i \in \sigma}` yields the identical lower bound on `[0, 1]^\sigma` whenever the diagonal restriction is nonzero.

### 2. Exact Ledger and Sharp Obstructions for Hecke–Factorial Auxiliaries `[PROVED HERE]`

By unique prime factorization (`\mathbb{N}_{>0} \simeq \bigoplus_{p} \mathbb{N}`), multivariate polynomials `Q \in \mathbb{Z}[X_p : p\text{ prime}]` in the commuting prime dilation operators correspond bijectively to finitely supported integer stencils `c : \mathbb{N} \to_0 \mathbb{Z}` with `c(0) = 0` (`mvPolyToStencil` / `stencilToMvPoly`). Define:
- `\mathrm{IsBalanced}(c)`: `\sum_{k \in \mathrm{supp}(c)} c(k)/k = 0`;
- `\mathrm{stepWeight}(c, m) = \sum_{k \in \mathrm{supp}(c)} c(k) \lfloor m / k \rfloor \in \mathbb{Z}`;
- `\mathrm{stencilSlope}(c) = -\sum_{k \in \mathrm{supp}(c)} \frac{c(k) \log k}{k} \in \mathbb{R}`;
- `\mathrm{stencilNum}(c, n) = \prod_{c(k) > 0} (\lfloor n / k \rfloor!)^{c(k)}`, `\mathrm{stencilDen}(c, n) = \prod_{c(k) < 0} (\lfloor n / k \rfloor!)^{-c(k)}`.

1. **Exact integrality equivalence.** By Legendre's formula (`padicValNat_factorial`) and `\lfloor \lfloor n/k \rfloor / p^i \rfloor = \lfloor \lfloor n/p^i \rfloor / k \rfloor`, for every prime `p`,
   $$v_p(\mathrm{stencilNum}(c, n)) - v_p(\mathrm{stencilDen}(c, n)) = \sum_{i = 1}^{n} \mathrm{stepWeight}(c, \lfloor n / p^i \rfloor).$$
   Thus `\mathrm{stencilDen}(c, n) \mid \mathrm{stencilNum}(c, n)` for all `n \in \mathbb{N}` if and only if `\mathrm{stepWeight}(c, m) \ge 0` for all `m \ge 1` (witnessing any negative `m_0` at `n = p m_0` for a prime `p > m_0` via `Nat.exists_infinite_primes`).
2. **Vanishing-order upper producer.** Let `\mathrm{IsBalanced}(c)`, `\mathrm{stepWeight}(c, r) \ge 0` for all `r`, and `\mathrm{stepWeight}(c, r) \ge m \ge 1` for `1 \le r < B` (`B \ge 2`). Set `A_n = \mathrm{stencilNum}(c, n) / \mathrm{stencilDen}(c, n) \in \mathbb{N}_{>0}`. For every prime power `p^j \in (n/B, n]`, `1 \le \lfloor n/p^j \rfloor < B`, so `v_p(A_n) \ge m \cdot \#\{j \ge 1 : p^j \le n\} - \dots`, giving `m(\psi(n) - \psi(\lfloor n/B \rfloor)) \le \log A_n`. Stirling bounds under `\mathrm{IsBalanced}(c)` give `|\log A_n - \mathrm{stencilSlope}(c) \cdot n| \le E_c (1 + \log n)` (`n \ge 1`), and `B`-adic telescoping yields unconditionally
   $$\psi(x) \le \frac{\mathrm{stencilSlope}(c)}{m(1 - 1/B)} x + C_c (\log x)^2 \qquad (\forall x \ge 2).$$
3. **Pronic slope series.** For every `k \ge 1`, Abel summation gives `\sum_{r=1}^{\infty} \frac{r \bmod k}{k \, r(r+1)} = \frac{\log k}{k}`. Under `\mathrm{IsBalanced}(c)`, `\mathrm{stepWeight}(c, r) = -\sum_{k \ge 1} \frac{c(k)}{k} (r \bmod k)`, hence
   $$\mathrm{stencilSlope}(c) = \sum_{r = 1}^{\infty} \frac{\mathrm{stepWeight}(c, r)}{r(r + 1)}.$$
4. **Single-prime Hecke ceiling (`2 \log 2`).** If `\mathrm{supp}(c) \subseteq \{p_0^j : 0 \le j \le K\}` (`p_0` prime) and `\mathrm{IsBalanced}(c)`, then `\sum_{r = 0}^{M} \mathrm{stepWeight}(c, p_0^r) p_0^{-r} = \mathrm{stencilSlope}(c) / \log p_0` for all `M \ge K`. Consequently, if `\mathrm{stepWeight}(c) \ge 0` and `\mathrm{stepWeight}(c, p_0^r) \ge m` for `0 \le r < R`, then `\frac{\mathrm{stencilSlope}(c)}{m(1 - p_0^{-R})} \ge \frac{p_0 \log p_0}{p_0 - 1} \ge 2 \log 2`.
5. **Two-prime `{2, 3}` breakthrough.** The balanced stencil `c_{2,3} = e_1 - e_2 - e_3 - e_4 + e_{12}` is `12`-periodic with `\mathrm{stepWeight}(c_{2,3}, r) \in \{0, 1\}`, equals `1` on `r \in \{1, 2, 3\}` (`B = 4, m = 1`), and achieves normalized slope `\frac{10}{9}\log 2 + \frac{1}{3}\log 3 < \frac{23}{20} = 1.15 < 2 \log 2`.
6. **Universal finite-prime coprime jump obstruction (`> 1`).** For any finite prime set `S` (`P_S = \prod_{p \in S} p`), every `S`-supported stencil jumps by `\mathrm{stepWeight}(c, 1)` at `q_0 = P_S + 1` (`\gcd(q_0, P_S) = 1`), forcing normalized slope `> 1 + \frac{1}{(P_S + 1)(P_S + 2)} > 1`. Since `c.support` is finite, no single stencil attains slope `1` (`1 \notin \mathrm{ProducerSlopeSet}`).
7. **Parity-blind / non-alternating multinomial obstruction (`> 31/30`).** Every balanced producer with `c(k) \le 0` for all `k \ge 2` satisfies normalized slope `> 31 / 30` uniformly in `B \ge 2` (by Sylvester's dual weights `(\log 2, \frac{\log 3 - \log 2}{2}, \frac{\log 7 - \log 3}{6})` at `r \in \{1, 2, 6\}`). Thus any producer with normalized slope `\le 31/30` must alternate in sign on `k \ge 2`.

### 3. Main Theorem: Multivariate Parity-Selective Integer Auxiliaries Reach `1 + ε` `[PROVED HERE]`

Fix `\varepsilon > 0`, set `\varepsilon' = \min(\varepsilon, 1/30) > 0` and `\varepsilon_0 = \varepsilon'/2`.

1. **Finite-dimensional Farkas reduction and upward rational rounding.** For `2 \le B < L'` and `J = (\mathrm{divisors}(L')).\mathrm{erase}(1)`, Fourier–Motzkin elimination (`finset_farkas`) proves that either the real divisor LP
   $$\sum_{k \in J} x_k \log k \le (1 + \varepsilon_0)\Bigl(1 - \frac{1}{B}\Bigr), \quad \sum_{k \in J} x_k (r \bmod k) \ge 1 \;\;(1 \le r < B), \quad \sum_{k \in J} x_k (r \bmod k) \ge 0 \;\;(B \le r < L')$$
   is feasible, or there exist dual weights `u_1, \dots, u_{L'-1} \ge 0` with `\sum_{r = 1}^{L'-1} u_r (r \bmod k) = \log k` for all `k \mid L'` (`k \ge 1`) and `\sum_{r = 1}^{B - 1} u_r > (1 + \varepsilon_0)(1 - 1/B)`. Upward rational rounding `x_k < q_k < x_k + \delta_{\mathrm{rat}}` preserves all `(r \bmod k) \ge 0` constraints and lifts any primal solution to a balanced, `L'`-periodic, sign-alternating integer producer `(c, m, B)` of normalized slope `< 1 + 2\varepsilon_0 = 1 + \varepsilon' \le 1 + \varepsilon`.
2. **Elimination of dual certificates via Möbius harmonic and sawtooth cancellation.** At dyadic scales `T = 2^{\ell}` (`\ell \ge 10`), `B = T + 1`, `L_0 = B!`, `j_0 = 4\ell` (`2^{j_0} = T^4`), and `L' = 2^M L_0`, pair the dual equalities with the balanced Möbius residue test
   $$F_T(r) = -\sum_{b = 1}^{T} \frac{\mu(b)}{b} (r \bmod b) + \delta_T \bigl(r \bmod (T + 1)\bigr), \qquad \delta_T = \sum_{b = 1}^{T} \frac{\mu(b)}{b}.$$
   - **Global identity:** `\sum_{r = 1}^{L'-1} u_r F_T(r) = \sum_{b = 1}^{T} (-\mu(b) \log b / b) + \delta_T \log(T + 1) \to 1` (`tendsto_moebiusLogHarmonicPartial_one` and `|\delta_T| \le K_2 (1 + \log T)^{-4}`).
   - **Main window (`1 \le r \le T`):** Möbius inversion gives `F_T(r) = \sum_{b = 1}^{T} \mu(b) \lfloor r / b \rfloor = 1`.
   - **Region 1 (`B \le r < 2^{4\ell} B`):** Sawtooth cancellation (`exists_abs_sum_coprime_moebius_fract_le`) gives `|F_T(r)| \le \eta_T r` with `\eta_T = O((\log T)^{-3})`, and Markov at `k_0 = 2^{4\ell} B \mid L'` gives `\sum r u_r \le \log k_0 \le 6\ell`, so the contribution is `O(1/\ell)`.
   - **Region 2 (`2^{4\ell} B \le r < 2^{M-1} B`):** Uniformly `|F_T(r)| \le 3 T`, and dyadic Markov blocks at `k_{j+1} = 2^{j+1} B \mid L'` sum geometrically via `\sum_{i < d} (A + i) 2^{-i} \le 2 A + 2` to `\le 84/\ell`.
   - **Region 3 (`2^{M-1} B \le r < L'`):** Markov at `L'` gives `\le 3(\log L') / 2^{M-1} \le \varepsilon_0 / 8` for `M` large.

   Choosing `\ell` and then `M` large refutes `\sum_{r = 1}^{B - 1} u_r > (1 + \varepsilon_0)(1 - 1/B)`, proving unconditional primal feasibility for every `\varepsilon_0 > 0`.

## Lean surface

Namespace `GaloisForLFunctions.ArithmeticKreinLangerTheory` (wired into `formal/GaloisForLFunctions/ArithmeticKreinLangerTheory.lean` and documented in `formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/README.md`):

1. `formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheUnivariateIntegerChebyshevCeiling.lean`:
   - `exists_Ioo_gt_univariate_chebyshev_cap`, `exists_Icc_gt_univariate_chebyshev_cap`;
   - `sup_certified_log_inv_lt`;
   - `natDegree_diagonal_mvPolynomial_le`, `exists_cube_gt_of_mvPolynomial_totalDegree_le`.
2. `formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/FinitePrimeHeckeAuxiliaryObstructions.lean`:
   - `mvPolyToStencil`, `stencilToMvPoly`, `mvPolyToStencil_stencilToMvPoly`, `stencilToMvPoly_mvPolyToStencil`;
   - `forall_stencilDen_dvd_stencilNum_iff`, `psi_le_of_stepWeight_producer`, `hasSum_stepWeight_div_pronic`;
   - `single_prime_hecke_slope_ge`, `single_prime_hecke_slope_ge_two_log_two`;
   - `twoThreeStencil`, `twoThreeStencil_slope_lt`, `psi_le_of_twoThreeStencil`;
   - `stepWeight_coprime_jump`, `finite_prime_alphabet_slope_gt_one`, `one_lt_normalized_slope_of_producer`;
   - `non_alternating_stencil_slope_gt`, `exists_sign_alternation_of_slope_le`.
3. `formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/MultivariateParityAuxiliariesReachTheMainTerm.lean`:
   - `finset_farkas`, `exists_stencil_of_real_lp`, `exists_real_lp_or_dual`, `exists_real_lp_solution`;
   - `exists_multivariate_parity_producer`, `exists_mvPolynomial_parity_producer`;
   - `psi_le_one_add_eps_of_vanishing_order`, `theta_le_one_add_eps_of_vanishing_order`;
   - `ProducerSlopeSet`, `isGLB_producerSlopeSet`, `one_notMem_producerSlopeSet`;
   - `exists_producer_escaping_prime_finset`, `multivariate_parity_resolution_of_chebyshev_ceiling`.

All three modules pass foreground `lake --old env lean` verification with zero warnings, zero raised heartbeat/recursion budgets, and `#print axioms` reporting only `[propext, Classical.choice, Quot.sound]`.
