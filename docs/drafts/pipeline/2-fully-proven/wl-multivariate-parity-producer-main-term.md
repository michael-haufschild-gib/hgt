# Multivariate parity-selective integer auxiliaries reach the prime-number-theorem main term by vanishing order alone

- **ID:** wl-multivariate-parity-producer-main-term
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-3110/obstacles-summary.md §2.5.4 (Route WL) · docs/reports/researchlogs/big-pictures.md
- **Statement:** Multivariate, parity-selective integer Hecke–factorial auxiliaries reach normalized vanishing-order slope `< 1 + ε` for every `ε > 0`, yielding `ψ(x) ≤ (1 + ε) x + C_ε (log x)^2` unconditionally by `p`-adic vanishing order alone and strictly beating the univariate integer-Chebyshev ceiling (`< 87/100`), the single-prime Hecke ceiling (`2 log 2`), the universal finite-prime alphabet ceiling (`> 1 + 1/((P_S + 1)(P_S + 2))`), and the parity-blind multinomial ceiling (`> 31/30`).

## Goal
Resolve §2.5.4 of `obstacles-summary.md` completely and unconditionally, together with the sharp structural boundaries separating univariate `[0, 1]` polynomials, single-prime Hecke auxiliaries, finite-prime multivariate Hecke auxiliaries, parity-blind multinomial auxiliaries, and general multivariate parity-selective integer auxiliaries.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean modules in `GaloisForLFunctions.ArithmeticKreinLangerTheory`, `lake --old env lean` green, `#print axioms` clean

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
   Therefore `\frac{89}{81} b_k \le (\frac{89}{81} b_3)^{2^{k-3}} < (2.382)^{2^k}`, and `2.382 < 1 + 0.87 + \frac{0.87^2}{2} + \frac{0.87^3}{6} + \frac{0.87^4}{24} \le e^{87/100}` yields `b_k < e^{(87/100) \cdot 2^k}` for every `k ≥ 0`.
4. **Resultant pigeonhole lower bound.** Let `P ∈ ℤ[X] \setminus \{0\}` have `\deg P \le n` (`n ≥ 1`). Since `P` has at most `n` real roots and `Z_0, \dots, Z_n` are `n + 1` pairwise disjoint subsets of `(0, 1)`, some `k ≤ n` satisfies `Z_k \cap \mathrm{Roots}(P) = \emptyset`. By `Polynomial.resultant_map_map` and `Polynomial.resultant_eq_prod_eval`,
   $$1 \le |\mathrm{Res}_{2^k, n}(F_k, P)| = b_k^n \prod_{\alpha \in Z_k} |P(\alpha)| \le b_k^n \Bigl(\sup_{x \in [0, 1]} |P(x)|\Bigr)^{2^k},$$
   so `\sup_{x \in [0, 1]} |P(x)| \ge b_k^{-n / 2^k} > e^{-(87/100) n}`. Restricting `Q ∈ ℤ[X_1, \dots, X_d]` of total degree `\le n` to the diagonal `(t, \dots, t)` yields the identical lower bound on `[0, 1]^d` whenever `Q(t, \dots, t) \not\equiv 0`.

### 2. Exact Ledger and Sharp Obstructions for Hecke–Factorial Auxiliaries `[PROVED HERE]`

By unique prime factorization (`\mathbb{N}_{>0} \simeq \bigoplus_{p} \mathbb{N}`), multivariate polynomials `Q \in \mathbb{Z}[X_p : p\text{ prime}]` in the commuting prime dilation operators correspond bijectively to finitely supported integer stencils `c : \mathbb{N} \to_0 \mathbb{Z}` with `c(0) = 0`. Define:
- `\mathrm{IsBalanced}(c)`: `\sum_{k \in \mathrm{supp}(c)} c(k)/k = 0`;
- `\mathrm{stepWeight}(c, m) = \sum_{k \in \mathrm{supp}(c)} c(k) \lfloor m / k \rfloor \in \mathbb{Z}`;
- `\mathrm{stencilSlope}(c) = -\sum_{k \in \mathrm{supp}(c)} \frac{c(k) \log k}{k} \in \mathbb{R}`;
- `\mathrm{stencilNum}(c, n) = \prod_{c(k) > 0} (\lfloor n / k \rfloor!)^{c(k)}`, `\mathrm{stencilDen}(c, n) = \prod_{c(k) < 0} (\lfloor n / k \rfloor!)^{-c(k)}`.

1. **Exact integrality equivalence.** By Legendre's formula (`padicValNat_factorial`) and `\lfloor \lfloor n/k \rfloor / p^i \rfloor = \lfloor \lfloor n/p^i \rfloor / k \rfloor`, for every prime `p`,
   $$v_p(\mathrm{stencilNum}(c, n)) - v_p(\mathrm{stencilDen}(c, n)) = \sum_{i = 1}^{n} \mathrm{stepWeight}(c, \lfloor n / p^i \rfloor).$$
   If `\mathrm{stepWeight}(c, m) \ge 0` for all `m \ge 1`, every right-hand side is nonnegative, so `\mathrm{stencilDen}(c, n) \mid \mathrm{stencilNum}(c, n)` for all `n`. Conversely, if `\mathrm{stepWeight}(c, m_0) < 0` for some `m_0 \ge 1`, choosing a prime `p > m_0` and `n = p m_0` gives `\lfloor n / p \rfloor = m_0` and `\lfloor n / p^i \rfloor = 0` for `i \ge 2`, so `v_p(\mathrm{num}) - v_p(\mathrm{den}) = \mathrm{stepWeight}(c, m_0) < 0` and `\mathrm{stencilDen}(c, p m_0) \nmid \mathrm{stencilNum}(c, p m_0)`.
2. **Vanishing-order upper producer.** Let `\mathrm{IsBalanced}(c)`, `\mathrm{stepWeight}(c, r) \ge 0` for all `r`, and `\mathrm{stepWeight}(c, r) \ge m \ge 1` for `1 \le r < B` (`B \ge 2`). Set `A_n = \mathrm{stencilNum}(c, n) / \mathrm{stencilDen}(c, n) \in \mathbb{N}_{>0}`. For every prime `p \in (n/B, n]`, `1 \le \lfloor n/p \rfloor < B`, so `v_p(A_n) \ge m`, i.e., `p^m \mid A_n`; `IntegralityProducesLinearCounts.sum_mul_log_le_log_of_dvd` yields `m(\theta(n) - \theta(\lfloor n/B \rfloor)) \le \log A_n`, and `chebyshevTransform_vonMangoldt` likewise gives `m(\psi(n) - \psi(\lfloor n/B \rfloor)) \le \log A_n`. Applying `log_factorial_sub_bounds` under `\mathrm{IsBalanced}(c)` bounds `\log A_n \le \mathrm{stencilSlope}(c) \cdot n + E_c (1 + \log n)` (`n \ge 1`), and `B`-adic telescoping `N_j = \lfloor \lfloor x \rfloor / B^j \rfloor` over `0 \le j \le \lfloor \log_B x \rfloor + 1` gives unconditionally
   $$\psi(x) \le \frac{\mathrm{stencilSlope}(c)}{m(1 - 1/B)} x + C_c (\log x)^2 \qquad (\forall x \ge 2).$$
3. **Pronic slope series.** For every `k \ge 1`, Abel summation over `1 \le r \le d K` gives `\sum_{r=1}^{\infty} \frac{r \bmod k}{k \, r(r+1)} = \frac{\log k}{k}` (`Real.tendsto_harmonic_sub_log`). Under `\mathrm{IsBalanced}(c)`, `\mathrm{stepWeight}(c, r) = -\sum_{k \ge 1} \frac{c(k)}{k} (r \bmod k)`, hence
   $$\mathrm{stencilSlope}(c) = \sum_{r = 1}^{\infty} \frac{\mathrm{stepWeight}(c, r)}{r(r + 1)}.$$
4. **Single-prime Hecke ceiling (`2 \log 2`).** If `\mathrm{supp}(c) \subseteq \{p_0^j : 0 \le j \le K\}` (`p_0` prime) and `\mathrm{IsBalanced}(c)`, then for `M \ge K`,
   $$\sum_{r = 0}^{M} \frac{\mathrm{stepWeight}(c, p_0^r)}{p_0^r} = \sum_{j = 0}^{K} c(p_0^j) \sum_{r = j}^{M} \frac{p_0^{r-j}}{p_0^r} = \sum_{j = 0}^{K} \frac{c(p_0^j)}{p_0^j}(M - j + 1) = -\sum_{j = 0}^{K} \frac{j \, c(p_0^j)}{p_0^j} = \frac{\mathrm{stencilSlope}(c)}{\log p_0}.$$
   Consequently, if `\mathrm{stepWeight}(c, r) \ge 0` everywhere and `\mathrm{stepWeight}(c, p_0^r) \ge m` for `0 \le r < R` (`R \ge 1`), then `\frac{\mathrm{stencilSlope}(c)}{m(1 - p_0^{-R})} \ge \frac{p_0 \log p_0}{p_0 - 1} \ge 2 \log 2`.
5. **Two-prime `{2, 3}` breakthrough.** The balanced stencil `c_{2,3} = e_1 - e_2 - e_3 - e_4 + e_{12}` (`1 - X_2 - X_3 - X_2^2 + X_2^2 X_3`) is `12`-periodic with `\mathrm{stepWeight}(c_{2,3}, r) \in \{0, 1\}`, equals `1` on `r \in \{1, 2, 3\}` (`B = 4, m = 1`), and has normalized slope `\frac{10}{9}\log 2 + \frac{1}{3}\log 3 < \frac{23}{20} = 1.15 < 2 \log 2`.
6. **Universal finite-prime coprime jump obstruction (`> 1`).** Let `S` be any finite set of primes and `P_S = \prod_{p \in S} p`. If every prime factor of every `k \in \mathrm{supp}(c)` lies in `S`, then for every `q \ge 2` with `\gcd(q, P_S) = 1`, no `k \in \mathrm{supp}(c) \setminus \{1\}` divides `q`, so `\lfloor q / k \rfloor = \lfloor (q - 1)/k \rfloor` for `k \ge 2` and `\mathrm{stepWeight}(c, q) - \mathrm{stepWeight}(c, q - 1) = c(1) = \mathrm{stepWeight}(c, 1)`. Under `\mathrm{stepWeight}(c) \ge 0` and `\mathrm{stepWeight}(c, r) \ge m > 0` on `1 \le r < B` (`B \ge 2`), taking `q_0 = P_S + 1 \ge 2` (`\gcd(q_0, P_S) = 1`) forces `\mathrm{stepWeight}(c, q_0) - m \cdot \mathbf{1}_{1 \le q_0 < B} \ge m`, whence by the pronic series
   $$\frac{\mathrm{stencilSlope}(c)}{m(1 - 1/B)} \ge 1 + \frac{1}{(1 - 1/B)(P_S + 1)(P_S + 2)} > 1 + \frac{1}{(P_S + 1)(P_S + 2)} > 1.$$
7. **Parity-blind / non-alternating multinomial obstruction (`> 31/30`).** Suppose `c(k) \le 0` for all `k \ge 2` (no positive numerator parity-cancellation terms at `k \ge 2`), `\mathrm{IsBalanced}(c)`, and `\mathrm{stepWeight}(c, r) \ge m > 0` for `1 \le r < B` (`B \ge 2`). Write `x_k = -c(k)/(k m) \ge 0` (`k \ge 2`), so `\sum_{k \ge 2} x_k (r \bmod k) \ge 1` on `1 \le r < B` and `\mathrm{stencilSlope}(c)/m = \sum_{k \ge 2} x_k \log k`:
   - If `B = 2`, `r = 1` gives `\sum_{k \ge 2} x_k \ge 1`, so `\frac{\mathrm{stencilSlope}(c)}{m(1 - 1/2)} \ge 2 \log 2 > \frac{31}{30}`.
   - If `3 \le B \le 6`, weights `(w_1, w_2) = (\log 2, \frac{\log 3 - \log 2}{2}) \ge 0` satisfy `w_1(1 \bmod k) + w_2(2 \bmod k) \le \log k` for all `k \ge 2`, so `\frac{\mathrm{stencilSlope}(c)}{m(1 - 1/B)} \ge \frac{\frac{1}{2}\log 6}{5/6} = \frac{3}{5}\log 6 > \frac{31}{30}` (`6^{18} > (2.72)^{31} > e^{31}`).
   - If `B \ge 7`, Sylvester weights `(w_1, w_2, w_6) = (\log 2, \frac{\log 3 - \log 2}{2}, \frac{\log 7 - \log 3}{6}) \ge 0` satisfy `w_1(1 \bmod k) + w_2(2 \bmod k) + w_6(6 \bmod k) \le \log k` for all `k \ge 2` (using `63 < 64` at `k = 4` and `1701 < 15625` at `k = 5`), so `\frac{\mathrm{stencilSlope}(c)}{m(1 - 1/B)} > w_1 + w_2 + w_6 = \frac{\log 504}{6} > \frac{31}{30}` (`504^5 > (2.72)^{31} > e^{31}`).

### 3. Main Theorem: Multivariate Parity-Selective Integer Auxiliaries Reach `1 + ε` `[PROVED HERE]`

Fix `\varepsilon > 0` and set `\varepsilon' = \min(\varepsilon/2, 1) > 0`.

1. **Finite-dimensional Farkas reduction and upward rational rounding.** For any `2 \le B \le L'` and `J = \{k \mid L' : k \ge 2\}`, consider the real linear system in `(x_k)_{k \in J}`:
   $$\sum_{k \in J} x_k \log k \le \Bigl(1 + \frac{\varepsilon'}{2}\Bigr)\Bigl(1 - \frac{1}{B}\Bigr), \quad \sum_{k \in J} x_k (r \bmod k) \ge 1 \;\;(1 \le r < B), \quad \sum_{k \in J} x_k (r \bmod k) \ge 0 \;\;(B \le r < L').$$
   By Fourier–Motzkin elimination on `J`, either a real solution `x` exists, or normalized dual weights `u_1, \dots, u_{L'-1} \ge 0` exist (`w_0 > 0` since `r \bmod L' = r \ge 1` at `k = L'`) satisfying:
   - **(D1)** `\sum_{r = 1}^{L' - 1} u_r (r \bmod k) = \log k` for every `k \mid L'` (`k \ge 1`);
   - **(D2)** `\sum_{r = 1}^{B - 1} u_r > (1 + \varepsilon'/2)(1 - 1/B)`.
   Whenever a real solution `x` exists, since `(r \bmod k) \ge 0` for all `r, k`, choosing `q_k \in \mathbb{Q}` with `x_k \le q_k \le x_k + \delta_{\mathrm{rat}}` (`\delta_{\mathrm{rat}} \sum_{k \in J} \log k < \frac{\varepsilon'}{2}(1 - 1/B)`) preserves all positivity and `[1, B)` inequalities; clearing denominators with `D = \prod_{k \in J} \mathrm{den}(q_k) \ge 1`, `z_k = D q_k \in \mathbb{Z}`, `c(k) = -k z_k` (`k \in J`), `c(1) = \sum_{k \in J} z_k`, and `m = D` produces an integer balanced stencil `c` (`L'`-periodic since `k \mid L'`) with `\mathrm{stepWeight}(c) \ge 0` everywhere, `\mathrm{stepWeight}(c) \ge m` on `[1, B)`, sign alternation on `k \ge 2` once `\varepsilon < 1/30` (by §2.7), and normalized slope `< 1 + \varepsilon`.
2. **Elimination of dual certificates via Möbius harmonic and sawtooth cancellation.** Take `T = 2^{\ell}` (`\ell \ge 8`, so `T \ge 256`), `B = T + 1`, `L_0 = \mathrm{lcm}(1, \dots, T + 1)`, `j_0 = 4 \ell` (`2^{j_0} = T^4`), and `L' = 2^J L_0` (`J > j_0 + 1`). Set `\delta_T = \sum_{b=1}^{T} \mu(b)/b` and define
   $$F_T(r) = -\sum_{b = 1}^{T} \frac{\mu(b)}{b} (r \bmod b) + \delta_T \bigl(r \bmod (T + 1)\bigr) = \sum_{b = 1}^{T} \mu(b) \lfloor r / b \rfloor - \delta_T (T + 1) \lfloor r / (T + 1) \rfloor.$$
   Since `1, \dots, T + 1` divide `L_0 \mid L'`, pairing **(D1)** with `F_T` gives
   $$\sum_{r = 1}^{L' - 1} u_r F_T(r) = \sum_{b = 1}^{T} \Bigl(-\frac{\mu(b) \log b}{b}\Bigr) + \delta_T \log(T + 1).$$
   - **Main block (`1 \le r \le T`):** `\lfloor r / (T + 1) \rfloor = 0` and `\sum_{b=1}^{T} \mu(b) \lfloor r / b \rfloor = 1`, so `F_T(r) = 1`.
   - **Region 1 (`T + 1 \le r < k_{j_0}`, `k_{j_0} = 2^{j_0}(T + 1) \mid L'`):** By `BezoutValuationIncidence.exists_abs_sum_coprime_moebius_fract_le` (`f = 1, c = 1`) and `exists_abs_coprimeMoebiusHarmonicSum_le_four` (`|\delta_T| \le K (1 + \log T)^{-4}`), together with `r \bmod (T + 1) \le r`, we have `|F_T(r)| \le \eta_T r` where `\eta_T = \frac{2 K}{(1 + \log T)^3} + \frac{1}{\sqrt{T}}`. Since `r \bmod k_{j_0} = r` on `r < k_{j_0}`, **(D1)** at `k_{j_0}` gives `\sum_{r = T+1}^{k_{j_0}-1} r u_r \le \log k_{j_0} \le 6 \log T`, bounding Region 1 by `6 \eta_T \log T = O((\log T)^{-2})`.
   - **Region 2 (`k_{j_0} \le r < 2^{J-1}(T + 1)`):** Once `|\delta_T| \le 1/2`, `|F_T(r)| \le 2 T` for all `r`. On each dyadic block `I_j = [2^j(T + 1), 2^{j+1}(T + 1))` (`j_0 \le j \le J - 2`), `k_{j+1} = 2^{j+1}(T + 1) \mid L'` and **(D1)** at `k_{j+1}` give `2^j(T + 1) \sum_{r \in I_j} u_r \le \log k_{j+1} \le (j + 2)\log(T + 1)`. By the telescoping identity `\sum_{i=0}^{K-1} \frac{A + i}{2^i} \le 2 A + 2`, summing over `j \ge j_0` (`2^{j_0} = T^4`) bounds Region 2 by `2 \log(T + 1) \cdot \frac{2 j_0 + 6}{T^4} = O((\log T)^2 / T^4)`.
   - **Region 3 (`2^{J-1}(T + 1) \le r < L'`):** **(D1)** at `L'` gives `\sum_{r \ge 2^{J-1}(T+1)} u_r \le \frac{J \log 2 + \log L_0}{2^{J-1}(T + 1)}`, bounding Region 3 by `\frac{2(J \log 2 + \log L_0)}{2^{J-1}} \to 0` as `J \to \infty`.

   By `RHTower.Sieve.tendsto_moebiusLogHarmonicPartial_one`, `\sum_{b=1}^{T} (-\mu(b) \log b / b) \to 1` as `\ell \to \infty`, while `\delta_T \log(T + 1) \to 0` and `(1 + \varepsilon'/2)(1 - 1/(T + 1)) \to 1 + \varepsilon'/2 > 1`. Choosing `\ell` and then `J` large refutes **(D2)**. Therefore the primal solution exists, establishing both the unconditional vanishing-order PNT upper bound `\psi(x) \le (1 + \varepsilon) x + C_{\varepsilon} (\log x)^2` for every `\varepsilon > 0` and the exact infimum `1` of normalized vanishing-order slopes.

## Log
- 2026-10-31 — created and proved in `2-fully-proven`
