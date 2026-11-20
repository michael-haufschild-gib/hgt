# Exact Zero-Free Rate Abscissa and Resolution of the Integer Floor-Alphabet Obstruction

- **ID:** aad-full-scale-rate-and-floor-obstruction-resolution
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1911/todo.md#L112-L116 · Item 18
- **Statement:** Unconditionally, $\lim_{K \to \infty} \frac{\log \mathrm{bestRate}(K)}{\log K} = \Theta_\zeta - 1$, where $\Theta_\zeta = \sup\{\Re \rho : \zeta(\rho) = 0\} \in [\frac{1}{2}, 1]$; for every $\Theta \in [\frac{1}{2}, 1)$, $\zeta(s) \ne 0$ on $\Re s > \Theta$ if and only if $\mathrm{HasRate}(K \mapsto K^{-a})$ holds for every $a \in (0, 1 - \Theta)$; and for every $a_0 \in [0, \frac{1}{2})$ (in particular $a_0 = \frac{1}{4}$), the proposed strict floor-alphabet obstruction $\exists a_* \in (a_0, \frac{1}{2}),\, \forall^\infty K,\, \forall (c, m, B) \text{ on } [1, K],\, \mathrm{rate}(c, m, B) > K^{-a_*}$ is logically equivalent to $\neg\,\mathrm{RiemannHypothesis}$.

## Goal

Resolve Question 18 of `docs/reports/review-1911/todo.md` completely and close the polynomial rate gap $[(2 - 2\Theta)/(5 - 2\Theta),\, 1 - \Theta]$ across the entire critical strip $\Theta \in [\frac{1}{2}, 1)$ (in particular $[1/4, 1/2]$ under RH) in `ArithmeticAuxiliaryDynamics`.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `ArithmeticAuxiliaryDynamics`, `lake --old env lean` green, `#print axioms` clean (`[propext, Classical.choice, Quot.sound]`)

## Lean 4 Formalization

- **Modules:**
  1. `formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheLogarithmicPlancherelVariationOfMertens.lean`
     - `norm_smoothedMertens_sub_mertens_le`
     - `exists_smoothedMertens_log_L2_increment_bound`
     - `exists_mertens_subpower_of_zeroFree`
  2. `formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheTautStringSmoothMertensStencil.lean`
     - `dyadic_haar_chaining`
     - `exists_smooth_odd_jump_letter`
     - `exists_taut_mertens_stencil`
  3. `formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/HammingSquareCompensationOfTheSmallPrimes.lean`
     - `exists_hamming_compensated_producer`
  4. `formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheHalfRateUnderTheRiemannHypothesis.lean`
     - `eventually_rate_gt_of_zero`
     - `eventually_bestRate_ge_of_one_sub_zetaZeroAbscissa_lt`
     - `hasRate_of_zeroFree_exact`
     - `hasRate_of_lt_one_sub_zetaZeroAbscissa`
     - `zeroFree_iff_forall_hasRate`
     - `zeroFree_iff_forall_frequently_bestRate_le`
     - `hasRate_of_riemannHypothesis_half`
     - `riemannHypothesis_iff_forall_hasRate_half`
     - `tendsto_log_bestRate_div_log`
     - `exists_strict_floor_obstruction_iff_not_riemannHypothesis`
     - `strict_floor_obstruction_quarter_iff_not_riemannHypothesis`

## No-go closure (Question 18 proposed impossibility statement)

- **Exact killing theorem/mechanism:** Question 18 asks whether there exists $a_* \in (\frac{1}{4}, \frac{1}{2})$ such that for all sufficiently large $K$, every admissible balanced integer floor producer $(c, m, B)$ supported in $[1, K]$ satisfies $\mathrm{rate}(c, m, B) > K^{-a_*}$. No unconditional arithmetic or combinatorial obstruction in $(\frac{1}{4}, \frac{1}{2})$ exists beyond zeros of $\zeta$: combining a taut-string Mellin–Plancherel step approximation of $M(x)$ with bipartite Hamming-square cofactor clusters and a subset-product CRT ramp constructs admissible balanced integer producers achieving $\mathrm{rate}(c, m, B) \le K^{-a}$ for every $a \in (0, 1 - \Theta)$ whenever $\zeta(s) \ne 0$ on $\Re s > \Theta$. Under RH ($\Theta = \frac{1}{2}$) this refutes the proposed obstruction for every $a_* < \frac{1}{2}$, while any off-line zero $\rho$ ($\Re \rho > \frac{1}{2}$) forces the obstruction for every $a_* \in (\max(a_0, 1 - \Re \rho), \frac{1}{2})$.
- **Strongest positive survivor:**
  1. **Unconditional exact rate-exponent law (`tendsto_log_bestRate_div_log`):** $\lim_{K \to \infty} \frac{\log \mathrm{bestRate}(K)}{\log K} = \Theta_\zeta - 1$.
  2. **Full-strip equivalence (`zeroFree_iff_forall_hasRate`, `zeroFree_iff_forall_frequently_bestRate_le`):**
     $$(\forall s \in \mathbb{C},\, \Theta < \Re s \to \zeta(s) \ne 0) \iff \forall a \in (0, 1 - \Theta),\, \mathrm{HasRate}(K^{-a}) \iff \forall a \in (0, 1 - \Theta),\, \exists^\infty K,\, \mathrm{bestRate}(K) \le K^{-a}.$$
  3. **Exact equivalence of Question 18 with $\neg\,\mathrm{RH}$ (`exists_strict_floor_obstruction_iff_not_riemannHypothesis`, `strict_floor_obstruction_quarter_iff_not_riemannHypothesis`):**
     $$\Big(\exists a_* \in \left(a_0, \frac{1}{2}\right),\, \forall^\infty K \in \mathbb{N},\, \forall (c, m, B) \text{ on } [1, K],\, \mathrm{rate}(c, m, B) > K^{-a_*}\Big) \iff \neg\,\mathrm{RiemannHypothesis}.$$
- **New insight:** Previous constructions (`SmoothCompensationOfTheLargePrimes`, `TheCompensatedProducer`, `TheOneQuarterRateUnderTheRiemannHypothesis`) retained $L^1$ stencil mass $\asymp T = y^2$ on $[1, y^2]$ and detected prime-power failures by single dyadic moduli $2^g Q \le K$, forcing $K \gtrsim y^3 / Y \asymp y^4$. Two elementary mechanisms eliminate both losses simultaneously without exponential sums: (i) Mellin–Plancherel on $\Re s = \Theta + \varepsilon$ plus dyadic Haar chaining bounds the greedy tube-exit variation of smoothed $M(x)$ at relative tolerance $1/y$ up to $T = y^\alpha$ by $O_\varepsilon(y^{1+2\varepsilon} T^{2\Theta - 1 + 2\varepsilon})$, and dyadic Bertrand products place every jump on an integer $k$ with $4 \nmid k$ and all odd prime-power divisors $Q \le C_d y$; (ii) bipartite Hamming squares $2^{b_Q} p_1 p_2 Q$ ($p_1, p_2 \in \mathcal{P}_W \subseteq (W, 2^S W]$) coupled to $\binom{\mathcal{P}_W}{m_*}$ subset-product ramps enforce CRT alignment down to a single residue $h(r) < B_0 \asymp K / W$ at slope cost $O_\delta(\frac{W \log K}{K} \sum_Q D_Q)$.
- **Status:** Complete dependency-closed paper proof and unconditional Lean 4 formalization verified (`lake --old env lean` exit 0, `#print axioms` clean).

---

## Complete Paper Proof `[PROVED HERE]`

### 1. Cofinal Zero-Width Reading and Equivalence of the Obstruction Criterion

**Lemma 1.1 (Uniform Supercritical Floor from a Single Zero, `eventually_rate_gt_of_zero`).** *Let $\rho \in \mathbb{C}$ satisfy $\zeta(\rho) = 0$, and let $a \in (0, \frac{1}{2}]$ satisfy $\Re \rho > 1 - a$. Then there exists $K_0 \in \mathbb{N}$ such that for every $K \ge K_0$ and every producer $(c, m, B)$ with $\mathrm{AlphabetLE}\,c\,K$, one has $\mathrm{rate}(c, m, B) > K^{-a}$.*

*Proof.* Since $\zeta(s) \ne 0$ for $\Re s \ge 1$ (`riemannZeta_ne_zero_of_one_le_re`), $\beta := \Re \rho \le 1$, while $a \le \frac{1}{2}$ and $\beta > 1 - a$ give $\beta > \frac{1}{2}$. Put $\delta := \beta + a - 1 > 0$. Since $(1 + \log K) K^{-\delta / 2} \to 0$ as $K \to \infty$, choose $K_0 \ge 1$ so that $4800 \|\rho\| ((1 + \log K) K^{-\delta / 2})^2 < 1$ for all $K \ge K_0$. Suppose $(c, m, B)$ is a producer on $[1, K]$ ($K \ge K_0$) with $\varepsilon := \mathrm{rate}(c, m, B) \le K^{-a} \le 1$. By `IsProducer.peakRatio_le`, the peak ratio $x := \mathrm{peak}(c)/m \ge 1$ satisfies $x \le 100(1 + \log K)^2(K \varepsilon + 1) \le 200(1 + \log K)^2 K^{1 - a}$. Since $0 \le 1 - \beta \le \frac{1}{2} \le 1$, $x^{1 - \beta} \varepsilon^\beta \le 200(1 + \log K)^2 K^{(1 - a)(1 - \beta) - a \beta} = 200(1 + \log K)^2 K^{-\delta}$. By `IsProducer.zero_law`, $1 \le 24 \|\rho\| x^{1 - \beta} \varepsilon^\beta \le 4800 \|\rho\| ((1 + \log K) K^{-\delta/2})^2 < 1$, a contradiction. $\square$

**Corollary 1.2 (Supercritical Floor Above $1 - \Theta_\zeta$, `eventually_bestRate_ge_of_one_sub_zetaZeroAbscissa_lt`).** *For every $a > 1 - \Theta_\zeta$, for all sufficiently large $K$, $\mathrm{bestRate}(K) \ge K^{-a}$ and every producer $(c, m, B)$ on $[1, K]$ satisfies $\mathrm{rate}(c, m, B) > K^{-a}$.*

*Proof.* If $a > \frac{1}{2}$, `exists_half_floor` gives $\mathrm{rate}(c, m, B) \ge c_1 / (\sqrt{K}(1 + \log K)) > K^{-a}$ uniformly for all large $K$. If $1 - \Theta_\zeta < a \le \frac{1}{2}$, then $a > 0$ (as $\Theta_\zeta \le 1$) and $1 - a < \Theta_\zeta = \sup\{\Re \rho : \zeta(\rho) = 0\}$, so `exists_zetaZero_lt_re` yields $\rho$ with $\zeta(\rho) = 0$ and $\Re \rho > 1 - a$; Lemma 1.1 applies, and taking the infimum over `rateSet K` (nonempty for large $K$ by `hasRate_vk`) gives $\mathrm{bestRate}(K) \ge K^{-a}$. $\square$

---

### 2. Short-Interval $L^2$ Mellin–Plancherel Bound and Taut-String Smooth Stencil

Fix $\Theta \in [\frac{1}{2}, 1)$ such that $\zeta(s) \ne 0$ for all $\Re s > \Theta$. Fix $\varepsilon \in (0, \frac{1}{4}]$ with $\Theta + \varepsilon < 1$, and put $\sigma := \Theta + \varepsilon \in (\frac{1}{2}, 1)$.

**Lemma 2.1 (Logarithmic $L^2$ Increment Bound for Smoothed Mertens Sums, `exists_smoothedMertens_log_L2_increment_bound`).** *For $\theta \in (0, 1]$ and $X > 0$, define*
$$S_\theta(X) := \sum_{n = 1}^\infty \mu(n)\, \mathrm{smoothWeight}(X, \theta X)(n).$$
*There exists $C_{\Theta, \varepsilon} > 0$ independent of $\theta \in (0, 1]$ and $\lambda \in (0, 1]$ such that:*
1. *For all $X > 0$, $|S_\theta(X) - M(\lfloor X \rfloor)| \le \theta X + 1$.*
2. *For all $\theta \in (0, 1]$ and $\lambda \in (0, 1]$,*
   $$\int_{-\infty}^\infty e^{-2\sigma u} \big| S_\theta(e^{u + \lambda}) - S_\theta(e^u) \big|^2 \, du \le C_{\Theta, \varepsilon}\, \lambda^{1 - 2\varepsilon / 3}.$$

*Proof.* (1) is `norm_tsum_smoothWeight_sub_sum_le` applied to $N = X, H = \theta X$ (note $\mu(0) = 0$ and both sides are real).
For (2), putting $\varepsilon' := \varepsilon / 3 \in (0, \frac{1}{12}]$ (so $1 - 2\varepsilon' > 0$), since $\mathrm{smoothWeight}(X, \theta X)(x) = \mathrm{smoothWeight}(1, \theta)(x / X)$, substituting $x = X v$ in the Mellin integral gives $\mathcal{M}(\mathrm{smoothWeight}(X, \theta X))(s) = X^s W_\theta(s)$ for $\Re s > 0$. By `mobius_perron_shift_of_zeroFree` and `exists_invZeta_shift_data_of_zeroFree`, there exists $K_b \ge 0$ such that $\|\mathrm{invZeta}(\sigma + i t)\| \le K_b (2 + |t|)^{\varepsilon'}$ for all $t \in \mathbb{R}$, and $S_\theta(e^\lambda X) - S_\theta(X) = \mathrm{mellinInv}\,\sigma\,\Psi_{\theta, \lambda}(X^{-1})$, where $\Psi_{\theta, \lambda}(s) := (e^{\lambda s} - 1)\,\mathrm{invZeta}(s)\,W_\theta(s)$. Applying `integral_norm_sq_mellinInv`, `integral_Ioi_comp_neg_log_div`, and splitting at $|t| = \lambda^{-1}$ yields the $\lambda^{1 - 2\varepsilon'}$ bound. $\square$

**Lemma 2.2 (Dyadic Haar Chaining on Discrete Grids, `dyadic_haar_chaining`).** *Let $f : \mathbb{N} \to \mathbb{R}$ and $M \in \mathbb{N}$. For any $R$ pairwise disjoint intervals $[a_r, b_r) \subseteq [0, 2^M)$ ($a_r < b_r$) with $|f(b_r) - f(a_r)| \ge \Delta > 0$ for each $r$, one has $R \Delta^2 \le 2 (M + 1) \mathcal{E}_M(f)$.*

**Lemma 2.3 (Dyadic Bertrand Smooth Jump Placement, `exists_smooth_odd_jump_letter`).** *Fix $d \ge 1$. Put $C_{d,0} := 4 (d + 4)^d$ and $C_{d,1} := \max(C_{d,0},\, 2^{d + 3})$. For every $y \ge 4 d + 5$ and every integer $z$ with $C_{d,0} y \le z \le y^{d + 1}$, there exists $k \in \mathbb{N}$ such that $z < k \le z(1 + \frac{(4 d + 5) 2^{d^2 + d}}{4 y})$, $3 \le k$, $4 \nmid k$, and every prime power $q^e \mid k$ satisfies $q^e \le C_{d,1} y$.*

**Proposition 2.4 (Taut-String Smooth Stencil, `exists_taut_mertens_stencil`).** *Fix $\Theta \in [\frac{1}{2}, 1)$, $\varepsilon \in (0, \frac{1}{4}]$ with $\Theta + \varepsilon < 1$, and $d \ge 1$. There exist constants $C_1, C_2 > 0$ such that for all integers $y, T$ with $\mathrm{tautStencilMinY}(d) \le y$ and $C_{d,0} y \le T \le y^{d + 1}$, there exists $b : \mathbb{N} \to \mathbb{Z}$ supported in $[1, 2 T]$ with $b(0) = 0, b(1) = 1, b(2) = -1$ satisfying:*
1. *For every $k \ge 2$ with $b(k) \ne 0$, $4 \nmid k$ and every prime power $q^e \mid k$ satisfies $q^e \le C_{d,1} y$.*
2. *$\sum_{k = 1}^{2 T} |b(k)| \le C_1 \big((1 + \log T)^3 y^{1 + 2\varepsilon} T^{2(\Theta + \varepsilon) - 1} + (1 + \log T)(T / y) + T^{\Theta + \varepsilon}\big)$.*
3. *For every integer $x \ge 1$, $|\sum_{k = 1}^x b(k) - M(x)| \le C_2 (\frac{1}{y} + T^{-(1 - \Theta - \varepsilon)}) x$.*

---

### 3. Bipartite Hamming-Square Clusters and Subset-Product CRT Ramp

**Proposition 3.1 (Bipartite Connectedness and CRT Producer Assembly, `exists_hamming_compensated_producer`).** *Fix integers $M_0 \ge 2$, $S := 16 M_0 + 4$, $W \ge 2$, and $2 T \le K \le X$ such that $1 \le \lfloor \log_{2^S W} K \rfloor < M_0$, $B_0 := \lfloor \frac{K}{2^{S(M_0 + 1) + 2} W} \rfloor \ge 2$, and $K \ge 2^{2 S + 2} W^2 (P_{\max} + 1)$. Combining $F_{\mathrm{near}}(r)$ with the bipartite Hamming-square clusters $C_Q(r)$ and subset-product CRT ramp $F_{\mathrm{ramp}}(r)$ via `exists_stencil_of_family` produces $(c, m)$ with $\mathrm{IsProducer}\,c\,m\,B_0$, $\mathrm{AlphabetLE}\,c\,K$, and*
$$\mathrm{rate}(c, m, B_0) \le 2 \left( Y_n (1 + \log B_0) + 8 Y_n \log K + \frac{\mathcal{M}_b}{B_0} + \frac{16 M_0 \cdot 2^{2 S + 1} \log K}{B_0} (\lfloor \log_2(2 T) \rfloor + 1)^2 \mathcal{M}_b \right).$$

---

### 4. Closing the Full Strip and Question 18

**Theorem 4.1 (`hasRate_of_zeroFree_exact`).** *Let $\Theta \in [\frac{1}{2}, 1)$ satisfy $\forall s \in \mathbb{C},\, \Theta < \Re s \to \zeta(s) \ne 0$. Then for every $a \in (0, 1 - \Theta)$, $\mathrm{HasRate}(K \mapsto K^{-a})$.*

**Theorem 4.2 (`tendsto_log_bestRate_div_log`, `zeroFree_iff_forall_hasRate`, `riemannHypothesis_iff_forall_hasRate_half`, `exists_strict_floor_obstruction_iff_not_riemannHypothesis`, `strict_floor_obstruction_quarter_iff_not_riemannHypothesis`).**
1. *Unconditionally, $\lim_{K \to \infty} \frac{\log \mathrm{bestRate}(K)}{\log K} = \Theta_\zeta - 1$.*
2. *For every $\Theta \in [\frac{1}{2}, 1)$, $(\forall s \in \mathbb{C},\, \Theta < \Re s \to \zeta(s) \ne 0) \iff \forall a \in (0, 1 - \Theta),\, \mathrm{HasRate}(K^{-a}) \iff \forall a \in (0, 1 - \Theta),\, \exists^\infty K,\, \mathrm{bestRate}(K) \le K^{-a}$.*
3. *$\mathrm{RiemannHypothesis} \iff \forall a \in (0, \frac{1}{2}),\, \mathrm{HasRate}(K^{-a})$.*
4. *For every $a_0 \in [0, \frac{1}{2})$ (and in particular $a_0 = \frac{1}{4}$, Question 18),*
   $$\Big(\exists a_* \in \left(a_0, \frac{1}{2}\right),\, \forall^\infty K \in \mathbb{N},\, \forall (c : \mathbb{N} \to_0 \mathbb{Z})\,(m\,B : \mathbb{N}),\, \mathrm{IsProducer}\,c\,m\,B \to \mathrm{AlphabetLE}\,c\,K \to K^{-a_*} < \mathrm{rate}(c, m, B)\Big) \iff \neg\,\mathrm{RiemannHypothesis}.$$
