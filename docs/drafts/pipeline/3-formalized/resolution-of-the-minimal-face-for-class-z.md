# Resolution of the minimal face for the class `𝒵`

## Metadata
- **Date**: 2026-11-10
- **Status**: 3-formalized
- **Author**: Agent
- **Target**:
  - `formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/HighFrequencyBinomialPolynomials.lean`
  - `formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/SubLogarithmicWindowsMissTheMinimalFace.lean`
- **Obstacle Reference**: B143 (`docs/reports/review-1011/obstacles-summary.md`, §3)

## Mathematical Statement

Let $\mathcal{Z}(\gamma_{\min}, C)$ be the class of tempered reflection-symmetric zero configurations $Z$ in $0 < \operatorname{Re} s < 1$ without real zeros, with lowest ordinate $|\operatorname{Im} \rho| \ge \gamma_{\min} > 0$ for all $\rho \in Z$ and unit-window local counts $N_Z(t, t+1] \le C \log(|t| + 3)$ for all $t \in \mathbb{R}$.

1. **Unbounded sub-logarithmic windows do not decide $\mathcal{Z}$ (Resolution of Question B143.2).**
   For every $\gamma_{\min} > 0$, $C > 0$, and $0 < \Theta \le 1/2$, there exist a zero configuration $Z \in \mathcal{Z}(\gamma_{\min}, C)$ of simple zeros ($\text{mult} \equiv 1$) with unattained accumulating top $\sup_{\rho \in Z} \operatorname{Re} \rho = 1/2 + \Theta$ ($\operatorname{Re} \rho < 1/2 + \Theta$ for all $\rho \in Z$) and a monotone window radius function $R : \mathbb{R} \to \mathbb{R}$ satisfying
   $$\lim_{T \to \infty} R(T) = +\infty, \qquad \lim_{T \to \infty} \frac{R(T)}{\log T} = 0$$
   such that $2 \operatorname{Re} S_Z(u)$ is bounded below beyond every bound on arbitrarily late windows of radius $R(T)$:
   $$\forall K, U \in \mathbb{R}, \quad \exists T \ge U, \quad \forall u \in [T - R(T), T + R(T)], \quad 2 \operatorname{Re} S_Z(u) \ge K.$$

2. **Bounded windows do not decide $\mathcal{Z}$ (Resolution of Question B143.1).**
   For every $\gamma_{\min} > 0$, $C > 0$, $0 < \Theta \le 1/2$, and $L > 0$, the same configuration $Z \in \mathcal{Z}(\gamma_{\min}, C)$ satisfies
   $$\forall K, U \in \mathbb{R}, \quad \exists u_0 \ge U, \quad \forall u \in [u_0, u_0 + L], \quad 2 \operatorname{Re} S_Z(u) \ge K.$$
   In particular, no bounded window length $L = L(\gamma_{\min}, C)$ decides $\mathcal{Z}(\gamma_{\min}, C)$.

3. **Prime-window corollaries and maximal-abscissa specialization.**
   Restricting $u = \log p$ to primes $p$, the configuration $Z \in \mathcal{Z}(\gamma_{\min}, C)$ satisfies $2 \operatorname{Re} S_Z(\log p) \ge K$ on arbitrarily late prime windows $|\log p - T| \le R(T)$ of unbounded sub-logarithmic radius $R(T) = o(\log T)$, and on arbitrarily late bounded prime windows $\log p \in [u_0, u_0 + L]$, while having off-line zeros accumulating at $1/2 + \Theta$ (and at $\operatorname{Re} s = 1$ when $\Theta = 1/2$).

## Formalized Declarations

- `GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.HighFrequencyBinomialPolynomials`:
  - `highFreqPoly`, `highFreqCoeff`
  - `norm_one_sub_highFreqPoly_le_quarter`, `three_quarters_le_re_highFreqPoly`
  - `highFreqPoly_eq_sum_highFreqCoeff`, `abs_highFreqCoeff_le_sixtyFour_pow`
  - `three_quarters_le_sum_highFreqCoeff_cos`
  - `generalSplinePoint`, `sincC_generalSplinePoint_bounds`
  - `phaseShift`, `phaseShift_bounds`, `cexp_I_add_phaseShift_mul`
  - `phase_split_pair_eq`, `norm_perturbed_mode_sub_le`
  - `levelRadius`, `levelStep`, `levelStart`, `levelBaseFreq`, `levelMinWeight`, `levelCoeffBound`, `levelTargetPhase`, `levelFreq`, `levelMain`, `levelRefl`, `levelWeightBound`
  - `levelFreq_strict_order`, `abs_levelMain_le`, `abs_levelRefl_le`, `levelMain_ge_on_window`
- `GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SubLogarithmicWindowsMissTheMinimalFace`:
  - `InClassZ`, `minimalFaceCounterConfig`, `minimalFaceSubLogRadius`
  - `inClassZ_minimalFaceCounterConfig`
  - `k_add_one_le_two_re_lagStructure_on_window`
  - `monotone_minimalFaceSubLogRadius`, `tendsto_minimalFaceSubLogRadius_atTop`, `minimalFaceSubLogRadius_sq_le_log`, `tendsto_minimalFaceSubLogRadius_div_log`
  - `exists_classZ_unbounded_subLog_windows_bddBelow_beyond_every_bound`
  - `not_forall_unbounded_radius_decides_classZ`
  - `exists_classZ_bounded_windows_bddBelow_beyond_every_bound`
  - `not_exists_bounded_window_length_decides_classZ`
  - `exists_classZ_unbounded_subLog_prime_windows_bddBelow_beyond_every_bound`
  - `exists_classZ_bounded_prime_windows_bddBelow_beyond_every_bound`
  - `exists_classZ_accumulating_at_one_subLog_windows_bddBelow_beyond_every_bound`

## Proof Summary

1. **High-frequency binomial polynomials on a short arc.**
   Expanding $1 = (z + (1 - z))^{2 m_0}$ and keeping the upper half $P_{m_0}(z) = \sum_{m = m_0}^{2 m_0} \binom{2 m_0}{m} z^m (1 - z)^{2 m_0 - m}$ gives $\|1 - P_{m_0}(z)\| \le 4^{m_0} (1/4)^{m_0 + 1} = 1/4$ on the short arc $\|z\| = 1, \|1 - z\| \le 1/4$, hence $\operatorname{Re} P_{m_0}(z) \ge 3/4$. Expanding $(1 - z)^{2 m_0 - m}$ yields $P_{m_0}(z) = \sum_{d = m_0}^{2 m_0} a(m_0, d) z^d$ with integer coefficients $|a(m_0, d)| \le 64^{m_0}$ supported entirely in $[m_0, 2 m_0]$ and $\sum_{d = m_0}^{2 m_0} a(m_0, d) \cos(d \delta v) \ge 3/4$ for $|v| \le R$, $\delta = 1/(4R)$.

2. **Phase-split simple-zero clusters at prescribed window centers.**
   At level $k$, depth $x_k = \Theta(1 - 2^{-k-1})$, radius $R_k = k + 1$, step $\delta_k = 1/(4(k + 1))$, and base ordinate $\Gamma_k \ge 4$, the harmonics $d \in [m_0(k), 2 m_0(k)]$ with $m_0(k) = 4(k + 1)\Gamma_k$ lie in $[\Gamma_k, 2 \Gamma_k]$. Splitting each harmonic into two simple zeros with arccosine phase offsets $\pm \arccos(|a(m_0(k), d)| r_{\min}(k) / (64^{m_0(k)} r_{k, d}))$ and $O(1/T_k)$ ordinate shifts aligns the phases at $u = T_k$ while keeping all ordinates strictly distinct (so $\text{mult} \equiv 1$). For $T_k$ large enough relative to $(m_0(k) + 1)(R_k + 16) 64^{m_0(k)} / r_{\min}(k)$, the level-$k$ main trace satisfies $\text{levelMain}_k(u) \ge \frac{3}{2} r_{\min}(k) / 64^{m_0(k)} > 0$ across the entire interval $[T_k - R_k, T_k + R_k]$.

3. **Mutual tower recursion, local zero counts, and sub-logarithmic radius.**
   Choosing $(\Gamma_k, T_k)$ by mutual recursion so that $\Gamma_k \ge \exp((32 k + 40)/C)$, the total weight of level $k$ decays faster than $2^{-k} \exp(-\Theta(T_{k-1} + R_{k-1}))$, and $T_k \ge \exp((k + 1)^2)$ IS large enough for level $k$ to dominate levels $0, \dots, k - 1$ on $[T_k - R_k, T_k + R_k]$ produces a configuration $Z \in \mathcal{Z}(\gamma_{\min}, C)$ with $2 \operatorname{Re} S_Z(u) \ge k + 1$ across $|u - T_{k+1}| \le R_{k+1} = k + 2$, while $R(T) := k + 1$ on $[T_k, T_{k+1})$ satisfies $R(T) \to \infty$ and $R(T)^2 \le \log T$ ($R(T) = o(\log T)$).
