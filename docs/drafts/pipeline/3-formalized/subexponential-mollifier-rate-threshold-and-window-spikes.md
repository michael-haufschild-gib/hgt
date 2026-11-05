# Complex Necessary-Length Law up to `exp(T^{1/60})`, Exact `exp(c log²T)` Rate Threshold, and Multi-Window Critical-Line Spikes

- **ID:** subexponential-mollifier-rate-threshold-and-window-spikes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0511/obstacles-summary.md` §2.5.1 (B20), §2.5.3 (B21); `formal/GaloisForLFunctions/ArithmeticProduction/README.md` §7 & §9 (Open Topics 2 & 3)
- **Lean Module:** `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.SubexponentialMollifierLengthAndWindowSpikes`
- **Lean Declarations:**
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.edPolyHermitianTrace`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.edPolyHermitianTrace_count_le`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_edPoly_line_logMean_floor_complex`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_left_floor_complex`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_logIntegral_le_of_complex_secondMoment`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.criticalClustering_of_complexMollifiedSecondMomentLaw`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.logFreeNearLineZeroDensity_of_complexSecondMomentRate`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.logFreeNearLineWindowOccupancy_of_complexSecondMomentRate`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.eventually_uniform_complex_necessary_length`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.eventually_uniform_complex_necessary_length_exp`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.eventually_log_mollifier_length_ge_of_excess`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.complexSecondMomentRate_forces_exp_logSq_length`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.not_complexSecondMomentRate_below_exp_logSq`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.tendsto_log_length_div_log_atTop_of_complex_second_moment_tendsto_one`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.occupiedBurnolWindows_criticalLine_spike_ge`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.occupiedBurnolWindows_criticalLine_sharp_spike_ge`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.occupiedBurnolWindows_le_of_prefixCancelling_secondMoment`
- **Statement:**
  1. **Hermitian analytic trace and removal of real-coefficient assumptions (`hbr`):** For every finite complex Dirichlet polynomial $\Psi(s) = \sum_{n \in s} a_n n^{-s}$ ($s \subseteq \mathbb{N}_{\ge 1}$) and height $T \in \mathbb{R}$, the entire function
     $$\operatorname{edPolyHermitianTrace}(a, s, T)(z) := \frac{\Psi(z + iT) + \Psi^*(z - iT)}{2}, \qquad \Psi^*(w) := \sum_{n \in s} \overline{a_n}\, n^{-w},$$
     satisfies $\operatorname{edPolyHermitianTrace}(a, s, T)(x) = \operatorname{Re}\Psi(x + iT)$ for all $x \in \mathbb{R}$, $\|\operatorname{edPolyHermitianTrace}(b, s, T)(4)\| \ge \tfrac{5}{16}$ when $b_1 = 1$ and $\|b_n\| \le 1$, and $\|\operatorname{edPolyHermitianTrace}(a, s, T)(z)\| \le \sum_{n \in s} \|a_n\| n^{-x}$ on $\operatorname{Re} z \ge x$. Consequently, the Backlund horizontal-edge bound, the Levinson mollified Littlewood budget, the critical-line log-integral ceiling $\int_T^{2T} \log\|\zeta(\tfrac{1}{2}+it)\|\,dt \le \tfrac{\varepsilon}{2}T + C + K(\log T + \log N)$, the clustering implication `ComplexMollifiedSecondMomentLaw → CriticalClustering`, the log-free density and window-occupancy implications `ComplexSecondMomentRate K₀ → LogFreeNearLineZeroDensity ∧ LogFreeNearLineWindowOccupancy`, and the left-of-line second-moment floor hold unconditionally for arbitrary complex coefficients $b : \mathbb{N} \to \mathbb{C}$ ($b_1 = 1$, $\|b_n\| \le 1$).
  2. **Uniform stretched-exponential necessary-length law and exact `exp(c log²T)` rate threshold:** Eventually as $T \to \infty$, simultaneously for all integers $1 \le N \le \exp(T^{1/60})$ and all complex Dirichlet polynomials $M(s) = \sum_{n=1}^N b_n n^{-s}$ with $b_1 = 1$ and $\|b_n\| \le 1$,
     $$\int_T^{2T} \left\|\zeta\!\left(\tfrac{1}{2}+it\right) M\!\left(\tfrac{1}{2}+it\right)\right\|^2 dt \;\ge\; \left(1 + \frac{\log T}{8\log T + 6\log N}\right) T.$$
     In particular:
     - Any complex normalized mollifier achieving $\int_T^{2T} \|\zeta(\tfrac{1}{2}+it)M(\tfrac{1}{2}+it)\|^2 dt \le (1 + \mathcal{E}) T$ ($\mathcal{E} > 0$) satisfies $\log N \ge \min\!\big(T^{1/60},\, \tfrac{\log T}{6\mathcal{E}} - \tfrac{4}{3}\log T\big)$ eventually in $T$.
     - Any complex mollifier family achieving the `D_zero`/`D_win`-forcing rate $\int_T^{2T} \|\zeta M(\tfrac{1}{2}+it)\|^2 dt \le (1 + K_0 / \log T) T$ ($K_0 > 0$) must satisfy $\log N(T) \ge \frac{(\log T)^2}{6 K_0} - \frac{4}{3}\log T$ eventually ($N(T) \ge \exp((\frac{1}{6K_0} - o(1))(\log T)^2)$); no quasi-polynomial family of length $N(T) \le \exp(\delta (\log T)^2)$ with $\delta < \frac{1}{6 K_0}$ can realize excess $K_0 / \log T$.
     - Any complex mollifier family whose normalized critical-line second moment tends to $1$ forces $\frac{\log N(T)}{\log T} \to +\infty$.
  3. **Superposed multi-window critical-line spike and window-occupancy bound (`D_win`):** For any $R \ge 1$, $\delta > 0$, $V \ge R + 4$, and any finite set $S \subseteq [\lceil V\rceil, \lfloor 2V\rfloor]$ of Burnol unit windows each containing a $\xi$-zero $\rho$ with $|\operatorname{Re}\rho - \tfrac{1}{2}| \ge \delta$, every complex prefix-cancelling mollifier $\Psi(s) = \sum_{d=1}^X b_d d^{-s}$ ($b_1 = 1$, $\|b_d\| \le B$, $\sum_{n=2}^{X_1} \|c_n\| n^{-(1/2+\delta)} \le \tfrac{1}{8}$, $Y \ge 1$) meeting the uniform Cahen–Mellin Gaussian tail bounds satisfies
     $$\int_{V - R - 3}^{2V + R + 3} \left\|\zeta\!\left(\tfrac{1}{2}+it\right)\Psi\!\left(\tfrac{1}{2}+it\right)\right\|^2 dt \;\ge\; \frac{|S|}{\lceil 2R + 7\rceil} \cdot \frac{3\delta}{4}\, e^{-\alpha/2} Y^{2\delta},$$
     and when $\alpha \le \log Y$ satisfies the sharper spike
     $$\int_{V - R - 3}^{2V + R + 3} \left\|\zeta\!\left(\tfrac{1}{2}+it\right)\Psi\!\left(\tfrac{1}{2}+it\right)\right\|^2 dt \;\ge\; \frac{|S|}{\lceil 2R + 7\rceil} \cdot \frac{3\delta}{4}\, e^{-2\alpha\delta^2} Y^{2\delta},$$
     bounding the $\delta$-occupied Burnol window count by $\frac{4}{3}\lceil 2R + 7\rceil e^{2\alpha\delta^2} \delta^{-1} Y^{-2\delta} M_{\mathrm{sq}}$.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized (`lake --old env lean` exit 0; `#print axioms` `[propext, Classical.choice, Quot.sound]`)

## Proof `[PROVED HERE]`
1. **Hermitian analytic trace (`edPolyHermitianTrace`):**
   - For $n \ge 1$ and $z \in \mathbb{C}$, $\overline{a_n n^{-z}} = \overline{a_n}\, n^{-\bar{z}}$, so $\overline{\operatorname{edPoly}(a, s, z)} = \operatorname{edPoly}(\operatorname{star} \circ a, s, \bar{z})$. At $z = x \in \mathbb{R}$, $\overline{x + iT} = x - iT$, giving $\operatorname{edPolyHermitianTrace}(a, s, T)(x) = \operatorname{Re}\operatorname{edPoly}(a, s, x + iT)$.
   - Since $\|\overline{a_n}\| = \|a_n\|$ and $\overline{b_1} = 1$, both summands satisfy the half-plane $\ell^1$ bound $\sum_{n \in s} \|b_n\| n^{-x}$ on $\operatorname{Re} z \ge x$ and head dominance $\|\operatorname{edPolyHermitianTrace}(b, s, T)(4) - 1\| \le \tfrac{11}{16}$. Jensen's disc divisor bound on $\overline{B}(4, 8)$ yields `edPolyHermitianTrace_count_le` and `abs_integral_weighted_im_logDeriv_edPoly_complex_le`, removing `hbr` across the Littlewood rectangle, left-of-line second-moment floor, log-integral ceiling, `CriticalClustering`, `LogFreeNearLineZeroDensity`, and `LogFreeNearLineWindowOccupancy` implications.

2. **Uniform stretched-exponential necessary-length law up to $N \le \exp(T^{1/60})$:**
   - For $\ell = \log T \ge 10$ and $1 \le N \le \exp(T^{1/60})$, set $\Theta = \log N \in [0, e^{\ell/60}]$, $\theta = \Theta / \ell \ge 0$, $w = \ell^2$, $B = \ell / 100$, $L = (2 + \tfrac{3}{2}\theta + \tfrac{1}{100})\ell$, $q = 2 + \tfrac{3}{2}\theta + \tfrac{3}{100}$, $p = 2/q \ge \tfrac{1}{2} e^{-\ell/60}$, $\varepsilon = p / 2000 \ge \tfrac{1}{4000} e^{-\ell/60}$, and $a = (\log 2)/(q \ell) \in (0, \tfrac{1}{4}]$.
   - The spectral left remainder cancels $\theta$ identically via $\exp(3\theta\ell) T^4 \exp(-2(L + \ell/100)) = \exp(-\ell/25)$, while the right spectral remainder decays as $w^2 e^{-\ell/50}$; both beat $\varepsilon w \sqrt{\pi}$ since $\tfrac{1}{50} - \tfrac{1}{60} = \tfrac{1}{300} > 0$.
   - At $K = 5 + \ell$, $(K - \tfrac{1}{2})^2 / w^2 \le 4 / \ell^2 \le \log 2$, $e^{-K\log 2} \ll e^{-\ell/2}$, and $a^2 / w^2 \le 10^4 \varepsilon^2 \le \varepsilon / 4$ (`le_integral_window_right_of_sq_le`).
   - With adaptive Gaussian margin $R = 4 w \sqrt{\Theta + 2\ell} \ll \ell^3 e^{\ell/60} \ll \varepsilon T$, $R^2 / (4 w^2) = 4\Theta + 8\ell$ suppresses $N^3 T^4 e^{-R^2/(4w^2)} \le e^{-4\ell}$ in the center tail and $e^{-R^2/(2w^2)} \le e^{-16\ell}$ in the interior Gaussian mass, while `exists_left_floor_complex` supplies the left floor since $C_l + K_l(\log T_2 + 5\Theta) \ll \ell e^{\ell/60} \ll v T$. Combining via `integrated_gauss_inequality`, `length_combine'`, and `final_numeric` yields $(1 + \frac{129}{1000} p) T \ge (1 + \frac{\log T}{8\log T + 6\log N}) T$.

3. **Superposed multi-window critical-line spike:**
   - Reflecting left-half zeros via `one_sub_star_mem_burnolUnitXiZeros` produces $\rho_m \in \operatorname{burnolUnitXiZeros}(m)$ with $\operatorname{Re}\rho_m \in [\tfrac{1}{2} + \delta, 1)$ and $\gamma_m \in (m - 3, m + 3)$ (`xi_eq_zero_iff_riemannZeta_of_re_pos`, `burnolUnit_coords`). Coloring $S$ modulo $\lceil 2R + 7\rceil$ extracts a subset $S_0$ of size $\ge |S| / \lceil 2R + 7\rceil$ whose intervals $(\gamma_m - R, \gamma_m + R]$ are pairwise disjoint inside $(V - R - 3, 2V + R + 3]$. Summing `integral_normSq_zetaMollified_criticalLine_spike_of_zero` (rescaled to $\sum_{n=2}^{X_1} \|c_n\| n^{-(1/2+\delta)} \le \tfrac{1}{8}$) over $S_0$ yields both spikes and `occupiedBurnolWindows_le_of_prefixCancelling_secondMoment`.
