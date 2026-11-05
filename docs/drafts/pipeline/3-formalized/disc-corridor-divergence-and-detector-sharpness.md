# Sharp V/log V Zero-Detection Phase Transition and Subcritical Mollifier Disc-Corridor Divergence

- **ID:** disc-corridor-divergence-and-detector-sharpness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/review-0511/obstacles-summary.md` §2.5.3 (B21, `D_win`)
- **Lean Module:** `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/DiscCorridorDivergenceAndDetectorSharpness.lean`
- **Lean Declarations:**
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.occupiedBurnolWindows_le_of_shiftedDefect_div_log`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.logFreeNearLineWindowOccupancy_of_shiftedDefect_div_log`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.fejerDirichletDetector_occupiedWindows_ge`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.fejerDirichletDetector_Lp_defect_le_div_log`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.fejerDirichletDetector_posLogMean_le_div_log`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_twoLength_defect_normSq_arbitrary_rate`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.subcriticalShiftedDefectFloor`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.eventually_integral_normSq_zetaMollified_sub_one_ge`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.eventually_discCorridorBound_zetaMollified_ge_mul_log`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_separated_dirPoly_sum_normSq_ge_mul_log`
- **Statement:**
  1. **Sharp $V/\log V$ Disc-Detection Sufficiency (`occupiedBurnolWindows_le_of_shiftedDefect_div_log`, `logFreeNearLineWindowOccupancy_of_shiftedDefect_div_log`):** Let $V \ge e^2$, $0 < A \le \log V$, $C \ge 0$, and $r > 0$. For every holomorphic zero-detector $F : \mathbb{C} \to \mathbb{C}$ on $[\tfrac{1}{2}, 2] \times_{\mathbb{C}} [V - 5, 2V + 5]$ vanishing at every $\rho \in \operatorname{burnolUnitXiZeros}(m)$ ($m \in [\lceil V\rceil, \lfloor 2V\rfloor]$) with $\operatorname{Re}\rho \ge \tfrac{1}{2} + \tfrac{A}{\log V}$ and satisfying
     $$\int_{V - 5}^{2V + 5} \left\|F(\sigma + it) - 1\right\|^2 dt \;\le\; C\, e^{-r(\sigma - 1/2)\log V} \frac{V}{\log V} \qquad \forall \sigma \in \left[\tfrac{1}{2} + \tfrac{A}{2\log V},\, 1 + \tfrac{A}{2\log V}\right],$$
     the number of occupied Burnol unit windows $m \in [\lceil V\rceil, \lfloor 2V\rfloor]$ containing a $\xi$-zero with $|\operatorname{Re}\rho - \tfrac{1}{2}| \ge \tfrac{A}{\log V}$ is at most $\frac{32 C}{\pi r} \frac{e^{-r A / 2}}{A^2} V$. Consequently, existence of such zero-detectors with uniform $(C, r)$ eventually in $V$ implies `LogFreeNearLineWindowOccupancy` (`D_win`).
  2. **Sharp $V/\log V$ Impossibility Across All $L^p$ ($1 \le p < \infty$) and $\log^+$ (`fejerDirichletDetector`):** For every $0 < \theta < 1$ and $A > 0$, the normalized Fejér–Dirichlet polynomial $F_V(s) = 1 - D_V(s)$ of length $\le \lfloor V^\theta\rfloor$ ($b_1 = 1$), where $\sigma_* = \tfrac{1}{2} + \tfrac{A}{\log V}$, $M = \lfloor \frac{\theta \log V}{2\log 2}\rfloor$, and $D_V(s) = 2^{-(s - \sigma_*)} (M^{-1}\sum_{j=0}^{M-1} 2^{-j(s - \sigma_*)})^2$:
     - vanishes identically at $\operatorname{Re} s = \tfrac{1}{2} + \tfrac{A}{\log V}$ inside at least $\tfrac{1}{12} V$ distinct Burnol unit windows `(burnolUnitLower m, burnolUnitUpper m)` ($m \in [\lceil V\rceil, \lfloor 2V\rfloor]$) eventually in $V$;
     - satisfies for **every** $p \ge 1$ and **every** $\sigma \ge \tfrac{1}{2}$:
       $$\int_{V - 5}^{2V + 5} \left\|F_V(\sigma + it) - 1\right\|^p dt \;\le\; C(p, \theta, A) \frac{V}{\log V}, \qquad \int_{V - 5}^{2V + 5} \max\!\big(0, \log\|F_V(\sigma + it)\|\big)\,dt \;\le\; C(1, \theta, A) \frac{V}{\log V}.$$
  3. **Log-Free Barban–Vehov Shifted $L^2$ Defect at Scale $V$ (`exists_twoLength_defect_normSq_arbitrary_rate`):** Unconditionally for $\zeta$, for every $0 < r < 1$ and $r/2 < \theta_Y < \theta_X < 1/2$, there exists $A_0 > 0$ such that eventually in $S$, on admissible blocks $[T_1, T_2] \subset (2S/3, 4S/3)$ with $Y = \operatorname{molLen}(\theta_Y, S)$ and $X = \operatorname{molLen}(\theta_X, S) \le S^{\theta_X}$,
     $$\int_{T_1}^{T_2} \left\|\zeta(\sigma_0 + it) M_{X,Y}(\sigma_0 + it) - 1\right\|^2 dt \;\le\; (T_2 - T_1) A_0 e^{-r(\sigma_0 - 1/2)\log S} + 240 S^{\theta_X + 1/2} \qquad \forall \sigma_0 \in [\tfrac{1}{2}, 1].$$
  4. **Universal Subcritical Mollifier Defect Floor and $V\log V$ Disc-Corridor Divergence (`eventually_integral_normSq_zetaMollified_sub_one_ge`, `eventually_discCorridorBound_zetaMollified_ge_mul_log`):** Setting $\operatorname{subcriticalShiftedDefectFloor}(\theta, a) := \max\!\big(e^{-2a}\log\tfrac{1}{\theta},\, c_{\mathrm{rough}} e^{-2a}/\theta - 1\big) > 0$, for every $0 < \theta < 1/2$, $a \ge 0$, and $\varepsilon > 0$, eventually in $V$, every normalized Dirichlet polynomial $\Psi(s) = \sum_{d=1}^y b_d d^{-s}$ ($1 \le y \le V^\theta$, $b_1 = 1$, $\|b_d\| \le 1$, including Selberg, Möbius, and two-length Barban–Vehov $M_{X,Y}$) satisfies
     $$\int_V^{2V} \left\|\zeta\!\left(\tfrac{1}{2} + \tfrac{a}{\log V} + it\right)\Psi\!\left(\tfrac{1}{2} + \tfrac{a}{\log V} + it\right) - 1\right\|^2 dt \;\ge\; \big(\operatorname{subcriticalShiftedDefectFloor}(\theta, a) - \varepsilon\big) V,$$
     and its 2D disc-corridor integral over $[\tfrac{1}{2} + \tfrac{A}{2\log V}, \tfrac{1}{2} + \tfrac{A}{\log V}] \times [V, 2V]$ divided by $\pi (A / (2\log V))^2$ is eventually at least $\frac{\operatorname{subcriticalShiftedDefectFloor}(\theta, A)}{2\pi A} V \log V$.
  5. **Sharpness of Gallagher's Discrete Dirichlet Large-Values $\log N$ Factor (`exists_separated_dirPoly_sum_normSq_ge_mul_log`):** For every $N \ge 4$ and $V \ge 40$, there exist $> 9$-separated ordinates $\lambda_0 < \dots < \lambda_R$ in $[V, 2V]$ and nonzero coefficients $a : \operatorname{Fin} N \to \mathbb{C}$ such that
     $$\sum_{r=0}^R \left\|\operatorname{dirPoly}\, N\, a\, (\lambda_r)\right\|^2 \;\ge\; \frac{1}{40}\, V\, (\log N) \sum_{m : \operatorname{Fin} N} \|a_m\|^2.$$

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized (`lake --old env lean` exit 0, `#print axioms` `[propext, Classical.choice, Quot.sound]`)

## Proof `[PROVED HERE]`
1. **Sufficiency below $V/\log V$:** Reflect deep zeros into $\operatorname{Re}\rho_m \in [\tfrac{1}{2} + \tfrac{A}{\log V}, 1)$ via `one_sub_star_mem_burnolUnitXiZeros`, partition occupied Burnol windows modulo $8$, and apply `norm_sq_value_mul_area_le_integral_ball_local` to $F - 1$ on pairwise disjoint open discs $B(\rho_m, \frac{A}{2\log V}) \subseteq \operatorname{Ioc}(\tfrac{1}{2} + \delta_R, 1 + \delta_R) \times_{\mathbb{C}} \operatorname{Ioc}(V - 5, 2V + 5)$ together with `Complex.volume_preserving_equivRealProd` and Fubini.
2. **Impossibility at $V/\log V$ across all $L^p$ and $\log^+$:** Construct $F_V(s) = 1 - 2^{-(s-\sigma_*)}(M^{-1}\sum_{j < M} 2^{-j(s-\sigma_*)})^2$ ($M = \lfloor \frac{\theta\log V}{2\log 2}\rfloor$). Periodicity along $t_k = \frac{2\pi k}{\log 2}$ produces $\ge \tfrac{1}{12} V$ distinct occupied Burnol windows, while Parseval orthogonality on each period $[t_0, t_0 + \frac{2\pi}{\log 2}]$ bounds the $L^1$ defect by $O(\frac{V}{M}) = O(\frac{V}{\log V})$ and pointwise boundedness extends this to all $L^p$ ($p \ge 1$) and $\log^+$.
3. **Barban–Vehov shifted $L^2$ defect:** Combine `exists_twoLength_mollified_meanSquare_arbitrary_exponents` with $\|\zeta M_{X,Y} - 1\|^2 = \|\zeta M_{X,Y}\|^2 - 1 - 2\operatorname{Re}(\zeta M_{X,Y} - 1)$ and `norm_integral_zeta_mul_edPoly_sub_one_block_le`.
4. **Universal subcritical mollifier defect floor & $V\log V$ corridor divergence:** Upgrade the prime-log and $y$-rough Gaussian mean-square floors uniformly across $a \in [0, A]$, subtract the $o(V)$ first-moment error ($\theta < 1/2$), integrate over $\sigma \in [\tfrac{1}{2} + \tfrac{A}{2\log V}, \tfrac{1}{2} + \tfrac{A}{\log V}]$, and divide by $\pi(A / (2\log V))^2$.
5. **Sharpness of Gallagher's discrete MVT:** Place unit coefficients on dyadic powers $2^j$ ($0 \le j < \lfloor \frac{\log N}{\log 2}\rfloor$) and evaluate at $> 9$-separated ordinates $\lambda_r = \frac{2\pi}{\log 2}(k_0 + r) \in [V, 2V]$.
