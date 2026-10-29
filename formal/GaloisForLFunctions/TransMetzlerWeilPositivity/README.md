# Trans-Metzler Complete Weil Positivity and the Overlap-Ratio Phase Diagram

Namespace `GaloisForLFunctions.TransMetzlerWeilPositivity`; umbrella `TransMetzlerWeilPositivity.lean`.

**Question.** At horizon $N$ and atom width $w = c/N$ (overlap ratio $c = w/\delta_N$ against the spacing $\delta_N = \log(1 + 1/N)$), the complete Weil form of $\zeta$ on atomic families $f_x(u) = \sum_{n \le N} x_n \varphi((u - \log n)/w)$ is governed by a Metzler trickle-down inequality below $c = 1$, while for every profile strictly positive on $(0, 1)$ and every $\rho > 1$ the top-collar triangle $\{1, N - 1, N\}$ frustrates every unimodular gauge (`metzlerThreshold_overlapRatio`). **Does unconditional positivity of the complete Weil form survive strictly past the Metzler wall $c = 1$, where does selectivity against the Liouville twin first turn on, what zero-side content does a fixed overlap ratio carry, and how slowly can an RH-equivalent overlap schedule grow?**

> Unconditional positivity of $\zeta$'s complete Weil form **crosses the Metzler threshold $c = 1$**: for the explicit smooth full-support plateau $\varphi_0 = \texttt{plateau}(1/1000)$ and explicit rational overlap ratio $c_0 = 1 + 10^{-18} > 1$ (and at exact spacing width $\rho_0 \delta_N$ with $\rho_0 = 1 + \frac{1}{2}\cdot 10^{-18} > 1$), `completeWeilMatrix φ₀ c N` is eventually positive definite on all of $(0, c_0]$ while no unimodular gauge makes the atomic Markov form Metzler. What replaces the diagonal gauge is a **convex combination of Ramanujan norm-quasimode spectral exclusion and strict-variance prime-defect coercivity**, paying both long-shift archimedean overlaps and the additive successor prime correlations $(kn, kn \pm 1)$ in the top third $3n > N$. By contrast, the Liouville twin $\lambda\Lambda$ breaks down inside the strictly separated regime at the **Robin–Euler ratio** $c_{\mathrm{RE}}(\varphi) = e^{\beta(\varphi)/\|\varphi\|_2^2}/(2\pi) < 1/2$ (approaching $e/(2\pi) \approx 0.4326 < 1$ on thin plateaus), failing at both $c = 1$ and $c_0$. On the zero side, finite off-line support bounds the atomic negative index uniformly across all $c > 0$, while the tempered countermodel `isolatedPairConfig` refutes any purely zero-side deduction of fixed-$c$ positivity without $\zeta$'s $\frac{\log T}{2\pi}$ zero density. Finally, a single fixed Steklov infinite-convolution Denjoy–Carleman profile pushes RH-complete overlap growth strictly below every Gevrey power $(\log\log N)^{1+\varepsilon}$ down to $(\log\log N)(\log\log\log N)^\beta$ for every $\beta > 2$.

---

## 1. Place in the research

| Programme | Takes / adds |
|---|---|
| `RenormalizedArithmeticPotentialTheory` | Complete Weil horizon matrix, Ramanujan adjunction spectrum $E_m$, prime-defect coercivity, archimedean finite part $-\log 2\pi$ / perturbative trans-Metzler splitting, Fejér–Abel center floor, Liouville breakdown above $c_{\mathrm{RE}}(\varphi)$ |
| `CriticalArithmeticCorrelationTheory` | Smooth plateau shape/charge limits, overlap-length cross-error control / explicit numerical reserve on $\varphi_0 = \texttt{plateau}(1/1000)$ and crossing $c > 1$ |
| `ArithmeticLorentzianGeometry` | Sharp Metzler frustration threshold at $\rho = 1$, narrow-spacing twin Hodge index / simultaneous positive definiteness and gauge frustration at $\rho_0 \delta_N > \delta_N$ |
| `SpacingScaleHarmonicAnalysis` | Single-zero Nyquist weight bound, Euler–Maclaurin synthesis, Gevrey profiles / sharp linear-in-$c$ zero lower bound, Steklov logarithmic Denjoy–Carleman profile and $(\log\log N)(\log\log\log N)^\beta$ RH-equivalence |
| `HeckeKreinToeplitz`, `ArithmeticIndexDescent`, `SquareRootThreshold` | Krein receiver index bound, complex/real Weil Gram bridge, `isolatedPairConfig` / uniform atomic negative-index bound under `FiniteOffLine` and all-ratio countermodel to purely zero-side proofs |

---

## 2. Regulator, counterterm, anomaly, and gauge map

* **Regulator:** prime-order horizon $n \le N$ coupled to atom width $w_N = c/N$ (or $\rho \delta_N$).
* **Counterterm & survival reserve:** rank-one polar counterterm $\ell(x)^2 = (\sum_{n \le N} x_n/\sqrt{n})^2$; strict profile Cauchy–Schwarz variance $1 - q(\varphi_0) = 1 - (\int \varphi_0)^2/\int \varphi_0^2 \ge 1/128000$ retains a uniform `poleDefect` reserve across $c \in (0, 1 + 1/512000]$.
* **Paying place:** the completed Robin margin $\beta(\varphi_0)/\|\varphi_0\|_2^2 + c\,q(\varphi_0) - \log(2\pi c) > 1/20$ lifts the conductor-$1$ Ramanujan mode, while `poleDefect` pays top-collar mass ($\sum_{n > N/3} x_n^2 \ll (\texttt{poleDefect } N\ x + \|x\|^2)/\log(N/3)$) and absorbs the $O((c - 1) + 1/N)(\texttt{poleDefect } N\ x + \|x\|^2)$ successor prime correlations.
* **Gauge selectivity:**
  * **$\zeta$ (trivial gauge):** pole-matched; positive definite for all $c \in (0, c_0]$ with $c_0 = 1 + 10^{-18} > 1$.
  * **Liouville twin $\lambda\Lambda$:** anti-matched on the pole; its prime form attains $\log M - \gamma + o(1)$ on the pole-orthogonal hyperplane $\sum_{n \le M} x_n/\sqrt{n} = 0$, so its complete Weil form becomes negative at every fixed $c > c_{\mathrm{RE}}(\varphi)$ (for $\varphi_0$, every $c \ge 1/2$), while remaining nonnegative for $0 < c \le \texttt{fixedWidthRatio}$.

| Overlap regime $c = w/\delta_N$ | $\zeta$ complete Weil form | Liouville twin $\lambda\Lambda$ | Zero-side stratum |
|---|---|---|---|
| $0 < c \le \texttt{fixedWidthRatio}$ | Unconditionally $\ge 0$ | Unconditionally $\ge 0$ | Universal stability |
| $c_{\mathrm{RE}}(\varphi) < c \le 1$ ($e/(2\pi) < 1$) | Eventually `PosDef` (including $c = 1$) | Eventually $< 0$ | Pole-matching selectivity inside strict separation |
| $1 < c \le c_0 = 1 + 10^{-18}$ | Eventually `PosDef` (frustrated Markov gauge) | Eventually $< 0$ | Unconditional trans-Metzler positivity |
| Arbitrary fixed $c > 0$ | $\ge 0$ under RH; `hermNegIndex ≤ ncard(rightZeros)` under `FiniteOffLine` | Eventually $< 0$ for $c > c_{\mathrm{RE}}(\varphi)$ | Fails on `isolatedPairConfig` at every $c > 0$ |
| $c_N = (\log\log N)(\log\log\log N)^\beta$ ($\beta > 2$) | Eventually $\ge 0 \iff \texttt{RiemannHypothesis}$ (one fixed profile `steklovDCProfile`) | Infinitely often $< 0$ | Full RH completeness below all Gevrey powers |

---

## 3. Modules and pillar theorems

### `ExplicitPlateauParameters.lean`
Quantitative bounds for `transMetzlerProfile = plateau (1 / 1000)` and explicit trans-Metzler constants `deltaZero = 10⁻¹⁸`, `cZero = 1 + 10⁻¹⁸`, `rhoZero = 1 + (1/2) * 10⁻¹⁸`:
* `deriv_smoothTransition_bounds`: $0 \le \sigma'(x) \le 4$, giving Lipschitz constant $8000$ on `transMetzlerProfile`.
* `transMetzlerProfile_frustrated_of_one_lt`: for every $\rho > 1$, eventually no unimodular gauge makes `atomicMarkovGram` Metzler.
* `transMetzlerProfile_charge_deficit_ge`: $1/128000 \le 1 - \texttt{completeWeilPoleShift transMetzlerProfile } 1$.
* `completeWeilAdjunctionEnergy_transMetzlerProfile_gt_one_twentieth`: $1/20 < E_m(\varphi_0, c)$ for all $c \in (0, 1 + 1/1000]$ and $m \ge 1$.
* `transMetzlerProfile_robinEuler_lt_half`: $\exp(\beta(\varphi_0)/\|\varphi_0\|_2^2)/(2\pi) < 1/2$.

### `TransMetzlerDecomposition.lean`
Exact perturbative decomposition `normalizedFullWeilHorizonMatrix = transMetzlerMainMatrix + perturbation` for widths $1/(2N) \le w \le (1 + \delta_0)/N$:
* `top_adjacent_of_log_gap_le`, `sum_top_third_sq_le_poleDefect`: support overlaps occur only on adjacent pairs $|j - n| = 1$ in the top collar $2\min(n, j) + 2 \ge N$, where mass is paid by `poleDefect / log(N / 3)`.
* `tendsto_transMetzlerMainMatrix_ramanujan_residual_norm`: norm quasimode convergence $\|H_N^{\mathrm{main}} u_m^{(N)} - E_m u_m^{(N)}\| \to 0$ for every conductor $m \ge 1$.
* `abs_nonRatioForm_transMetzler_le`: signed prime-defect + Chebyshev bound on the additive successor prime pairs $(kn, kn \pm 1)$ with factor $\delta_0 + 2/N$.
* `exists_perturbation_bound_transMetzler`: total overlap-and-drift perturbation bounded by $(2000\delta_0 + C_{\mathrm{short}}/\log(N/3))(\texttt{poleDefect } N\ x + \|x\|^2)$.

### `TransMetzlerPositivity.lean`
Crossing the Metzler threshold unconditionally:
* `eventually_transMetzlerMainMatrix_floor_and_defect`: convex combination of the $1/25$ eigenvalue floor and uniform coercivity retains $(1/60)\|x\|^2 + c_{\mathrm{pd}}\,\texttt{poleDefect } N\ x$.
* `exists_gt_one_eventually_completeWeilMatrix_posDef`: unconditional existence of $c > 1$ (`cZero`) and $\varphi \in C_c^\infty(\mathbb{R})$ (`transMetzlerProfile`, positive on $(0, 1)$) with `(completeWeilMatrix φ c N).PosDef` and atomic `weilQuad ≥ 0` eventually.
* `eventually_completeWeilMatrix_posDef_of_mem_Ioc`, `eventually_completeWeilMatrix_posDef_one`, `eventually_touching_atomSpacing_posDef`: eventual positive definiteness across all $c \in (0, c_0]$ and at exact spacing `atomSpacing N`.
* `eventually_transMetzler_atomSpacing_posDef_and_frustrated`: simultaneous complete Weil positive definiteness and unimodular Markov gauge frustration at `rhoZero * atomSpacing N`.

### `LiouvilleTwinSelectivity.lean`
Sharp selectivity of fixed overlap ratios on the Liouville twin:
* `neg_four_le_sum_cos_div`, `sum_archimedeanCenterKernel_ge`: uniform Fejér–Abel cosine partial-sum bound $\sum_{d=1}^M \cos(d\theta)/d \ge -4$ and Hankel moment positivity give $\sum_{n, j \le M} x_n x_j\,\texttt{archimedeanCenterKernel } n\ j \ge -(17/4)\sum_{n \le M} n x_n^2$.
* `exists_bounded_hyperplane_liouville_witness`: pole-orthogonal witness $x_n = (\lambda(n) - s_M)/\sqrt{n}$ satisfying $n x_n^2 \le 4$ and attaining $\log M - \gamma - \varepsilon$ in the twin prime form.
* `eventually_liouville_weilQuadTw_neg_of_gt_robinEuler`: sub-horizon dilution $M_N = \lfloor (c'/c) N \rfloor$ forces eventual negativity of the Liouville twin's complete Weil form at every fixed $c > \texttt{robinEulerThreshold }\varphi$ whenever $\texttt{robinEulerThreshold }\varphi < 1$.
* `eventually_liouville_weilQuadTw_neg_transMetzlerProfile`, `exists_plateau_liouville_weilQuadTw_neg_of_gt_exp_div_two_pi`, `liouville_weilQuadTw_nonneg_of_le_fixedWidthRatio`: breakdown for $c \ge 1/2$ on `transMetzlerProfile` (hence at $c = 1$ and $c_0$), breakdown above $e/(2\pi)$ on plateaus, and survival up to `fixedWidthRatio`.

### `ZeroSideStratum.lean`
Zero-side implications and countermodel at fixed overlap ratios:
* `unconditional_transMetzler_positivity_interval`, `weilQuad_atomicTest_nonneg_of_riemannHypothesis`: unconditional positivity on $(0, c_0]$ and all-ratio positivity under `RiemannHypothesis`.
* `hermQuad_atomicShiftWeilGram_eq_weilQuad`, `hermNegIndex_atomicShiftWeilGram_le_of_finiteOffLine`: under `(rightZeros zetaZeroConfig).Finite`, the negative index of `atomicShiftWeilGram φ (c / N) N` is at most `(rightZeros zetaZeroConfig).ncard` uniformly across all $c > 0$ and $N \ge 1$.
* `re_Wsummand_atomicTest_const_one_ge`: sharp linear-in-$c$ lower bound on a single real zero summand at $x \equiv 1$.
* `isolatedPairConfig_atomic_negative_every_ratio`: on the tempered single-off-line-pair configuration `isolatedPairConfig (Real.log_pos one_lt_two) hδ hδ' 0`, the two-atom witness $x_1 = 1, x_2 = -1$ annihilates the entire vertical lattice and gives $\operatorname{Re} Z.W(f_x, f_x) < 0$ at every $c > 0$ and every $N \ge 2$.

### `SuperGevreyCriticalGrowth.lean`
Breaking below all Gevrey power schedules with one fixed Denjoy–Carleman profile:
* `steklovDCProfile`, `contDiff_steklovDCProfile`, `steklovDCProfile_vanishesOff`, `integral_steklovDCProfile`, `integral_abs_iteratedDeriv_steklovDCProfile_le`: explicit smooth profile supported in $[-1, 1]$ with unit integral and $\|\varphi^{(q)}\|_{L^1} \le (2\,\texttt{steklovBaseSup})\cdot 12^q q! (\log(q + 3))^{2q}$, constructed as the uniform limit of iterated Steklov averages at radii $a_m = 1/(4(m + 3)(\log(m + 3))^2)$.
* `superGevreyRatio_isLittleO_loglog_rpow`, `riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey`: for every $\beta > 2$, $c_N = (\log\log N)(\log\log\log N)^\beta = o((\log\log N)^{1+\varepsilon})$ for all $\varepsilon > 0$, and eventual atomic Weil nonnegativity of `steklovDCProfile` at ratio $c_N$ is equivalent to `RiemannHypothesis`.

---

## 4. Traps

| Trap | Truth |
|---|---|
| Crossing $c = 1$ requires a new diagonal gauge on the atomic basis | Impossible by `metzlerThreshold_overlapRatio`; positivity past $c = 1$ comes from convex-combination spectral exclusion + `poleDefect` reserve |
| Short-shift archimedean overlaps vanish per pair as $c \to 1^+$ | Individual short-shift entries near $N$ are $\Theta(1)$, not $O(c - 1)$; they vanish only against bounded-`poleDefect` modes via the $1/\log(N/3)$ top-collar mass saving |
| Touching positivity ($c = 1$) is universal over sign twists | False: the Liouville twin already fails above $c_{\mathrm{RE}}(\varphi) < 1/2$ (down to $e/(2\pi) \approx 0.4326$) via pole-hyperplane witnesses |
| `TemperedConfig` + `FiniteOffLine` + single-zero Nyquist bound implies eventual fixed-$c$ positivity | False: `isolatedPairConfig` with period $2\pi/\log 2$ fails at every $c > 0$ on $x_1 = 1, x_2 = -1$; $\zeta$'s growing $\frac{\log T}{2\pi}$ density is indispensable |
| Fixed-profile Euler–Maclaurin synthesis stops at Gevrey powers $(\log\log N)^{1+\varepsilon}$ | One fixed Steklov Denjoy–Carleman profile reaches $(\log\log N)(\log\log\log N)^\beta$ for every $\beta > 2$ |

---

## 5. Open problems

1. **Macroscopic overlap ratios $c \ge 2$:** how far across integer successor shells $(kn, kn \pm r)$ ($1 \le r < c$) does unconditional complete Weil positivity extend for $\zeta$ before any putative off-line zero could enter?
2. **Finite off-line support for $\zeta$ itself at arbitrary $c \gg 1$:** does `(rightZeros zetaZeroConfig).Finite` imply eventual positivity of `completeWeilMatrix φ c N` for every fixed $c > 0$ once $\zeta$'s $\frac{\log T}{2\pi}$ on-line zero density (or prime explicit formula) decouples off-line Dirichlet polynomial vectors $(n^{\rho_0 - 1/2})_{n \le N}$ from bounded-`poleDefect` modes?
3. **Sharp Denjoy–Carleman exponent $\beta \in (1, 2]$:** closing the gap between Euler–Maclaurin synthesis at $(\log\log N)(\log\log\log N)^\beta$ ($\beta > 2$, from $\sum (m (\log m)^2)^{-1} < \infty$) and the Denjoy–Carleman quasi-analyticity boundary $\sum (m \log m)^{-1} = \infty$.
