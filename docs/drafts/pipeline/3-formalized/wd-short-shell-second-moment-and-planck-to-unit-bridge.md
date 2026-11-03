# Short-Shell Per-Window Second Moment, Giant-Cluster Equivalence, and Planck-to-Unit Occupancy Bridge

- **ID:** wd-short-shell-second-moment-and-planck-to-unit-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0211/obstacles-summary.md · NearLineLogMean
- **Statement:** Unconditional short-shell × Selberg per-window $L^p$/$L^2$ bounds ($O_r(e^{-r A} A^{-1} V (\log V)^2)$ globally and $o(V)$ above $\frac{2}{r}\log\log V$), exact $(\log V)^2$ and $V\log V$ sharpness countermodels, necessary-and-sufficient giant-cluster characterization of $(D_{\mathrm{win}}) \leftrightarrow (D_{\mathrm{zero}})$, unconditional Planck-window `logDoorStage` Bessel–Szegő certificates with $\eta(c) \to 0$, mesoscopic window push $W_r(A, V) = \min(1, e^{r A/2}/\log V)$, and vertical Planck-shadow equivalence for unit-window $(D_{\mathrm{win}})$.

## Goal
Resolve two coupled near-line zero-density problems for $\zeta$:
1. Determine the exact unconditional per-window second moment $\sum_{m = \lceil V \rceil}^{\lfloor 2V \rfloor} N_m(A, V)^2$ obtainable from `shortShell_orderSum_le_log` and Selberg's near-line density, prove where it becomes $o(V)$, prove sharpness of the $(\log V)^2$ factor at fixed $A$, and establish the exact necessary-and-sufficient condition upgrading $(D_{\mathrm{win}})$ to $(D_{\mathrm{zero}})$.
2. Push the critical-scale Planck-window bound `planckWindow_nearLine_zeroFree_volume_le` to: (a) true `logDoorStage` explicit Bessel–Szegő certificates on Planck windows with exceptional measure $\eta(c) V$, $\eta(c) \to 0$; (b) exponentially expanding mesoscopic windows with $\delta(A) \to 0$; and (c) an unconditional $O_r(e^{-r A} A^{-1} V)$ local Planck-shadow sum isolating vertically thin off-line projections as the sole obstruction to unit-window $(D_{\mathrm{win}})$.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ShortShellSecondMomentAndPlanckBridge`, `lake --old env lean` green, `#print axioms` PASS (`[propext, Classical.choice, Quot.sound]`)

## Lean Declarations
Module: `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/ShortShellSecondMomentAndPlanckBridge.lean`
- `burnolDeepOrderSum`, `shortShellCapConst`, `burnolDeepOrderSum_le_logV`, `sum_burnolDeepOrderSum_le_eight_mul_extendedShell`
- `perWindow_deepOrderSum_rpow_le_selberg`, `perWindow_deepOrderSum_sq_le_selberg`, `perWindow_deepOrderSum_sq_doubleLog_le`
- `clusteredModel_sqMoment_lower_bound`, `exists_logSpacingModel_zeroDensity_not_linearSqMoment`
- `logFreeNearLineZeroDensity_iff_windowOccupancy_and_clusterTail`, `logFreeNearLineZeroDensity_of_windowOccupancy_and_growingSqMoment`
- `sparseModel_uniformPlanckVolume_not_windowOccupancy`
- `HasPlanckLogStageBesselCertificate`, `almostAll_planckWindow_logStage_besselSzegoCertificate`
- `mesoscopicWindow_nearLine_zeroFree_volume_le`
- `planckShadowSet`, `planckShadow`, `planckShadow_pos_iff`, `unitWindow_planckShadow_sum_le`, `logFreeNearLineWindowOccupancy_iff_thinPlanckShadow`

## Approach & Complete Paper Proofs

### §1. Short-Shell × Selberg Per-Window $L^p$/$L^2$ Moment Bounds (`[PROVED HERE]`)

For $m \in \mathbb{N}$ and $A, V \in \mathbb{R}$, set
$$N_m(A, V) := \sum_{\substack{\rho \in \mathrm{burnolUnitXiZeros}\,m \\ |\operatorname{Re}\rho - 1/2| \ge A / \log V}} \operatorname{ord}_{\xi}(\rho), \qquad I_V := [\lceil V \rceil, \lfloor 2V \rfloor] \cap \mathbb{N}.$$

**Theorem 1.1 (`burnolDeepOrderSum_le_logV`, `perWindow_deepOrderSum_rpow_le_selberg`, `perWindow_deepOrderSum_sq_le_selberg`, `perWindow_deepOrderSum_sq_doubleLog_le`).**
Let $C_{\mathrm{sh}} := 48(|\mathrm{xiLineTwoLogDerivConstant}| + 2) > 0$.
1. For every $V \ge 32$ with $\log V \ge 4$, every $m \in I_V$, and every $A \in \mathbb{R}$, $N_m(A, V) \le C_{\mathrm{sh}} \log V$.
2. For every $0 < r < 1$, with $C_d, \kappa_r > 0$ from `deepExtendedShell_orderSum_le`, eventually in $V$: for all $2 \le A \le \kappa_r \log V$ and all $p \ge 1$,
   $$\sum_{m \in I_V} N_m(A, V)^p \le 8 C_{\mathrm{sh}}^{p - 1} C_d \frac{e^{-r A}}{A} V (\log V)^p, \qquad \sum_{m \in I_V} N_m(A, V)^2 \le 8 C_{\mathrm{sh}} C_d \frac{e^{-r A}}{A} V (\log V)^2.$$
3. *(Double-logarithmic $o(V)$ second moment)* For every $0 < r < 1$, eventually in $V$: uniformly across $0 \le u \le \frac{\kappa_r}{2} \log V$, setting $A_V(r, u) := \frac{2}{r}\log\log V + u$,
   $$\sum_{m \in I_V} N_m(A_V(r, u), V)^2 \le \frac{4 r C_{\mathrm{sh}} C_d e^{-r u}}{\log\log V} V.$$

*Proof.*
(1) Every $\rho \in \mathrm{burnolUnitXiZeros}\,m$ ($m \in I_V$, $V \ge 32$) satisfies $0 < \operatorname{Re}\rho < 1$ and $m - 3 < \operatorname{Im}\rho \le m + 3 \le 2V + 4$, so $\mathrm{burnolUnitXiZeros}\,m \subseteq \mathrm{shellZeros}(m - 3, m + 3)$ with $(m + 3) - (m - 3) = 6$. Applying `mediumCap_orderSum_le_logV` gives $N_m(A, V) \le C_{\mathrm{sh}} \log V$.

(2) Set $B_{\mathrm{ext}} := \{z \in \mathrm{shellZeros}(V - 4, 2V + 4) : |\operatorname{Re} z - 1/2| \ge A / \log V\}$. Each $z \in B_{\mathrm{ext}}$ belongs to `burnolUnitXiZeros m` for at most $8$ indices $m \in [\lfloor \operatorname{Im} z \rfloor - 3, \lfloor \operatorname{Im} z \rfloor + 4]$, so $\sum_{m \in I_V} N_m(A, V) \le 8 \sum_{z \in B_{\mathrm{ext}}} \operatorname{ord}_\xi(z) \le 8 C_d \frac{e^{-r A}}{A} V \log V$. Multiplying by $N_m(A, V)^{p-1} \le (C_{\mathrm{sh}} \log V)^{p-1}$ yields the $L^p$ and $p = 2$ bounds.

(3) At $A_V(r, u) = \frac{2}{r}\log\log V + u$, $e^{-r A_V(r, u)} = (\log V)^{-2} e^{-r u}$ cancels $(\log V)^2$ identically and leaves $\frac{4 r C_{\mathrm{sh}} C_d e^{-r u}}{\log\log V} V$. $\square$

---

### §2. Sharpness Countermodels & Giant-Cluster Equivalence (`[PROVED HERE]`)

**Theorem 2.1 (`clusteredModel_sqMoment_lower_bound`).**
`clusteredModel` satisfies `WindowOccupancy`, yet for every $A > 0$, setting $v_A := \lceil 4 A \rceil_+ + 4$, eventually in $V$:
$$\sum_{m \in I_V} \left(\sum_{\substack{z \in \mathrm{clusteredModel}.Z(m) \\ |z.\mathrm{re} - 1/2| \ge A / \log V}} \mathrm{clusteredModel}.\mathrm{mult}(z)\right)^2 \ge \frac{1}{2704 \cdot 2^{v_A + 2}} V (\log V)^2.$$

*Proof.* By `exists_evenHalves_subset_Icc`, at least $V / 2^{v_A + 2}$ indices $m \in I_V$ satisfy $\mathrm{evenHalves}(m) = v_A$, each active with $d_{\mathrm{Clust}}(m) \ge A / \log V$ and $2 q_{\mathrm{Clust}}(m) \ge \frac{\log V}{52}$ off-line zeros. $\square$

**Theorem 2.2 (`exists_logSpacingModel_zeroDensity_not_linearSqMoment`).**
Using `natBitLen` on $\lfloor \log m \rfloor + 1$ so $2^{\mathrm{logTwoShift}(m)} \asymp \log m$, `logSpacingModel` is a `UnitWindowStripZeroModel` satisfying `LogFreeZeroDensity`, `WindowOccupancy`, `HorizontalMomentLittleO`, and `CriticalClustering`, yet for every $A > 0$, eventually in $V$:
$$\sum_{m \in I_V} \left(\sum_{\substack{z \in \mathrm{logSpacingModel}.Z(m) \\ |z.\mathrm{re} - 1/2| \ge A / \log V}} \mathrm{logSpacingModel}.\mathrm{mult}(z)\right)^2 \ge \frac{1}{21632 \cdot 2^{\lceil 4 A \rceil_+ + 4}} V \log V.$$

*Proof.* Dyadic divisibility $2^{r_V + \lceil 2 a \rceil_+} \mid m$ with $2^{r_V} \asymp \log V$ cancels the packet multiplicity $\Theta(\log V)$ in $L^1_m$ (giving `LogFreeZeroDensity` and Selberg's horizontal moment) while leaving $\Theta_A(V / \log V)$ active windows of squared multiplicity $\Theta((\log V)^2)$, hence $\Omega_A(V \log V)$ in $L^2_m$. $\square$

**Theorem 2.3 (`logFreeNearLineZeroDensity_iff_windowOccupancy_and_clusterTail`, `logFreeNearLineZeroDensity_of_windowOccupancy_and_growingSqMoment`).**
1. `LogFreeNearLineZeroDensity` holds **if and only if** there exist $\delta, K, \tau : \mathbb{R} \to \mathbb{R}$ with $\delta(A) \to 0$, $K(A)|\delta(A)| \to 0$, $\tau(A) \to 0$ such that for all $A > 0$, $0 \le K(A)$, eventually $\#\{m \in I_V : \exists \rho \in \mathrm{burnolUnitXiZeros}\,m,\; |\operatorname{Re}\rho - 1/2| \ge A/\log V\} \le \delta(A) V$, and eventually $\sum_{m \in I_V,\, N_m(A, V) > K(A)} N_m(A, V) \le \tau(A) V$.
2. If `LogFreeNearLineWindowOccupancy` holds at rate $\delta(A) \to 0$ and $\sum_{m \in I_V} N_m(A, V)^2 \le M(A) V$ eventually with $|\delta(A)| \cdot |M(A)| \to 0$, then `LogFreeNearLineZeroDensity` holds.

*Proof.* Partition `Bad_occ` at $K(A)$ into bounded-cluster and giant-cluster windows for ($\Leftarrow$), and take $K(A) = 0$ with $8$-fold Burnol overlap and `mediumCap_orderSum_le_logV` on the two endpoint caps for ($\Rightarrow$). Part (2) follows by Cauchy–Schwarz on `Bad_occ`. $\square$

---

### §3. Planck-to-Unit Push: Obstruction, True Log-Stage Planck Certificates, Mesoscopic Windows, and Planck-Shadow Bridge (`[PROVED HERE]`)

**Theorem 3.1 (`sparseModel_uniformPlanckVolume_not_windowOccupancy`).**
For every $0 < r < 1$, eventually in $V$, uniformly across $A \ge 2$ and $0 < B \le \log V$, `sparseModel` satisfies $\operatorname{vol}\{t \in [V, 2V] : \exists m, \exists z \in \mathrm{sparseModel}.Z(m),\, t \le \operatorname{Im} z \le t + B/\log V \wedge |\operatorname{Re} z - 1/2| \ge A/\log V\} \le 8 B \frac{e^{-r A}}{A} V$ while violating unit-window `WindowOccupancy`.

**Theorem 3.2 (`almostAll_planckWindow_logStage_besselSzegoCertificate`).**
For every $B > 0$ and $0 < r < 1$, there exists $\eta : \mathbb{R} \to \mathbb{R}$ with $\lim_{c \to 0^+} \eta(c) = 0$ such that for every $c > 0$, eventually in $V$:
$$\operatorname{vol}\{t \in [V, 2V] : \neg \mathrm{HasPlanckLogStageBesselCertificate}(B, V, c, t)\} \le \eta(c) V.$$

*Proof.* Outside a finite measure-zero set $Y_{\mathrm{fin}}$ of horizontal-edge zero ordinates, $[-1/2, 3/2] \times [t, t + B/\log V]$ is boundary-regular inside the $m = \lfloor t \rfloor$ Burnol unit window. Failure of `InCorridor` at $n_m = \mathrm{logDoorStage}\,c\,m$ and $\eta = \frac{1}{4 n_m}$ gives $2(\operatorname{Re} z - 1/2) > \frac{1}{4 n_m}$, i.e., $\operatorname{Re} z - 1/2 > \frac{1}{8 n_m}$. Quantitative zero transfer at radius $\frac{1}{16 n_m}$ produces $w \in \mathrm{burnolUnitXiZeros}\,m$ with $|\operatorname{Re} w - 1/2| \ge \frac{1}{16 n_m} \ge \frac{A_c}{\log V}$ ($A_c = \frac{1}{64 c}$, since $n_m \le 3 c \log V$), and `deepExtendedShell_orderSum_le` bounds the union of intervals $[w.\mathrm{im} - B/\log V - \delta_{\mathrm{im}}, w.\mathrm{im} + \delta_{\mathrm{im}}]$ by $C_d(8 + 64 B c) e^{-r / (64 c)} V$. $\square$

**Theorem 3.3 (`mesoscopicWindow_nearLine_zeroFree_volume_le`).**
Setting $B = \min(\log V, e^{r A / 2})$ in `planckWindow_nearLine_zeroFree_volume_le` gives log-free exceptional measure $C_r \frac{e^{-r A / 2}}{A} V \to 0 \cdot V$ on mesoscopic windows of width $\min(1, e^{r A / 2} / \log V)$.

**Theorem 3.4 (`planckShadow_pos_iff`, `unitWindow_planckShadow_sum_le`, `logFreeNearLineWindowOccupancy_iff_thinPlanckShadow`).**
1. For $B > 0$ and $\log V > 0$, $\mathrm{planckShadow}(m, A, B, V) > 0 \iff \exists \rho \in \mathrm{burnolUnitXiZeros}\,m,\; |\operatorname{Re}\rho - 1/2| \ge A / \log V$.
2. For $0 < r < 1$, eventually in $V$, uniformly across $2 \le A \le \kappa_r \log V$ and $0 < B \le \log V$, $\sum_{m \in I_V} \mathrm{planckShadow}(m, A, B, V) \le 8 C_d B \frac{e^{-r A}}{A} V$, so at most $8 C_d \frac{e^{-r A / 2}}{A} V$ unit windows satisfy $\mathrm{planckShadow}(m, A, 1, V) \ge e^{-r A / 2}$.
3. `LogFreeNearLineWindowOccupancy` holds **if and only if** the count of unit windows with $0 < \mathrm{planckShadow}(m, A, 1, V) < e^{-r A / 2}$ is $o_{A \to \infty}(V)$.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:**
  1. `clusteredModel_sqMoment_lower_bound` & `exists_logSpacingModel_zeroDensity_not_linearSqMoment`: Even assuming `WindowOccupancy`, $\sum_m N_m(A, V)^2 \ge c_A V (\log V)^2$; even assuming `LogFreeZeroDensity`, $\sum_m N_m(A, V)^2 \ge c'_A V \log V$.
  2. `sparseModel_uniformPlanckVolume_not_windowOccupancy`: Even assuming the full uniform Planck-window volume bound across all $0 < B \le \log V$ and $0 < r < 1$, unit-window `WindowOccupancy` fails on $100\%$ of windows because $B = \log V$ incurs the exact $\log V$ covering factor.
- **Strongest positive survivor:**
  1. Unconditional short-shell × Selberg $O_r(e^{-r A} A^{-1} V (\log V)^2)$ bound + unconditional $o(V)$ per-window second moment above $\frac{2}{r}\log\log V$ + exact giant-cluster `IFF` characterization of $(D_{\mathrm{win}}) \leftrightarrow (D_{\mathrm{zero}})$.
  2. Unconditional Planck-window `logDoorStage` explicit Bessel–Szegő certificate with $\eta(c) \to 0$ + mesoscopic scale-push $W_r(A, V) = \min(1, e^{r A/2}/\log V)$ + $O_r(e^{-r A} A^{-1} V)$ Planck-shadow sum reducing unit $(D_{\mathrm{win}})$ to excluding vertically thin off-line projections.
- **New insight:** Separates $(D_{\mathrm{zero}})$ into two orthogonal geometric axes on unit windows: (a) vertical Minkowski $1/\log V$-content `planckShadow` (unconditionally $o_{A \to \infty}(V)$ in $L^1_m$, leaving only vertically thin sets $0 < \mathrm{planckShadow} < e^{-r A/2}$), and (b) horizontal/multiplicity giant clusters $N_m > K(A)$ (exact `IFF` gap between $(D_{\mathrm{win}})$ and $(D_{\mathrm{zero}})$, unconditionally killed above $\frac{2}{r}\log\log V$).
- **Status:** Unconditionally formalized in `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/ShortShellSecondMomentAndPlanckBridge.lean`; `lake --old env lean` green (`0` `sorry`s, standard axioms only).

## Log
- 2026-11-03 — created with complete dependency-closed paper proofs in 2-fully-proven
- 2026-11-03 — unconditionally formalized in `ShortShellSecondMomentAndPlanckBridge.lean` and promoted to 3-formalized
