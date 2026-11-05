# Super-Enlarged Weil Floor Apertures, Neutral Signed Theta-Gauge Sliver Laws up to $\log 5$, and Non-Orthogonal Multiplicative Convolution Horizon Stabilization

- **ID:** super-enlarged-theta-sliver-and-multiplicative-convolution-horizon
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `SignedWindowCriticality` · `ArithmeticIncidencePositivity` · `ArithmeticHodgeTheoryOfDegenerations`
- **Statement:** Every compact window $[-R, R]$ ($R > 0$) obeys an explicit derivative-free multi-prime dilation modulus across arbitrary prime-power entries (generating an infinite strictly increasing tower of unconditional Weil-floor apertures `weilFloorApertureTower : ℕ → ℝ` above `enlargedWeilFloorAperture` and `successorWeilFloorAperture`); the neutral signed theta-gauge pair `(signedEvenThetaGauge b (neutralEvenThetaParam b c), shiftedGroundState a)` satisfies exact pole-neutral $(b, \alpha_0)$-invariance, asymptotic $b \to \infty$ outside-deficit conservation, and sub-unit collective $\{2, 3, 4\}$ outward Lévy edge-carry across $0 < 2c < \log 5$; and non-orthogonal multiplicative-convolution horizon shifts `dirichletShiftWeights d g₀ N` couple at $O(1)$ to $W(\mathrm{halfWeight}\,h)$, stabilizing every nonzero horizon test on $[-(A + \log 2), 0]$ ($A \ge 0$ arbitrary) along every critical curve $c_N^8 / \log N \to K$ for all $K > 0$.

## Goal
1. Push the unconditional quantitative Weil-positivity and reflection-pair sliver frontier strictly above $2 \cdot \mathrm{enlargedWeilFloorAperture}$ (and above $2 \cdot \mathrm{successorWeilFloorAperture}$) without numerical matrix computations, while characterizing the exact $(b, a)$ optimization and prime-$3$ / prime-$4$ endpoint-sliver structure of `(signedEvenThetaGauge b (neutralEvenThetaParam b c), shiftedGroundState a)` across $0 < 2c < \log 5$.
2. Overcome the $O(1/K)$ conductor-grading obstruction (`conductorGrading_obstruction_to_enteringConductor_payment`) in `ArithmeticHodgeTheoryOfDegenerations` by replacing orthogonal twists `twistedWeights g (primeTwist p) N` with non-orthogonal multiplicative-convolution / sublattice-shift vectors `dirichletShiftWeights d g₀ N` that couple directly at $O(1)$ to $W(\mathrm{halfWeight}\,h)$, and establish the exact necessary and sufficient condition for universal critical-curve stabilization across all stages $A \ge 0$.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, competing conjectures interrogated in Phases 1–4
- [x] 1 → 2  fully-proven: complete dependency-closed paper proofs below, `[PROVED HERE]`, zero open dependencies
- [x] 2 → 3  formalized: Lean modules `MultiPrimeDilationModulusAndIteratedWeilFloors`, `NeutralThetaGaugeOptimizationAndPrimeFourSliverFrontier`, `MultiplicativeConvolutionHorizonAndTailCancellation`, `lake --old env lean` exit 0, `#print axioms` `[propext, Classical.choice, Quot.sound]`

## Competing Conjectures & No-Go Closures
1. **Killed Conjecture A0 (`FALSE`):** Optimizing $(b, a)$ alone (sending $b \to \infty$ in `signedEvenThetaGauge b (neutralEvenThetaParam b c)` so that archimedean exterior jumps $\nu_\infty(b)/\cosh(b/2) = O(e^{-b}) \to 0$, and varying $a > 0$ in `shiftedGroundState a`) yields positive gauge potentials above $2c = \log 3$ without retaining variance or paying $\{2, 3, 4\}$ endpoint slivers.
   - **Exact killing mechanism:** `neutralEvenTheta_poleNeutral_invariance`, `tendsto_neutralEvenTheta_signedJump_and_variance_atTop`, and `odd_shiftedGroundState_variance_retention_necessary`. On the pole-neutral hyperplane $\mathrm{evenPoleMoment}(F) = 0$, the $(b, \alpha_0)$-dependent weight cancels identically between `signedJumpEnergy` and $2 \cdot \mathrm{chargeVariance}$; as $b \to \infty$, exterior prime-power jumps $\Lambda(n)/\sqrt{n}$ into the negative pockets at $\pm b$ retain $-2\bigl(\frac{1}{2} - \int_{-c}^c \Phi\cosh\bigr)\int (F^2/\Phi)\cosh$, conserving the exact ground-state outside cosh deficit; and in the odd sector, variance-dropped bounds fail for every $a > 0$ above $c = 273/400$.
   - **Strongest positive survivor:** Joint retained-variance and $\{2, 3, 4\}$ endpoint-sliver structure (`twoThreeFour_collarKicks_le_levyEnergy`, `primeSum_eq_two_sliver_of_collarWindow_lt_log_three`, `joint_neutralThetaGauge_and_twoThreeFour_sliver_equivalence`) together with the infinite strictly increasing tower of unconditional Weil-floor and sliver-floor apertures (`weilFloorApertureTower`, `weilQuad_sub_abs_orderedCoupling_ge_of_le_weilFloorApertureTower`).
2. **Killed Conjecture B0 (`FALSE`):** For every prime $p$, adding stage-$A$ multiplicative-convolution vectors `dirichletShiftWeights p g₀ N` ($g_0$ supported in $[-A, 0]$) stabilizes every nonzero $h$ on $[-(A + \log p), 0]$ along all critical curves $c_N^8 / \log N \to K$ ($K > 0$).
   - **Exact killing mechanism:** `shiftedHorizonProfile_eq_zero_of_gt_neg_log` and `dirichletShift_head_obstruction_necessity`. Because `shiftedHorizonProfile d g₀` vanishes identically on $(-\log d, 0]$ (and vanishes on all of $\mathbb{R}$ at $A = 0$ by continuity), universal stabilization across $A \ge 0$ forces $\mathrm{windowThreshold}(\log d) = \top$.
   - **Strongest positive survivor:** Open-head stabilization (`exists_dirichletShift_eventually_pos_of_windowThreshold_add_pos_eq_top`), unconditional $d = 2$ arbitrary-aperture critical-curve stabilization across all $A \ge 0$ and all $K > 0$ (`exists_primeTwo_dirichletShift_eventually_pos_all_criticalCurves`), and global equivalence across $d \ge 2$ (or primes $p$) with `RiemannHypothesis` (`forall_divisor_dirichletShift_stabilizes_iff_riemannHypothesis`).

---

## Complete Paper Proofs (`[PROVED HERE]`)

### Theorem 1 (Arbitrary-Radius Multi-Prime Dilation Modulus, Openness Across Prime Entries, and Infinite Aperture Tower)
Let $R > 0$ and $f \in C^2_c(\mathbb{R})$ satisfy $f(u) = 0$ for $|u| > R$.
1. **Arbitrary-radius polar bound and dilation cost:** For $|q|, |q'| \le 1/2$ and $|u| \le R$, $|e^{qu} - e^{q'u}| \le R e^{R/2} |q - q'|$, $|\int f(u) e^{qu}\,du| \le e^{R/2} \int |f|$, and $(\int |f|)^2 \le 2R \int f^2$. Writing $\mathrm{realPoleForm}(f) = 2 M_f(1/2) M_f(-1/2)$,
   $$|\mathrm{realPoleForm}(f)| \le 4 R e^R \int_{\mathbb{R}} f(u)^2\,du,$$
   and for every $r \ge 1$, setting $q = 1/(2r) \in (0, 1/2]$ so $|q - 1/2| \le (r - 1)/2$ and $|2/r - 2| \le 2(r - 1)$,
   $$|r\,\mathrm{realPoleForm}(f(r\,\cdot)) - \mathrm{realPoleForm}(f)| \le 4 R (R + 1) e^R (r - 1) \int_{\mathbb{R}} f(u)^2\,du.$$
2. **Multi-prime truncation and low-energy Lévy bound:** Since $|u|, |v| \le R \implies |u - v| \le 2R$, $\mathrm{autocorr}\,f(\log n) = 0$ whenever $\log n > 2R$, i.e., $n > \lfloor e^{2R}\rfloor_+$. Hence
   $$\mathrm{primeSum}(f) = \sum_{n \in \mathrm{Icc}\,2\,\lfloor e^{2R}\rfloor_+} 2\,\mathrm{vonMangoldtAtom}(n)\,\mathrm{autocorr}\,f(\log n).$$
   Define $P(R) := \sum_{n \in \mathrm{Icc}\,2\,\lfloor e^{2R}\rfloor_+} 2\,\mathrm{vonMangoldtAtom}(n) \ge 0$ and
   $$L(R) := 1 + 2|\gamma_{\mathrm{Hardy}}(0)| + P(R) + 4 R e^R.$$
   Whenever $\mathrm{fullZeroForm}(f) \le \int f^2$, $\mathrm{biScaleLevyEnergy}(f) \le L(R) \int_{\mathbb{R}} f(u)^2\,du$.
3. **Multi-prime dilation modulus:** Let $M_{\mathrm{max}}(R) := \max(1, 2R) \ge 1$ and $D(R) := P(R)\bigl(32 e^{1/2} L(R) + 2\bigr)$. For $r > 1$ with $(r - 1) M_{\mathrm{max}}(R) < 1$, both $\mathrm{primeSum}(f(r\,\cdot))$ and $\mathrm{primeSum}(f)$ truncate to $\mathrm{Icc}\,2\,\lfloor e^{2R}\rfloor_+$; applying `neg_log_mul_abs_autocorr_sub_le` termwise and combining with `archForm_logarithmic_dilation_bound` ($10\log r \int f^2$) and (1) gives, on $\mathrm{fullZeroForm}(f) \le \int f^2$:
   $$|r\,\mathrm{fullZeroForm}(f(r\,\cdot)) - \mathrm{fullZeroForm}(f)| \le \left(10\log r + 4 R (R + 1) e^R (r - 1) + \frac{D(R)}{-\log\bigl((r - 1) M_{\mathrm{max}}(R)\bigr)}\right)\int_{\mathbb{R}} f(u)^2\,du.$$
4. **Quantitative openness across arbitrary prime-power thresholds:** Suppose $R > 0$, $0 < \delta \le 1$, and $\mathrm{fullZeroForm}(g) \ge \delta \int g^2$ for all $g \in C^2_c(\mathbb{R})$ vanishing outside $[-R, R]$. Set $R_1 := (11/10) R$ and
   $$d(R, \delta) := \min\!\left(\frac{1}{10},\; \frac{\delta}{4\bigl(11 + 4 R_1 (R_1 + 1) e^{R_1}\bigr)},\; \frac{\exp\bigl(-1 - 4 D(R_1) / \delta\bigr)}{M_{\mathrm{max}}(R_1)}\right) > 0.$$
   For any $f \in C^2_c(\mathbb{R})$ vanishing outside $[-R(1 + d(R,\delta)),\, R(1 + d(R,\delta))] \subseteq [-R_1, R_1]$, $P(R_1)$ accounts for all prime powers up to $\lfloor e^{2.2 R}\rfloor_+$; contracting by $r = 1 + d(R,\delta)$ yields $\mathrm{fullZeroForm}(f) \ge (\delta/2)\int f^2$.
5. **Infinite strictly increasing tower of unconditional Weil-floor apertures:** Starting at $R_0 = \mathrm{successorWeilFloorAperture}$ with $\delta_0 = 1/20000$, setting $\delta_{k+1} = \delta_k / 2$ and $R_{k+1} = R_k (1 + d(R_k, \delta_k))$ gives $\mathrm{enlargedWeilFloorAperture} < \mathrm{successorWeilFloorAperture} = R_0 < R_k < R_{k+1}$ with unconditional real and complex Weil floor $\frac{1}{20000 \cdot 2^k}$ on $[-R_k, R_k]$. $\square$

---

### Theorem 2 (Exact Neutral Signed Theta-Gauge Conservation, Pole-Neutral Invariance, and $\{2, 3, 4\}$ Endpoint-Sliver Frontier up to $2c = \log 5$)
1. **Finite-$b$ decomposition & pole-neutral hyperplane $(b, \alpha_0)$-invariance:** Let $c > 0$ and $b \in \mathbb{R}$ satisfy $M_{b, \alpha_0^*(b,c)}^+(x) > 0$ on $[-(c+1), c+1]$. For every $F \in C^2_c(\mathbb{R})$ vanishing outside $[-c, c]$ (without evenness assumptions), let $u_{b,c}(x) := F(x) / \mathrm{regularizedEvenThetaProfile}(c, b, \alpha_0^*(b,c), x)$. Then
   $$2\,\mathrm{chargeVariance}\bigl(M_{b, \alpha_0^*}^+ \cosh(\cdot/2), (-c, c), u_{b,c}\bigr) = \alpha_0^*(b,c)\int_{\mathbb{R}} \frac{F(x)^2}{\mathrm{regularizedEvenThetaProfile}(c, b, \alpha_0^*(b,c), x)}\cosh\!\frac{x}{2}\,dx - 2\,\mathrm{evenPoleMoment}(F)^2,$$
   $$\mathrm{signedJumpEnergy}(M_{b, \alpha_0^*}^+, u_{b,c}) = \mathrm{markovEnergy}(F) + \alpha_0^*(b,c)\int_{\mathbb{R}} \frac{F(x)^2}{\mathrm{regularizedEvenThetaProfile}(c, b, \alpha_0^*(b,c), x)}\cosh\!\frac{x}{2}\,dx.$$
   On $\mathrm{evenPoleMoment}(F) = 0$, the $(b, \alpha_0)$-dependent integral cancels identically, leaving $\mathrm{archForm}(F) - \mathrm{primeSum}(F)$ independent of $b$.
2. **Asymptotic $b \to \infty$ rescaling and outside-deficit conservation:** Uniformly in $x \in \mathbb{R}$, $|M_{b,0}^+(x)/(2\cosh(b/2)) - \Phi(x)| \le \Phi(0)/\cosh(b/2) \to 0$. Hence $\alpha_0^*(b,c)/(2\cosh(b/2)) \to I_\Phi(c)/(\frac{1}{2} - I_\Phi(c))$ and $M_{b,\alpha_0^*(b,c)}^+(x)/(2\cosh(b/2)) \to \frac{1/2}{\frac{1}{2} - I_\Phi(c)}\Phi(x)$ ($I_\Phi(c) := \int_{(-c,c)}\Phi(x)\cosh(x/2)\,dx$). For every $F \in C^2_c$ supported in $[-c, c]$, as $b \to \infty$, $2\,\mathrm{chargeVariance}$ converges to $2 V_{\Phi\cosh}^{(-c,c)}(F/\Phi)$ while
   $$\lim_{b \to \infty} \mathrm{signedJumpEnergy}(M_{b, \alpha_0^*(b,c)}^+, u_{b,c}) = J_\Phi(F/\Phi) - 2\Bigl(\frac{1}{2} - I_\Phi(c)\Bigr)\int_{\mathbb{R}} \frac{F(x)^2}{\Phi(x)}\cosh\!\frac{x}{2}\,dx.$$
3. **Exact $\{2, 3, 4\}$ reflection truncation, half-window $n = 2$-only sliver law, sub-unit outward Lévy edge-carry up to $2c = \log 5$, and infinite-tower sliver floors:** For $0 < c < (\log 5)/2$ and $f \in C^2_c$ supported in $[m - c, m]$:
   - $\mathrm{orderedCoupling}\,f\,(\mathrm{collarReflect}\,m\,f) = \mathrm{collarHankel}\,m\,f - \sum_{n \in \{2, 3, 4\}} \mathrm{vonMangoldtAtom}(n)\,\mathrm{selfConv}\,f(2m - \log n)$.
   - Since $c < (\log 5)/2 < \log 3$, primes $3$ and $4$ do not enter $\mathrm{primeSum}(f)$: $\mathrm{primeSum}(f) = 2\,\mathrm{vonMangoldtAtom}(2)\,\mathrm{autocorr}\,f(\log 2)$ (vanishing identically for $c \le \log 2$).
   - Across $c \le (\log 5)/2$, $\sum_{n \in \{2, 3, 4\}} \mathrm{vonMangoldtAtom}(n)\,|\mathrm{selfConv}\,f(2m - \log n)| \le \bigl(\frac{3\log 2}{8} + \frac{\log 3}{6}\bigr)\sqrt{5}\,\mathrm{levyEnergy}(f)$, with $\bigl(\frac{3\log 2}{8} + \frac{\log 3}{6}\bigr)\sqrt{5} < \frac{991}{1000} < 1$.
   - For every $k \in \mathbb{N}$ and $0 < c \le \mathrm{weilFloorApertureTower}(k)$, $\mathrm{weilQuad}(f) - |\mathrm{orderedCoupling}\,f\,(\mathrm{collarReflect}\,m\,f)| \ge \frac{1}{20000 \cdot 2^k}\int f^2$. $\square$

---

### Theorem 3 (Non-Orthogonal Multiplicative-Convolution Horizon Vectors, Direct $O(1)$ Coupling, Sharp Head-Invariance Characterization, and Arbitrary-Aperture Tail Cancellation)
1. **Exact Ramanujan-divisibility decomposition and stage transport:** With $\mathrm{shiftedHorizonProfile}(d, g_0)(y) := g_0(y + \log d)$ and $\mathrm{dirichletShiftWeights}(d, g_0, N)(n) := 1_{d \mid n}\,\mathrm{horizonWeights}(\mathrm{shiftedHorizonProfile}(d, g_0), N)(n)$, at $N = d^2 M$ and $n = d m$ ($1 \le d, M, m$) one has $\mathrm{dirichletShiftWeights}(d, g_0, d^2 M)(d m) = d^{-1/2}\mathrm{horizonWeights}(g_0, M)(m)$, and for all $d \ge 1$:
   $$\mathrm{dirichletShiftWeights}(d, g_0, N)(n) = \mathrm{horizonWeights}\bigl(d^{-1}\,\mathrm{shiftedHorizonProfile}(d, g_0), N\bigr)(n) + \mathrm{twistedWeights}\bigl(d^{-1}\,\mathrm{shiftedHorizonProfile}(d, g_0), \mathrm{primeTwist}\,d, N\bigr)(n).$$
2. **Exact critical-curve limit, direct $O(1)$ coupling, and pure-tail annihilation:** For $A \ge 0$, $d > 1$, $h \in C^2$ on $[-(A + \log d), 0]$, and $g_0 \in C^2$ on $[-A, 0]$, along any critical curve $c_N^8 / \log N \to K > 0$, the normalized Weil form of $\mathrm{horizonWeights}(h, N) + \mathrm{dirichletShiftWeights}(d, g_0, N)$ converges to $\mathrm{windowPencil}(K, \mathrm{halfWeight}(h + d^{-1}\mathrm{shiftedHorizonProfile}(d, g_0))) + \frac{(d^8 - 1) 7 J(1)}{K} M_8(\mathrm{halfWeight}(d^{-1}\mathrm{shiftedHorizonProfile}(d, g_0)))$, carrying the $O(1)$ bilinear polarization cross-term $2\,\mathrm{splineAtom}\,d^{-1}\,\mathrm{weilPair}(\mathrm{halfWeight}\,h, \mathrm{halfWeight}(\mathrm{shiftedHorizonProfile}(d, g_0)))$. Any nonzero $h$ supported in $[-(A + \log d), -\log d]$ is annihilated identically at $O(1)$ by $g_0(u) = -d\,h(u - \log d)$.
3. **Head-obstruction necessity, open-head stabilization, unconditional $d = 2$ arbitrary-aperture stabilization, and global RH equivalence:**
   - **Necessity:** Universal stabilization across $A \ge 0$ and $K > 0$ implies $\mathrm{windowThreshold}(\log d) = \top$.
   - **Open-head sufficiency:** Whenever $\mathrm{windowThreshold}(\log d + \varepsilon) = \top$ ($\varepsilon > 0$), for every $A \ge 0$ and every $h \in C^2$ on $[-(A + \log d), 0]$ with $\mathrm{halfWeight}\,h \ne 0$, $g_0(u) := -d\,\mathrm{cutoff}(-(\log d + \varepsilon), -\log d, u - \log d)\,h(u - \log d)$ on $[-A, 0]$ makes the critical-curve limit and eventual `weilQuad (atomicTest ...)` strictly positive for **all** $K > 0$.
   - **Unconditional $d = 2$ theorem & global RH equivalence:** For every $k \in \mathbb{N}$, $\mathrm{windowThreshold}(2 \cdot \mathrm{weilFloorApertureTower}(k)) = \top$. Since $\log 2 < 2 \cdot \mathrm{weilFloorApertureTower}(0)$, $d = 2$ stabilizes every nonzero $h$ on $[-(A + \log 2), 0]$ unconditionally for **all** $A \ge 0$ and **all** $K > 0$; globally across $d > 1$ (or primes $p$), universal stabilization is equivalent to `RiemannHypothesis`. $\square$

---

## Lean Formalization
- **`GaloisForLFunctions.ArithmeticIncidencePositivity.MultiPrimeDilationModulusAndIteratedWeilFloors`:**
  - `abs_realPoleForm_le_of_radius`, `realPoleForm_dilation_bound_of_radius`
  - `primeSum_eq_finsetSum_of_radius`, `biScaleLevyEnergy_le_of_fullZeroForm_le_mass_of_radius`
  - `fullZeroForm_dilation_bound_of_radius`, `multiPrimeApertureStep`, `fullZeroForm_ge_of_dilated_radius`
  - `weilFloorApertureTower`, `weilFloorApertureTower_strictMono`, `enlargedWeilFloorAperture_lt_weilFloorApertureTower`
  - `fullZeroForm_ge_of_support_le_weilFloorApertureTower`, `zetaZeroConfig_re_W_ge_of_aperture_le_weilFloorApertureTower`
- **`GaloisForLFunctions.SignedWindowCriticality.NeutralThetaGaugeOptimizationAndPrimeFourSliverFrontier`:**
  - `neutralEvenTheta_signedJump_and_variance_eq`, `neutralEvenTheta_poleNeutral_invariance`, `odd_shiftedGroundState_variance_retention_necessary`
  - `tendsto_neutralEvenThetaParam_div_two_cosh_atTop`, `tendsto_signedEvenThetaProfile_neutral_div_two_cosh_atTop`, `tendsto_neutralEvenTheta_signedJump_and_variance_atTop`
  - `orderedCoupling_collarReflect_eq_two_three_four_of_lt_half_log_five`, `primeSum_eq_two_sliver_of_collarWindow_lt_log_three`, `twoThreeFour_collarKicks_le_levyEnergy`
  - `weilQuad_sub_abs_orderedCoupling_ge_of_le_weilFloorApertureTower`, `joint_neutralThetaGauge_and_twoThreeFour_sliver_equivalence`
- **`GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.MultiplicativeConvolutionHorizonAndTailCancellation`:**
  - `shiftedHorizonProfile`, `dirichletShiftWeights`, `dirichletShiftWeights_mul_sq_eq`, `shiftedHorizonProfile_eq_zero_of_gt_neg_log`, `dirichletShiftWeights_eq_horizon_add_twisted`
  - `dirichletShift_orderOne_crossTerm_eq`, `dirichletShift_criticalCurve_exact`, `dirichletShift_criticalCurve_prime`, `pureTail_exact_orderOne_annihilation`
  - `dirichletShift_head_obstruction_necessity`, `exists_dirichletShift_eventually_pos_of_windowThreshold_add_pos_eq_top`
  - `weilQuad_ge_of_le_two_mul_weilFloorApertureTower`, `windowThreshold_eq_top_of_le_two_mul_weilFloorApertureTower`
  - `exists_primeTwo_dirichletShift_eventually_pos_all_criticalCurves`, `forall_divisor_dirichletShift_stabilizes_iff_riemannHypothesis`

## Log
- 2026-11-05 — dependency-closed paper proofs completed in `2-fully-proven`
- 2026-11-05 — formalized unconditionally in Lean 4 (`lake --old env lean` exit 0, `#print axioms` `[propext, Classical.choice, Quot.sound]`) and promoted to `3-formalized`
