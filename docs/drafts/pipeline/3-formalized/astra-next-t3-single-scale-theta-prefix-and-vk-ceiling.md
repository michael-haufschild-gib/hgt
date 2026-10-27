# Quantitative Single-Scale Integer Theta Prefix Transfer and Unconditional Vinogradov–Korobov Sub-Trivial Prefix Ceiling (`RBG` Open Topic #2)

- **ID:** astra-next-t3-single-scale-theta-prefix-and-vk-ceiling
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4 formalized)
- **Source:** docs/reports/review-2710/astra.md · Focus Question 3 / `RenormalizedBiarithmeticGeometry/README.md` Open Topic #2
- **Statement:** Explicit all-`n ≥ 1` integer-theta prefix-to-defect and electrostatic moment-of-inertia bounds (`heckeDefect_le_of_explicit_reading`, `depthSecondMoment_le_of_explicit_reading`), exact single-scale logarithmic-horizon integer-prefix equivalence (`zetaZeroAbscissa ≤ 1 - θ`, `GrowingEndpointEscapedMoebiusLaw θ`, and `RiemannHypothesis` along `dyadicThetaPrefix k = ⌊exp(2^k/2)⌋₊ + 1`), and the first unconditional sub-trivial single-scale upper bound on `RBG.reading f L 1 n` across `|L| ≤ 2 log(n + 1)` beating the trivial strip ceiling `mass f · (n + 1)^2` by the Vinogradov–Korobov factor `exp(-4 δ_VK(n + 2) log(n + 1))` (`tendsto_reading_logHorizon_div_sq_zero`).
- **Lean Module:** `formal/GaloisForLFunctions/BezoutValuationIncidence/SingleScaleThetaPrefixTransferAndVKCeiling.lean`

## Goal
Attack `RenormalizedBiarithmeticGeometry` Open Topic #2 ("Single-scale bounds on the integer theta prefix readings") via `heckeDefect_le_depthKernel_of_dyadic_exp_rate` (`UnconditionalEscapedMoebiusDecayAndCrossRouteBridge.lean`), `RBG.heckeDefect_le_of_readings` (`IntegerThetaPrefixesReadTheDefectWithoutLoss.lean`), and `AES.moment_le_heckeDefect` (`TheHeckeDefectIsTheMomentOfInertia.lean`):
1. Replace the existential `∃ N(f, ε)` threshold in `RBG.heckeDefect_le_of_readings` by a quantitative all-`n ≥ 1` finite-prefix transfer certificate and electrostatic transverse moment-of-inertia bound using `CDG.exists_finiteThetaSource_logarithmic_error_bound`.
2. Establish the exact single-scale logarithmic-horizon integer-prefix equivalence for `zetaZeroAbscissa ≤ 1 - θ` (`0 < θ ≤ 1/2`), `GrowingEndpointEscapedMoebiusLaw θ`, and `RiemannHypothesis`.
3. Prove unconditionally that at the single-scale logarithmic horizon `|L| ≤ 2 log(n + 1)`, both `heckeDefect f L` and the finite integer-theta curvature reading `RBG.reading f L 1 n` beat the trivial strip ceiling `mass f · (n + 1)^2` by an explicit Vinogradov–Korobov factor `exp(-4 min(η₁, vkZeroFreeWidth(n + 2)) log(n + 1)) + O_f((log n)/n)`, forcing `reading f (L n) 1 n / (n + 1)^2 → 0` for every `f : CompactTest` and every `|L n| ≤ 2 log(n + 1)`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, internal corpus audit completed
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `SingleScaleThetaPrefixTransferAndVKCeiling.lean`, `lake --old env lean` green, axiom check PASS

## Approach & Complete Dependency-Closed Paper Proof (`[PROVED HERE]`)

### 1. Explicit All-`n` Lossless Prefix-to-Defect Transfer
For any `f : CompactTest` and moment order $j \in \{0, 1\}$, `CDG.exists_finiteThetaSource_logarithmic_error_bound f j` at $\tau = 0$ (`sourceTwist 0 f = f`) supplies constants $B_j, D_j \ge 0$ such that for **every** $n \ge 1$ and every $L \in \mathbb{R}$ with $j |L| \le 2 \log(n + 1)$,
$$|\operatorname{reading}(f, L, j, n) - \operatorname{depthMoment}(f, L, j)| \le \mathcal{E}_{B_j, D_j}(n) := B_j e^{-n^4 + 56 n^2 + 62} + D_j \frac{16}{n}\bigl(C_{\xi, 2} + \log(n + 4)\bigr).$$
In particular, at $j = 1$ ($\operatorname{depthMoment}(f, L, 1) = \operatorname{heckeDefect}(f, L)$) and $j = 0, L = 0$ ($\operatorname{depthMoment}(f, 0, 0) = \operatorname{mass}(f)$):
- **Explicit finite-`n` transfer (`heckeDefect_le_of_explicit_reading`):** For every $n \ge 1$, $k \in \mathbb{N}$, and $L, \varphi \in \mathbb{R}$ with $2^k |L| \le 2 \log(n + 1)$, if
  $$\operatorname{reading}(f, 2^k L, 1, n) + \mathcal{E}_{B_1, D_1}(n) \le \bigl(\operatorname{reading}(f, 0, 0, n) - \mathcal{E}_{B_0, D_0}(n)\bigr)(2\cosh(2^k\varphi) - 2),$$
  then $\operatorname{heckeDefect}(f, 2^k L) \le \operatorname{mass}(f)(2\cosh(2^k\varphi) - 2)$, and `RBG.heckeDefect_le_of_dyadic_le` gives $\operatorname{heckeDefect}(f, L) \le \operatorname{mass}(f)(2\cosh\varphi - 2)$ with zero loss.

### 2. Single-Scale Logarithmic-Horizon Integer-Prefix Equivalence for `zetaZeroAbscissa ≤ 1 - θ` and `RH`
Fix $0 < \theta \le 1/2$. For any dyadic scale $2^k$ ($k \in \mathbb{N}$), define the canonical minimal admissible prefix length
$$n_{\mathrm{hor}}(k) := \lfloor \exp(2^{k - 1}) \rfloor_+ \quad (\text{or } \lceil \exp(2^k / 2) \rceil_+ : \; n_k := \lfloor \exp(2^k / 2) \rfloor_+ + 1).$$
Observe that $n_k := \lfloor \exp(2^k / 2) \rfloor_+ + 1 \ge 2$ satisfies $\exp(2^k / 2) < (n_k : \mathbb{R}) < (n_k : \mathbb{R}) + 1 \le \exp(2^k / 2) + 2 \le 3 \exp(2^k / 2)$, hence:
- $2^k = 2 \log(\exp(2^k / 2)) \le 2 \log(n_k + 1)$ (so $L = 2^k$ lies inside the logarithmic horizon of prefix $n_k$ for **every** $k \in \mathbb{N}$!);
- $\exp(2^k) < (n_k + 1)^2 \le 9 \exp(2^k)$.
Combining $|\operatorname{reading}(f, 2^k, 1, n_k) - \operatorname{heckeDefect}(f, 2^k)| \le \mathcal{E}_{B_1, D_1}(n_k) = O_f(1)$ ($n_k \ge 1$, and $\mathcal{E}_{B_1, D_1}(n) \to 0$ as $n \to \infty$) with `heckeDefect_le_depthKernel_of_dyadic_exp_rate` and `zetaZeroAbscissa_le_iff_dyadic_heckeDefect_rate` (`UnconditionalEscapedMoebiusDecayAndCrossRouteBridge.lean:618`):
- **Single-scale prefix characterization (`zetaZeroAbscissa_le_iff_singleScale_reading_rate`):**
  $$\operatorname{zetaZeroAbscissa} \le 1 - \theta \iff \forall f : \mathrm{CompactTest},\; \forall \varepsilon > 0,\; \exists C \ge 0,\; \forall k \in \mathbb{N},\; \operatorname{reading}(f, 2^k, 1, n_k) \le C (n_k + 1)^{2(1 - 2\theta) + \varepsilon}.$$
- **Endpoint (`riemannHypothesis_iff_singleScale_reading_subpoly`):** Taking $\theta = 1/2$ (`zetaZeroAbscissa_le_half_iff_riemannHypothesis`), `RiemannHypothesis` holds **if and only if** for every `f : CompactTest` and $\varepsilon > 0$, $\operatorname{reading}(f, 2^k, 1, n_k) = O_{f, \varepsilon}((n_k + 1)^\varepsilon)$.

### 3. Unconditional Vinogradov–Korobov Sub-Trivial Ceiling on `heckeDefect` and `RBG.reading`
We prove unconditionally that `RBG.reading f L 1 n` beats the trivial strip ceiling $\operatorname{mass}(f)(n + 1)^2$ along $|L| \le 2 \log(n + 1)$ for every `f : CompactTest`:
1. **Two-sided carrier depth bound (`abs_zetaDepth_le_half_sub_vkProfile`):**
   Let $\gamma_0 \ge \exp(e^{30})$ be the threshold from `SRT.exists_re_le_of_mem_zetaCarrier_vk`, and define for $G \ge \gamma_0$:
   $$\delta_{\mathrm{VK}}(G) := \min\!\Bigl(\frac{1}{58 \log \gamma_0},\; \operatorname{vkZeroFreeWidth}(G)\Bigr) > 0.$$
   Let $\rho \in \operatorname{zetaZeroConfig.carrier}$ satisfy $|(\rho : \mathbb{C}).\mathrm{im}| \le G$:
   - If $|\rho.\mathrm{im}| \le \gamma_0$, `RHTower.four_le_abs_im_of_zeta_zero` gives $4 \le |\rho.\mathrm{im}| \le \gamma_0$, hence $0 < \log |\rho.\mathrm{im}| \le \log \gamma_0$, and `re_le_one_sub_of_zeta_zero` + `one_div_le_re_of_zeta_zero` give $\frac{1}{58 \log \gamma_0} \le \rho.\mathrm{re} \le 1 - \frac{1}{58 \log \gamma_0}$, so $|\operatorname{zetaDepth}(\rho)| \le \frac{1}{2} - \delta_{\mathrm{VK}}(G)$.
   - If $\gamma_0 < |\rho.\mathrm{im}| \le G$, `exists_re_le_of_mem_zetaCarrier_vk` applied to both $\rho$ and $1 - \rho \in \operatorname{carrier}$ (`riemannZeta_one_sub_eq_zero_of_mem_openStrip`, $|(1 - \rho).\mathrm{im}| = |\rho.\mathrm{im}|$), together with `vkZeroFreeWidth_antitone` ($\exp(e^{30}) \le \gamma_0 < |\rho.\mathrm{im}| \le G$), gives $\operatorname{vkZeroFreeWidth}(G) \le \rho.\mathrm{re} \le 1 - \operatorname{vkZeroFreeWidth}(G)$, so again $|\operatorname{zetaDepth}(\rho)| \le \frac{1}{2} - \delta_{\mathrm{VK}}(G)$.
2. **Cutoff trace splitting on $|L| \le 2 \log(n + 1)$ (`heckeDefect_logHorizon_le_vk`):**
   Fix $f : \mathrm{CompactTest}$. By `CDG.moving_depth_trace_tail_le f 1` at $\tau = 0$, there exists $C_{\mathrm{tail}} \ge 0$ such that for all $n \in \mathbb{N}$ and $|L| \le 2 \log(n + 1)$,
   $$\operatorname{heckeDefect}(f, L) \le \sum_{\rho} \operatorname{sourceCutoff}(n, \rho) \operatorname{zetaWeight}(f, \rho) \operatorname{depthKernel}(L, \operatorname{zetaDepth}(\rho)) + C_{\mathrm{tail}} \operatorname{sourceReferenceTail}(n),$$
   since $\operatorname{zetaSourceTrace}(\operatorname{sourceDepthKernel}(f, L, 1)) = \operatorname{heckeDefect}(f, L)$!
   Whenever $\operatorname{sourceCutoff}(n, \rho) \ne 0$, $\rho \in \operatorname{support}(\operatorname{sourceCutoff}(n)) = \operatorname{ball}(0, n + 2)$, so $|\rho.\mathrm{im}| \le \|\rho\| < n + 2$. Thus for all $n \in \mathbb{N}$ with $(n : \mathbb{R}) + 2 \ge \gamma_0$, every surviving $\rho$ has $|\operatorname{zetaDepth}(\rho)| \le \frac{1}{2} - \delta_{\mathrm{VK}}(n + 2)$.
   Since $2\cosh(x) - 2 = e^x + e^{-x} - 2 \le e^x$ for all $x \ge 0$ (`depthKernel_le_exp_two_mul`: for $0 \le d$, $\operatorname{depthKernel}(L, d) = 2\cosh(2 d |L|) - 2 \le \exp(2 d |L|)$), on $|L| \le 2 \log(n + 1)$ and $0 \le \delta_{\mathrm{VK}}(n + 2) \le \frac{1}{2}$:
   $$\operatorname{depthKernel}\bigl(L, \tfrac{1}{2} - \delta_{\mathrm{VK}}(n + 2)\bigr) \le \exp\bigl((1 - 2\delta_{\mathrm{VK}}(n + 2)) \cdot 2\log(n + 1)\bigr) = (n + 1)^2 \exp\bigl(-4 \delta_{\mathrm{VK}}(n + 2) \log(n + 1)\bigr).$$
   Using $0 \le \operatorname{sourceCutoff}(n, \rho) \le 1$, summing over $\rho$ yields for all $(n : \mathbb{R}) + 2 \ge \gamma_0$ and $|L| \le 2 \log(n + 1)$:
   $$\operatorname{heckeDefect}(f, L) \le \operatorname{mass}(f) \cdot (n + 1)^2 \exp\bigl(-4 \delta_{\mathrm{VK}}(n + 2) \log(n + 1)\bigr) + C_{\mathrm{tail}} \operatorname{sourceReferenceTail}(n).$$
3. **Transfer to `RBG.reading` and Asymptotic Sub-Triviality (`reading_logHorizon_le_vk`, `tendsto_reading_logHorizon_div_sq_zero`):**
   Combining item 2 with `exists_finiteThetaSource_logarithmic_error_bound f 1` gives unconditionally for all $n \ge 1$ with $(n : \mathbb{R}) + 2 \ge \gamma_0$ and $|L| \le 2 \log(n + 1)$:
   $$\operatorname{reading}(f, L, 1, n) \le \operatorname{mass}(f) \cdot (n + 1)^2 \exp\bigl(-4 \delta_{\mathrm{VK}}(n + 2) \log(n + 1)\bigr) + C_{\mathrm{tail}} \operatorname{sourceReferenceTail}(n) + \mathcal{E}_{B_1, D_1}(n).$$
   Finally, for large $n$, $\delta_{\mathrm{VK}}(n + 2) = \operatorname{vkZeroFreeWidth}(n + 2) = \frac{(\log(n + 2))^{-2/3}(\log\log(n + 2))^{-5/3}}{10^8}$, while $\log(n + 1) \ge \frac{1}{2} \log(n + 2)$, so $4 \delta_{\mathrm{VK}}(n + 2) \log(n + 1) \ge \frac{2}{10^8} (\log(n + 2))^{1/3}(\log\log(n + 2))^{-5/3} \to +\infty$ (since $x^{1/3} (\log x)^{-5/3} \to +\infty$ as $x = \log(n + 2) \to +\infty$), whereas $\operatorname{sourceReferenceTail}(n) \to 0$ and $\mathcal{E}_{B_1, D_1}(n) \to 0$. Dividing by $(n + 1)^2 \ge 1$ proves unconditionally:
   $$\lim_{n \to \infty} \sup_{|L| \le 2\log(n+1)} \frac{\operatorname{reading}(f, L, 1, n)}{(n + 1)^2} = 0$$
   (in particular $\operatorname{reading}(f, 2\log(n + 1), 1, n) / (n + 1)^2 \to 0$) for **every** `f : CompactTest`!

## Log
- 2026-10-27 — created and completed dependency-closed paper proof in `2-fully-proven/`
- 2026-10-27 — formalized unconditionally in `SingleScaleThetaPrefixTransferAndVKCeiling.lean` (`lake --old env lean` exit 0, zero warnings, wired into `BezoutValuationIncidence.lean`), moved to `3-formalized/`
