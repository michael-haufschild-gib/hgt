# Logarithmic-Scale Hecke Defect vs. Prime Polynomial: Self-Absorption, Corridor Rigidity, and Pole-Nodal Dyadic RH Equivalence

- **ID:** wd-log-scale-hecke-defect-prime-polynomial-resolution
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `ConjugateDiagonalGeometry` · `docs/reports/rh-current-frontier-map.md` (`#wd`, `B17b`, `obstacles-summary.md` §2.6.3)
- **Lean Modules:**
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.ArchimedeanAndKernelFoundations`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.PrimePolynomialSelfAbsorption`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.FiniteStratumAndCorridorClassification`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.DyadicPoleNodalRHEquivalence`
- **Lean Declarations:**
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_depthKernel_scale_transfer`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_norm_tr_twist_baseBump_le_pow`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.unitWindow_depthCharge_le_heckeDefect`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.normSq_tr_twist_heckeAvgBump_le_of_sep_strip`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_abs_re_archPart_sub_pole_heckeAvgBump_le`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_abs_re_archPart_heckeAvgBump_log_le`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.abs_re_W_le_collidedForm`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.unitWindow_integral_normSq_tr_twist_heckeAvgBump_le`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_unitWindow_integral_collidedForm_heckeAvgBump_le_of_zeroConfig`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_unitWindow_integral_norm_primePolynomial_le`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_rvm_zeroConfig_not_heckeDefect_le_spectralDeviation`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_heckeDefect_log_le_div_pow_of_finiteOffLine`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_heckeDefect_log_le_primePolynomial_any_cutoff_of_finiteOffLine`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_heckeDefect_log_le_neg_re_primePolynomial_of_finiteOffLine`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.unitWindowDepthCharge_log_iff_of_pos`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.heckeDefect_log_unitWindow_tfae`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.eventually_heckeDefect_le_pos_re_primePolynomial_iff`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_log_zeroFree_corridor_of_heckeDefect_bound`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.zerosApproachLine_and_lindelof_of_heckeDefect_log_bound`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.three_lt_abs_im_of_mem_zetaZeroConfig`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_zero_avoiding_subinterval_in_unitWindow`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_poleNodal_ordinate_in_Icc`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.riemannHypothesis_iff_dyadic_heckeDefect_le_primePolynomial`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.riemannHypothesis_of_dyadic_heckeDefect_le_neg_re_primePolynomial`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.riemannHypothesis_iff_forall_scale_heckeDefect_le_primePolynomial`
- **Statement:**
  Write $E_\gamma(L) := \operatorname{heckeDefect}(\operatorname{baseTwistTest}\,\gamma, L)$, $F_L := \operatorname{heckeAvgBump}(L)$, $N^*(L) := \lfloor e^{2(L + 1/4)}\rfloor_+$, and $\Pi_{F_L}(\gamma) := \operatorname{primePolynomial}(F_L, N^*(L), -\gamma/(2\pi))$ (purely real by `im_primePolynomial_eq_zero`). At $L = c\log T$ uniformly over $\gamma \in [T, T+1)$:
  1. **Unconditional Unit-Window Self-Absorption of $\Pi_{F_{c\log T}}$ and Universal Zero-Configuration No-Go (`exists_unitWindow_integral_norm_primePolynomial_le`, `exists_rvm_zeroConfig_not_heckeDefect_le_spectralDeviation`):**
     For every $c > 0$, there exist $C_1(c) > 0$ and universal $C_2 = 8\pi/\cos^2(3/4) + 1 > 0$ (independent of $c$) such that eventually in $T$,
     $$\int_T^{T+1} \big\|\Pi_{F_{c\log T}}(\gamma)\big\|\,d\gamma \le C_1(c) + \frac{C_2}{c\log T}\int_T^{T+1} E_\gamma(c\log T)\,d\gamma.$$
     Consequently, $\Pi_{F_{c\log T}}$ carries at most an $O(1/\log T) = o(1)$ fraction of $E_\gamma(c\log T)$ across $[T, T+1)$ and cannot pay for unbounded Hecke defect. On the superposed configuration $Z' = \operatorname{superpose}(\operatorname{zetaZeroConfig}, \operatorname{clusterConfig})$ (`RiemannVonMangoldt Z'`, $Z'.N_0 = \operatorname{zetaZeroConfig}.N_0$), for every $c > 0$, $\alpha \ge 0$, and $C \in \mathbb{R}$, the spectral-deviation functional $|\operatorname{Re} A_{F_{c\log T}}(-\gamma/(2\pi)) - \operatorname{Re} W_{Z'}(\operatorname{twist}_\gamma F_{c\log T}, \operatorname{twist}_\gamma F_{c\log T})|$ fails to bound $E_{Z',\gamma}(c\log T)$ up to $C$ uniformly on $[T, T+1)$, even though $\operatorname{primeEnvelope}(F_{c\log T}) \asymp T^{2c}/\log T \gg T^c$.
  2. **Super-Polynomial Decay on `FiniteOffLine` (`exists_heckeDefect_log_le_div_pow_of_finiteOffLine`, `exists_heckeDefect_log_le_primePolynomial_any_cutoff_of_finiteOffLine`, `exists_heckeDefect_log_le_neg_re_primePolynomial_of_finiteOffLine`):**
     Under `FiniteOffLine` (including the non-RH stratum `FiniteOffLine ∧ ¬RiemannHypothesis`), for every $c > 0$ and every $N \in \mathbb{N}$, there exists $C > 0$ such that $E_\gamma(c\log T) \le C / T^N$ for all $T \ge 2$ and $\gamma \in [T, T+1)$. Hence for every $c > 0$, every prime cutoff $M : \mathbb{R} \to \mathbb{N}$ (including $\lfloor T^{2c}\rfloor_+$ and $N^*(c\log T)$), and every $\alpha \ge 0$, both $E_\gamma(c\log T) \le \alpha\|\operatorname{primePolynomial}(F_{c\log T}, M(T), -\gamma/(2\pi))\| + C$ and $E_\gamma(c\log T) \le -\alpha\operatorname{Re}\Pi_{F_{c\log T}}(\gamma) + C'$ hold for all $T \ge 2$ and $\gamma \in [T, T+1)$ without implying `RiemannHypothesis`.
  3. **Five-Way Equivalence, All-$c$ Scale Rigidity, Positive-Sign Separation, and `LindelofCriticalLine` (`heckeDefect_log_unitWindow_tfae`, `unitWindowDepthCharge_log_iff_of_pos`, `eventually_heckeDefect_le_pos_re_primePolynomial_iff`, `exists_log_zeroFree_corridor_of_heckeDefect_bound`, `zerosApproachLine_and_lindelof_of_heckeDefect_log_bound`):**
     - **Five-way TFAE:** For every $c > 0$ and $\alpha \ge 0$, eventual uniform bounds on $[T, T+1)$ by $\alpha\|\Pi_{F_{c\log T}}\| + C$, by $-\alpha\operatorname{Re}\Pi_{F_{c\log T}} + C$, by a bare constant $B$ ($\Pi_{F_{c\log T}}$ eliminated), in $L^1([T, T+1))$, and on $\operatorname{unitWindowDepthCharge}(T, c\log T)$ are mutually equivalent (`TFAE`) and invariant under changing $c > 0$ to any $c' > 0$.
     - **Positive-sign separation:** For $c > 0$ and $\alpha > 0$, $E_\gamma(c\log T) \le +\alpha\operatorname{Re}\Pi_{F_{c\log T}}(\gamma) + C$ holds uniformly on $[T, T+1)$ eventually in $T$ iff both $E_\gamma(c\log T) = O(1)$ and $D_\zeta(\operatorname{twist}_\gamma F_{c\log T}) = O(1)$.
     - **Unconditional implications:** Any of the 5 TFAE conditions unconditionally implies $|\operatorname{Re}\rho - 1/2| \le A/\log|\operatorname{Im}\rho|$ for $|\operatorname{Im}\rho| \ge T_1$, `ZerosApproachLine`, `OffLineSparse`, `LindelofCriticalLine`, and $\exists \beta < 1/2,\ \operatorname{XiZeroHalfPlaneBound}(\beta)$.
  4. **Zero-Avoiding Pole-Nodal Dyadic Equivalence to `RiemannHypothesis` (`exists_poleNodal_ordinate_in_Icc`, `riemannHypothesis_iff_dyadic_heckeDefect_le_primePolynomial`, `riemannHypothesis_of_dyadic_heckeDefect_le_neg_re_primePolynomial`, `riemannHypothesis_iff_forall_scale_heckeDefect_le_primePolynomial`):**
     For every $c_0 > 0$ and $\alpha \ge 0$,
     $$\mathrm{RiemannHypothesis} \;\Longleftrightarrow\; \exists C \in \mathbb{R},\ \forall k \in \mathbb{N},\ \forall T \ge 2,\ \forall \gamma \in [T, T+1),\ E_\gamma(2^k c_0 \log T) \le \alpha\big\|\Pi_{F_{2^k c_0 \log T}}(\gamma)\big\| + C,$$
     equivalently across all $c > 0$ with a single constant $C$, and with unconditional signed converse from $E_\gamma(2^k c_0 \log T) \le -\alpha\operatorname{Re}\Pi_{F_{2^k c_0 \log T}}(\gamma) + C$.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: 4 Lean modules in `ConjugateDiagonalGeometry/LogScaleHeckeDefect/`, `lake --old env lean` exit 0, `#print axioms` `[propext, Classical.choice, Quot.sound]` PASS

## Proof `[PROVED HERE]`
1. **All-$c$ $C_c^\infty$ rapid pole-decay and two-sided archimedean bounds:**
   Since $F_L = \operatorname{heckeAvgBump}(L)$ is real and even, the $s = 0, 1$ pole sum in $\operatorname{Re} A_{F_L}(-\gamma/(2\pi))$ equals $2\operatorname{Re}(\operatorname{tr}(\operatorname{twist}_\gamma F_L)(1)^2)$. Integrating by parts $K$ times on $[-1, 1]$ (`exists_norm_tr_twist_baseBump_le_pow`) bounds $\|\operatorname{tr}(\operatorname{twist}_\gamma h_0)(s)\| \le C_K / |\operatorname{Im} s - \gamma|^K$ uniformly on $|\operatorname{Re} s - 1/2| \le 1/2$. Choosing $K = \lceil c\rceil_+ + 1$ at $L = c\log T$ and $\gamma \in [T, T+1)$ ($T \ge 2$) absorbs $e^{c\log T}/\gamma^{2K} \le 1$ and combines with two-sided $\mu$-integral bounds to give $|\operatorname{Re} A_{F_{c\log T}}(-\gamma/(2\pi))| \le C_{\mathrm{arch}}(c)$ for every $c > 0$.
2. **Near-ordinate `baseBump` coercivity and separated-ordinate `heckeAvgBump` decay:**
   Evenness and nonnegativity of $h_0$ on $[-1/4, 1/4]$ give $\operatorname{normSq}(\operatorname{tr}(\operatorname{twist}_\gamma h_0)(s)) \ge \cos^2(A/4)$ whenever $|\operatorname{Im} s - \gamma| \le A < 2\pi$ (`cos_quarter_mul_sq_le_normSq_tr_twist_baseBump`), coercing $E_\gamma(L)$ on $[T, T+1)$ from below by $\cos^2(1/4)\operatorname{unitWindowDepthCharge}(T, L)$. For $|\operatorname{Im} s - \gamma| \ge \eta > 0$, exact evaluation of $\int_{-L}^L e^{z\ell}\,d\ell$ decomposes $\operatorname{normSq}(\operatorname{tr}(\operatorname{twist}_\gamma F_L)(s))$ into an $O((1 + \eta^{-2})L^{-2}(1 + (\gamma - \operatorname{Im} s)^2)^{-1})$ Lorentzian term plus $(4\eta^2 L^2)^{-1}\operatorname{normSq}(\operatorname{tr}(\operatorname{twist}_\gamma h_0)(s))\operatorname{depthKernel}(L, \delta)$ (`normSq_tr_twist_heckeAvgBump_le_of_sep_strip`).
3. **Self-absorption of $\Pi_{F_{c\log T}}$ and the `RiemannVonMangoldt` no-go:**
   Invariance of $Z.\mathrm{mult}$ under `reflEquiv` yields $|\operatorname{Re} W_Z(f, f)| \le D_Z(f)$. Splitting $Z.\mathrm{carrier}$ into $Z.\mathrm{window}(T - 2, T + 3)$ (bounded via Plancherel + $\sinh^2(\delta u) \le 4\operatorname{depthKernel}(L, \delta)$ on $|u| \le L + 1/4$ + $N_Z(T - 2, T + 3) \ll \log T$) and its complement ($|\operatorname{Im}\rho - \gamma| \ge 2$) proves self-absorption on any `RiemannVonMangoldt` configuration with logarithmic Lorentzian growth, specializing to $\zeta$ (`exists_unitWindow_integral_norm_primePolynomial_le`) and refuting the spectral-deviation bound on $\operatorname{superpose}(\operatorname{zetaZeroConfig}, \operatorname{clusterConfig})$ at $T_k = e^{e^k}$ (`exists_rvm_zeroConfig_not_heckeDefect_le_spectralDeviation`).
4. **Super-polynomial decay under `FiniteOffLine`:**
   Under `FiniteOffLine`, $E_\gamma(L)$ reduces globally to a fixed finite sum over $|\operatorname{Im}\rho| \le R_0$, where $K = N + \lceil c\rceil_+ + 1$ Paley–Wiener rapid decay bounds $E_\gamma(c\log T) \le C/T^N$ on $[T, T+1)$ for all $T \ge 2$.
5. **Hyperbolic scale transfer, 5-way TFAE, positive-sign separation, and `LindelofCriticalLine`:**
   Iterating `depthKernel_double` transfers bounded `depthKernel` across scales (`exists_depthKernel_scale_transfer`), proving all-$c$ invariance (`unitWindowDepthCharge_log_iff_of_pos`) and upgrading unit-window depth charge to the full series $E_\gamma(c\log T)$ via `Real.tsum_le_of_sum_le` (`eventually_heckeDefect_le_of_unitWindowDepthCharge_le`). Self-absorption closes `(1) → (4)` in `heckeDefect_log_unitWindow_tfae`, capacity balance closes `eventually_heckeDefect_le_pos_re_primePolynomial_iff`, and quadratic coercivity yields the logarithmic corridor (`exists_log_zeroFree_corridor_of_heckeDefect_bound`) and `ZerosApproachLine ∧ OffLineSparse ∧ LindelofCriticalLine` (`zerosApproachLine_and_lindelof_of_heckeDefect_log_bound`).
6. **Pole-nodal dyadic equivalence to `RiemannHypothesis`:**
   Any putative off-line zero has $|\operatorname{Im}\rho| > 3$ (`three_lt_abs_im_of_mem_zetaZeroConfig`); pigeonholing $[T_0, T_0 + 1]$ ($T_0 = \operatorname{Im}\rho_0 - 1/2 \ge 2$) against `finite_window` yields a zero-avoiding subinterval $[a_0, b_0]$ (`exists_zero_avoiding_subinterval_in_unitWindow`), on which the four-phase grid $2\gamma L \in 2\pi\mathbb{Z} + \{0, \pi/2, \pi, 3\pi/2\}$ forces a sign change and zero $\gamma_L \in [a_0, b_0]$ of $\operatorname{Re}(\operatorname{tr}(\operatorname{twist}_\gamma F_L)(1)^2)$ (`exists_poleNodal_ordinate_in_Icc`). Evaluating at $L_k = 2^k c_0\log T_0$ annihilates the exponential pole and traps $\frac{1}{2}E_{\gamma_k}(L_k)$ between $O_{T_0,\alpha,C}(1)$ and $2\cos^2(1/4)\delta_0^2 L_k^2 \to \infty$ (`riemannHypothesis_iff_dyadic_heckeDefect_le_primePolynomial`).

## No-go closure
- **Exact killing theorem/mechanism:**
  1. `exists_unitWindow_integral_norm_primePolynomial_le` & `exists_rvm_zeroConfig_not_heckeDefect_le_spectralDeviation`: unit-window Plancherel + separated-ordinate decay forces $\int_T^{T+1} \|\Pi_{F_{c\log T}}(\gamma)\|\,d\gamma \le C_1(c) + \frac{C_2}{c\log T}\int_T^{T+1} E_\gamma(c\log T)\,d\gamma$, killing prime-polynomial absorption of unbounded $E_\gamma(c\log T)$ and falsifying the universal explicit-formula / `RiemannVonMangoldt` bound on `superpose zetaZeroConfig clusterConfig`.
  2. `exists_heckeDefect_log_le_div_pow_of_finiteOffLine` & `exists_heckeDefect_log_le_primePolynomial_any_cutoff_of_finiteOffLine`: on `FiniteOffLine ∧ ¬RiemannHypothesis`, $C_c^\infty$ Paley–Wiener rapid decay beats $T^c$ for every fixed $c > 0$, refuting the fixed-$c$ dyadic bridge `B17b`.
- **Strongest positive survivor:**
  1. `heckeDefect_log_unitWindow_tfae`, `unitWindowDepthCharge_log_iff_of_pos`, `exists_log_zeroFree_corridor_of_heckeDefect_bound`, `zerosApproachLine_and_lindelof_of_heckeDefect_log_bound`.
  2. `eventually_heckeDefect_le_pos_re_primePolynomial_iff`.
  3. `exists_poleNodal_ordinate_in_Icc`, `riemannHypothesis_iff_dyadic_heckeDefect_le_primePolynomial`, `riemannHypothesis_of_dyadic_heckeDefect_le_neg_re_primePolynomial`, `riemannHypothesis_iff_forall_scale_heckeDefect_le_primePolynomial`.
- **New insight:** At logarithmic scale $L = c\log T$, unit-window Plancherel decouples $\Pi_{F_L}$ from $E_\gamma(L)$ by $(\log T)^{-1}$, collapsing any prime-assisted bound at fixed $c > 0$ to the scale-invariant prime-free logarithmic corridor charge, whereas restoring `RH` across dyadic scales $2^k c_0\log T$ at fixed $T$ is achieved unconditionally by evaluating at zero-avoiding pole-nodal ordinates $\gamma_L \in [T, T+1)$ where $\operatorname{Re}(\operatorname{tr}(\operatorname{twist}_{\gamma_L} F_L)(1)^2) = 0$.
- **Status:** Dependency-closed on paper and unconditionally formalized in Lean 4 across the 4 modules above (`lake --old env lean` exit 0, `#print axioms` `[propext, Classical.choice, Quot.sound]`).
