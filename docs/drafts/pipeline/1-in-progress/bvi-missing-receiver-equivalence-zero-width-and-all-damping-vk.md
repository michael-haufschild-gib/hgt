# The Missing Receiver of Bézout–Valuation Incidence: Exact Equivalence, Zero-Width Admission, All-Column Chain Law, and All-Damping Vinogradov–Korobov Bounds

- **ID:** bvi-missing-receiver-equivalence-zero-width-and-all-damping-vk
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/BezoutValuationIncidence/README.md` §7.1 ("### 7.1 The receiver")
- **Statement:** For every damping $\varepsilon > 0$, the three receiver formulations of `BezoutValuationIncidence` §7.1 (bounded actual receiver energy $\sup_T E_T(\varepsilon) < \infty$, bounded pure-interior pronic energy $\sup_T E_T^{\mathrm{int}}(\varepsilon) < \infty$, and strict interior contraction of the Bézout interior martingale $M_T^{\mathrm{int}}(\varepsilon)$ against the active-deleted diagonal budget) together with boundedness of the compensated interior bracket $2 M_T^{\mathrm{int}}(\varepsilon) + 2 c^{\mathrm{int}}(\varepsilon) H_T^{\mathrm{comp}}$, $\ell^2$-membership of every column of the centred damping chain $C_\varepsilon$, and $\ell^2$-membership of $C_\varepsilon b$ for all finitely supported $b \in c_0(\mathbb{N}, \mathbb{R})$ are unconditionally equivalent, satisfy the sharp horizon-by-horizon comparison $|\sqrt{E_T^{\mathrm{int}}(\varepsilon)} - \sqrt{E_T(\varepsilon)}| \le 1/2$, hold on the exact half-line $\varepsilon > \Theta - 1/2$ with common infimum and damping rate $\Theta - 1/2$, translate zeros with multiplicity up to the boundary $\operatorname{Re} \rho \ge 1/2 + k\varepsilon$, and hold unconditionally across the entire sub-half-damping range $0 < \varepsilon \le 1/2$ on the Vinogradov–Korobov band (removing the $\varepsilon \ge 1/4$ barrier).

## Goal
Resolve §7.1 ("The receiver") in `formal/GaloisForLFunctions/BezoutValuationIncidence/README.md` completely and unconditionally, formalize every consequence and corollary of this resolution, and apply it across `BezoutValuationIncidence` and `SignedArithmeticEnergyIncidence`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean modules compiled and audited with `lake --old env lean`, `#print axioms` clean
- [ ] 3 → 4  publication-ready: standalone paper / README integration

## Approach
1. **Module 1 (`formal/GaloisForLFunctions/BezoutValuationIncidence/TheReceiverEquivalenceAndZeroWidthLaw.lean`)**:
   - **Sharp Coefficient-One Square-Root Comparison (`abs_sqrt_pmBezoutInteriorPronicEnergy_sub_sqrt_le_half`, `abs_pmBezoutInteriorPronicEnergy_sub_discreteEnergy_le`)**:
     Using the step decomposition $F_\varepsilon(n) = F_\varepsilon^{\mathrm{int}}(n) + I_\varepsilon(n)$ and Cauchy–Schwarz on the pronic inner product together with $\sum_{n=1}^T I_\varepsilon(n)^2 / (n(n+1)) \le 1/4$, prove for all $\varepsilon \ge 0$ and $T \in \mathbb{N}$:
     $$|\sqrt{E_T^{\mathrm{int}}(\varepsilon)} - \sqrt{E_T(\varepsilon)}| \le \frac{1}{2}, \qquad |E_T^{\mathrm{int}}(\varepsilon) - E_T(\varepsilon)| \le \sqrt{E_T(\varepsilon)} + \frac{1}{4}.$$
   - **Horizon-Uniform $O_\varepsilon(1)$ Conservation-Law Remainder & Interior Energy–Martingale Identity (`exists_pmBezoutInteriorPronicEnergy_sub_compensated_martingale_bound`)**:
     Combine the non-circular conservation law $\mathrm{Grad}_T(\varepsilon) + 2\,\mathrm{Local}_T(\varepsilon) = D_T^{\mathrm{act}}(\varepsilon) + 2 M_T^{\mathrm{pred}}(\varepsilon) - E_T^{\mathrm{pair}}(\varepsilon) - \Phi_1^{\mathrm{int}}(\varepsilon)(1 - 1/(T+1))$ with the $O_\varepsilon(1)$ Euler–Maclaurin remainder bounds for $D_T^{\mathrm{act}}(\varepsilon)$ and $M_T^{\mathrm{pred}}(\varepsilon)$ to prove that $(E_T^{\mathrm{int}}(\varepsilon) + B_T^{\mathrm{int}}(\varepsilon)) - (2 M_T^{\mathrm{int}}(\varepsilon) + 2 c^{\mathrm{int}}(\varepsilon) H_T^{\mathrm{comp}}) = O_\varepsilon(1)$ uniformly in $T \ge 1$.
   - **Pointwise Equivalence of All Receiver Formulations (`mem_receiverDampings_iff_interior_and_contraction`)**:
     Prove that for every $\varepsilon > 0$, $\varepsilon \in \text{receiverDampings}$, $\varepsilon \in \text{interiorReceiverDampings}$, $\varepsilon \in \text{strictContractionDampings}$, strict contraction against $E_T^{\mathrm{int}}(\varepsilon)$, and uniform boundedness of $2 M_T^{\mathrm{int}}(\varepsilon) + 2 c^{\mathrm{int}}(\varepsilon) H_T^{\mathrm{comp}}$ are all equivalent.
   - **Exact Zero-Width Admission $(\Theta - 1/2, \infty)$, Damping Rate $\Theta - 1/2$, Zero Translation with Multiplicity, and Full Equivalences with `RiemannHypothesis`**:
     Upgrade `LittlewoodAdmitsTheReceiverAboveHalfTheZeroAbscissa` ($\varepsilon > \Theta/2$) and `exists_pmBezoutInteriorPronicEnergy_budget_of_half_le` ($\varepsilon \ge 1/2$) to all $\varepsilon > \Theta - 1/2$; prove `sInf interiorReceiverDampings = sInf strictContractionDampings = receiverDampingRate = zetaZeroAbscissa - 1 / 2`; prove iterated zero translation $\operatorname{ord}_\rho(\zeta) \le \operatorname{ord}_{\rho - k\varepsilon}(\zeta)$ up to the boundary $\operatorname{Re} \rho \ge 1/2 + k\varepsilon$ under bounded interior pronic energy or strict interior contraction; and establish full `↔` equivalences with `RiemannHypothesis`.

2. **Module 2 (`formal/GaloisForLFunctions/BezoutValuationIncidence/AllDampingVinogradovKorobovBandAndInteriorGrowth.lean`)**:
   - Eliminate the $\varepsilon \ge 1/4$ barrier across all unconditional sub-half-damping theorems in `BezoutValuationIncidence` by combining `abs_weightCenteredPrefix_dampedSign_le_of_linear_pos` ($0 < \varepsilon \le 1/2$) with `exists_abs_sum_moebiusReal_le_vk`:
     - All-damping VK prefix bound for both $F_\varepsilon(n)$ and $F_\varepsilon^{\mathrm{int}}(n)$ on $0 < \varepsilon \le 1/2$;
     - All-damping VK band boundedness for $E_T(\varepsilon)$, $E_T^{\mathrm{int}}(\varepsilon)$, and $2 M_T^{\mathrm{int}}(\varepsilon) + 2 c^{\mathrm{int}}(\varepsilon) H_T^{\mathrm{comp}}$ on $\varepsilon_0 \le \varepsilon \le 1/2$ with $\varepsilon \ge 1/2 - \kappa \sigma(T)/(480 \log T)$ for every $\varepsilon_0 \in (0, 1/2]$;
     - All-damping parity-pair separation on the VK band for every $\varepsilon_0 \in (0, 1/2]$;
     - All-damping VK growth bound $E_T(\varepsilon), E_T^{\mathrm{int}}(\varepsilon) \le C_\varepsilon T^{1-2\varepsilon} \exp(-\kappa \sigma(T)/270)$ and period-energy ratio decay $E_N^{\mathrm{int}}(\varepsilon) / \mathcal{E}_{\mathrm{prim}}(N) \le C'_\varepsilon \exp(-\kappa \sigma(N)/270) \to 0$ for every $0 < \varepsilon < 1/2$.

3. **Module 3 (`formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/AllColumnsOfTheChainAreTheReceiver.lean`)**:
   - Prove the universal horizon-uniform column energy bound for the centred damping chain $C_\eta$ at **every** damping $\eta > 0$, column $k \in \mathbb{N}$ ($K = k+1$), and horizon $T \in \mathbb{N}$:
     $$\sum_{n=0}^{T-1} C_\eta(n, k)^2 \le 12 (k+1)^{1 - 2\eta} E_T(\eta) + 24 (k+1)^{1 - 2\eta}.$$
   - Deduce that for every $\eta > 0$, the following are equivalent:
     1. $\eta$ is admitted ($\sup_T E_T(\eta) < \infty$, or $\sup_T E_T^{\mathrm{int}}(\eta) < \infty$, or strict interior contraction of $M_T^{\mathrm{int}}(\eta)$),
     2. The reciprocal orbit $C_\eta r$ lies in $\ell^2$,
     3. The first column $C_\eta e_0$ lies in $\ell^2$,
     4. Every column $C_\eta e_k$ ($k \in \mathbb{N}$) lies in $\ell^2$,
     5. $C_\eta b \in \ell^2$ for every finitely supported sequence $b \in c_0(\mathbb{N}, \mathbb{R})$;
   - Prove that all five hold unconditionally for every $\eta > \Theta - 1/2$, with uniform column norm bound $\sum_{n=0}^\infty C_{1/2}(n, k)^2 \le 12 B_{1/2} + 24$ at $\eta = 1/2$.

## Log
- 2026-10-24 — created in 1-in-progress
