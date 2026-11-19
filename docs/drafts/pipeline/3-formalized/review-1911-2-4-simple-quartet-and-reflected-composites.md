# Complete Resolution of the Simple Off-Line Quartet and Reflected-Composite Factorization Question (§2.4)

- **ID:** review-1911-2-4-simple-quartet-and-reflected-composites
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/review-1911/obstacles-summary.md` §2.4
- **Lean Modules:**
  - `formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ReflectedCompositeWaveTransmission.lean`
  - `formal/GaloisForLFunctions/ExceptionalLayerTheory/SimpleOffLineQuartetAndReflectedComposites.lean`
- **Key Lean Declarations:**
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.midpointMultiplier_ne_zero`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.exists_prime_power_re_lower_bound`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.largePrimeCofactorPrice_eq_clippedCofactorOp`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.clippedCofactorSliceOp_linear`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.clippedCofactorSliceOp_wave`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.clippedCofactorOp_linear_add_wave_defect`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.reflectedComposite_wave_compatible_iff_zeta_zero`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.clippedCofactorSliceOp_theta_of_two_le`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.singleQuartet_reflectedComposite_remainder_cancellation`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.singleQuartet_individual_cofactor_cell`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.clippedCofactorOp_logTwistedWave_at_zero`
  - `GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.logTwisted_wave_compatible_iff_deriv_zero`
  - `GaloisForLFunctions.ExceptionalLayerTheory.HasSimpleSingleOffLineQuartet`
  - `GaloisForLFunctions.ExceptionalLayerTheory.NoSimpleSingleOffLineQuartet`
  - `GaloisForLFunctions.ExceptionalLayerTheory.quartetCopyMult_eq_analyticOrderNatAt`
  - `GaloisForLFunctions.ExceptionalLayerTheory.quartetCopyMult_eq_one_iff_deriv_ne_zero`
  - `GaloisForLFunctions.ExceptionalLayerTheory.two_le_quartetCopyMult_iff_deriv_eq_zero`
  - `GaloisForLFunctions.ExceptionalLayerTheory.rightXiZeroCopy_encard_of_singleQuartet`
  - `GaloisForLFunctions.ExceptionalLayerTheory.offLineXiZeroCopy_encard_of_singleQuartet`
  - `GaloisForLFunctions.ExceptionalLayerTheory.hasSimpleSingleOffLineQuartet_tfae`
  - `GaloisForLFunctions.ExceptionalLayerTheory.unit_multiplicity_no_odd_harmonic_alias`
  - `GaloisForLFunctions.ExceptionalLayerTheory.unit_trial_under_noSimple_forces_ramified_quartet`
  - `GaloisForLFunctions.ExceptionalLayerTheory.coprimeZeroOneSet_imitator_rejected_by_reflectedComposites`
  - `GaloisForLFunctions.ExceptionalLayerTheory.unconditional_sEdit_rejected_above_max_two_thirds_zetaZeroAbscissa`
  - `GaloisForLFunctions.ExceptionalLayerTheory.unconditional_sEdit_rejected_on_zeroFreeStrip`
  - `GaloisForLFunctions.ExceptionalLayerTheory.rh_sEdit_imitates_radius_but_violates_reflectedComposites`
  - `GaloisForLFunctions.ExceptionalLayerTheory.singleQuartet_simple_iff_logTwisted_unbounded`
  - `GaloisForLFunctions.ExceptionalLayerTheory.noSimpleSingleOffLineQuartet_tfae`
  - `GaloisForLFunctions.ExceptionalLayerTheory.corollaries_of_noSimpleSingleOffLineQuartet`
  - `GaloisForLFunctions.ExceptionalLayerTheory.abscissa_unconstrained_under_no_simple_single_layer`
- **Statement:** Complete unconditional resolution of the §2.4 lone *simple* off-line quartet and reflected-composite factorization question: (1) negative answer for first-order reflected-composite transmission and joint prime/cofactor divisibility slicing — inserting $x - 2m\operatorname{Re}(x^z/z)$ into the large-factor cells $p > P \ge \lfloor 2\sqrt{n}\rfloor$, $\gcd(n, v) = 1$ transmits $\operatorname{reflectedDensity}\cdot\varphi(n) - 2m\operatorname{Re}\!\left(\frac{M(z)}{z}(1 - \zeta(z)E_n(z))n^z\right) + O_{z,m}\!\bigl((P^\beta + n P^{\beta-2})\operatorname{squarefreeDivisorMass}(n)\bigr)$ ($M(z) = 2\cdot 3^z - 2^z - 4^z \ne 0$, $E_n(z) = \sum_{d\mid n}\mu(d)d^{-z}$), matching `primeMidpointPrice n` and every $q$-divisible ($q \ge 2$) cofactor slice at $\zeta(\rho_0) = 0$ with signed remainder cancelling to $O_{\rho_0}\!\bigl(\sqrt{n}(\log^2 n + \operatorname{squarefreeDivisorMass}(n))\bigr)$, while intrinsic Beurling edits ($\beta \in (1/2, 2/3)$) and positive Euler twins realize simple off-line pairs/quartets; (2) positive unconditional selectivity, radius-imitator rejection, second-order multiplicity separation, and stratum corollaries — reflected composites reject every non-$\zeta$-zero wave ($\zeta(z) \ne 0$), every $\{0,1\}$-coprime radius imitator on $(1/2, 1)$, and every $\{0,1,2\}$-prime `sEdit` on $\max(2/3, \Theta) < \beta < 1$ unconditionally (including $20999/24000 < \beta < 1$, and all $2/3 < \beta < 1$ under `RH`); the log-twisted ($\partial_z$) reflected-composite defect at $\zeta(\rho_0) = 0$ equals $+2\operatorname{Re}\!\left(\frac{M(\rho_0)}{\rho_0}\zeta'(\rho_0)E_n(\rho_0)n^{\rho_0}\right) + O_{\rho_0}\!\bigl(n^{(1+\beta_0)/4}\operatorname{squarefreeDivisorMass}(n)\bigr)$, separating simple ($m=1$, $\zeta'(\rho_0) \ne 0$, $\Omega(n^{\beta_0})$) from ramified ($m \ge 2$, $\zeta'(\rho_0) = 0$) quartets; and `HasSimpleSingleOffLineQuartet` / `NoSimpleSingleOffLineQuartet` satisfy exact unit-wave, non-aliasing, divisor-copy, log-twisted receiver, and $\Theta$-non-advancement laws.

## Goal
Resolve completely whether ordinary integer arithmetic via the reflected composite factorization and joint prime/cofactor divisibility can exclude a lone *simple* off-line quartet while permitting multi-quartet configurations, infinite off-line divisors, and a higher-multiplicity quartet, and unconditionally formalize the transmitted coefficients, radius-imitator obstructions, second-order multiplicity separation, and global zero-configuration corollaries on $\zeta(s)$.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (`[PROVED HERE]`, complete dependency-closed paper proofs)
- [x] 2 → 3  formalized and audited via `lake --old env lean` (`[propext, Classical.choice, Quot.sound]`)

## Mathematical Proof

1. **Exact clipped-cofactor operator and forbidden-prime cancellation (`largePrimeCofactorPrice_eq_clippedCofactorOp`, `midpointMultiplier_ne_zero`).**
   For $n \ge 1$ and $\lfloor 2\sqrt{n}\rfloor \le P \le 2n$, every prime $p > P$ dividing $n$ satisfies $p^2 > 4n$, so $4(n/p) < p$ and `forbidden_prime_at_square_root_cut` gives `coprimeMidpointMultipleCount n p = 0`. Dropping $p \nmid n$ and using $M / p < v \le N / p \iff M / v < p \le N / v$ ($p, v \ge 1$) together with $4n / v \le 2n$ for $v \ge 2$ swaps primes and cofactors without rounding error:
   $$\operatorname{largePrimeCofactorPrice}(n, P) = \mathcal{T}_{n, P}(\theta), \qquad \mathcal{T}_{n, P}^{(q)}(F) := \sum_{\substack{2 \le v \le 4n \\ \gcd(n, v) = 1,\, q \mid v}} \Bigl(F(\max(P, 4n/v)) - 2F(\max(P, 3n/v)) + F(\max(P, 2n/v))\Bigr).$$
   By strict concavity of $u \mapsto u^\sigma$ on $(0, \infty)$ for $0 < \sigma < 1$, $\|M(z)\| \ge -\operatorname{Re} M(\operatorname{Re} z) = 2\cdot 3^{\operatorname{Re} z} - 2^{\operatorname{Re} z} - 4^{\operatorname{Re} z} > 0$, so $M(z) \ne 0$ throughout $\{0 < \operatorname{Re} z < 1\}$.

2. **Universal linear and oscillatory wave transmission and cofactor-divisibility slicing (`clippedCofactorSliceOp_linear`, `clippedCofactorSliceOp_wave`, `clippedCofactorSliceOp_theta_of_two_le`, `singleQuartet_reflectedComposite_remainder_cancellation`, `singleQuartet_individual_cofactor_cell`).**
   - *Linear baseline:* Replacing $\max(P, kn/(qu)) - P$ by $\bigl(\frac{kn}{qu} - (P + 1)\bigr)_+$ costs $\le \frac{12 n}{q(P + 1)}$, and Möbius-harmonic inversion cancels $\log\bigl(\frac{n}{(P+1)qd}\bigr) + \gamma_E - 1$ via $4 - 6 + 2 = 0$, leaving $\frac{1}{q}\operatorname{reflectedDensity}\cdot\varphi(n) + O\!\bigl((P + 1 + \frac{n}{q(P+1)})\operatorname{squarefreeDivisorMass}(n)\bigr)$.
   - *Oscillatory wave:* For $g_z(x) = x^z / z$ ($0 < \beta = \operatorname{Re} z < 1$), clamping to $kn/v$ costs $\le \frac{12}{q} n P^{\beta - 2}$, and Euler–Maclaurin truncation $\sum_{1 \le j \le \lfloor t\rfloor_+} j^{-z} = \zeta(z) + \frac{t^{1-z}}{1-z} + O_z(t^{-\beta})$ at $t_k = \frac{kn}{Pqd}$ cancels $d^{-\beta} t_k^{-\beta} = (kn)^{-\beta}(Pq)^\beta$ identically while $4 - 6 + 2 = 0$ kills both $P^{z-1}$ main terms, yielding $+\frac{M(z)}{z}(\mathbf{1}_{q=1} - q^{-z}\zeta(z)E_n(z))n^z$.
   - *Compatibility at $\zeta(\rho_0) = 0$:* Every $q \ge 2$ slice transmits $O_{\rho_0, m, q}(n^{\beta_0/2}\operatorname{squarefreeDivisorMass}(n))$ with zero $n^{\rho_0}$ wave, matching actual primes $\theta$ (`clippedCofactorSliceOp_theta_of_two_le`, proved unconditionally via Möbius-Stirling inversion on $a = qb \in (2n, 4n]$ because $q\mathbb{Z} \cap (2n, 4n]$ contains no primes). Under `HasSingleOffLineQuartet ρ₀`, individual cells transmit $+2m\operatorname{Re}\!\bigl(\frac{M(\rho_0)}{\rho_0}v_0^{-\rho_0}n^{\rho_0}\bigr)$ and the signed cofactor remainder cancels to $O_{\rho_0}\!\bigl(\sqrt{n}(\log^2 n + \operatorname{squarefreeDivisorMass}(n))\bigr)$.

3. **Exact $\zeta(z) = 0$ selectivity and rejection of radius imitators (`reflectedComposite_wave_compatible_iff_zeta_zero`, `coprimeZeroOneSet_imitator_rejected_by_reflectedComposites`, `unconditional_sEdit_rejected_above_max_two_thirds_zetaZeroAbscissa`, `unconditional_sEdit_rejected_on_zeroFreeStrip`, `rh_sEdit_imitates_radius_but_violates_reflectedComposites`).**
   - By $\mathbb{Q}$-linear independence of $\log p_1, \log p_2$ (`primeLogPhaseClockPair_injective`), for any $Q \ge 1$ and $A \ne 0$ there exists a prime $p > Q$ and $c > 0$ such that for every $k \ge 1$, at least one $n \in \{p^k, p^{k+1}\}$ has $\operatorname{squarefreeDivisorMass}(n) = 2$ and $|\operatorname{Re}(A E_n(z) n^z)| \ge c n^{\operatorname{Re} z}$ (`exists_prime_power_re_lower_bound`). Thus $x + W_{z, m}(x)$ satisfies reflected-composite balance within $O(\sqrt{n}\operatorname{squarefreeDivisorMass}(n))$ iff $\zeta(z) = 0$.
   - Every $\{0, 1\}$-coprime radius imitator $\theta_w$ ($1/2 < \beta < 1$, $\zeta(\beta + i\gamma) \ne 0$) violates reflected-composite balance at scale $\Omega(n^\beta)$.
   - Writing $\theta_e = \theta + \Delta_e$ around `large_prime_cofactor_centering` avoids paying the $\theta(x) - x$ exponent directly, while partial summation against $|\theta(n) - n| \le K_\theta n^{\theta_0}$ damps the error by $n^{\beta - 1}$ to $O(x^{\max(1/4, \theta_0 + \beta - 1)})$. Consequently `sEdit α β γ k₀` ($\alpha \in (\beta, \min(1, 4\beta - 2))$) violates ordinary-integer reflected-composite balance at scale $\Omega(n^\beta)$ across all $\max(2/3, \Theta) < \beta < 1$ unconditionally (in particular across $20999/24000 < \beta < 1$), and simultaneously imitates the two-interval radius while violating reflected composites across all $2/3 < \beta < 1$ under `RiemannHypothesis` — complementing the sub-square-root $(1/2, 2/3)$ intrinsic Beurling realization regime.

4. **Second-order (log-twisted) reflected-composite separation of simple vs. multiple quartets (`clippedCofactorOp_logTwistedWave_at_zero`, `logTwisted_wave_compatible_iff_deriv_zero`, `singleQuartet_simple_iff_logTwisted_unbounded`).**
   Applying Cauchy's derivative estimate on $\overline{B}(\rho_0, \frac{1 - \beta_0}{2})$ to the holomorphic remainder $R_{n, \lfloor 2\sqrt{n}\rfloor}(z)$ differentiates the wave identity to $\widetilde{W}_{\rho_0}(x) = -2\operatorname{Re}\!\bigl(\frac{x^{\rho_0}\log x}{\rho_0} - \frac{x^{\rho_0}}{\rho_0^2}\bigr)$ with sub-square-root error $O_{\rho_0}\!\bigl(n^{(1+\beta_0)/4}\operatorname{squarefreeDivisorMass}(n)\bigr)$, giving defect $+2\operatorname{Re}\!\bigl(\frac{M(\rho_0)}{\rho_0}\zeta'(\rho_0)E_n(\rho_0)n^{\rho_0}\bigr)$, which is $O(\sqrt{n}\operatorname{squarefreeDivisorMass}(n))$ iff $\zeta'(\rho_0) = 0$ (`2 ≤ quartetCopyMult ρ₀`).

5. **Exact characterizations, non-aliasing, corollaries, and $\Theta$-non-advancement of `HasSimpleSingleOffLineQuartet` and `NoSimpleSingleOffLineQuartet` (`hasSimpleSingleOffLineQuartet_tfae`, `unit_multiplicity_no_odd_harmonic_alias`, `unit_trial_under_noSimple_forces_ramified_quartet`, `noSimpleSingleOffLineQuartet_tfae`, `corollaries_of_noSimpleSingleOffLineQuartet`, `abscissa_unconstrained_under_no_simple_single_layer`).**
   `HasSimpleSingleOffLineQuartet ρ₀` satisfies an 8-way unconditional equivalence across `ζ'(ρ₀) ≠ 0`, `XiZeroCopy` cardinalities $2$ and $4$, unit-amplitude $\psi - \mathrm{id}$, $\theta - \mathrm{id}$, and odd-composite waves, and bounded unit-multiplicity two-interval radius + $(2, 3, 6)$ prime dilations; admits zero non-trivial odd-harmonic aliases (`k = 0, m = 1, ω = |γ|`); and its negation `NoSimpleSingleOffLineQuartet` satisfies a 6-way global equivalence forcing `8 ≤ #{q : XiZeroCopy | Re q ≠ 1/2}` under `¬ RH` while leaving the supremum abscissa $b \in (1/2, 14/15)$ unconstrained in $\{0, 1, 2\}$-prime Beurling systems.

## Log
- 2026-11-19 — created, proved on paper, formalized unconditionally in Lean 4 across `ReflectedCompositeWaveTransmission.lean` and `SimpleOffLineQuartetAndReflectedComposites.lean`, wired into `ExceptionalLayerTheory.lean`, and audited via `lake --old env lean`.
