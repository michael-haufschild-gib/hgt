# Bézout–Valuation Incidence (`GaloisForLFunctions.BezoutValuationIncidence`)

## 1. Why This Library Exists (Motivation & Problem Space)

Classical Ramanujan–Fourier and Selberg sieve methods analyze a truncated divisor sum
$$s_{N,c}(n) = \sum_{\substack{d \mid n \\ d \le N}} c(d) = \sum_{q=1}^N Y_{N,c}(q)\,c_q(n), \qquad Y_{N,c}(q) = \sum_{\substack{d \le N \\ q \mid d}} \frac{c(d)}{d}$$
by averaging over a full period $L_N = \operatorname{lcm}(1, \dots, N) = e^{N(1+o(1))}$, where distinct Ramanujan modes $c_q(n)$ are orthogonal.

In finite-horizon problems—where the observation window $M$ is polynomial in $N$ ($M \sim N$, $M \le 4N$, or a short shifted interval $[M_0+1, M_0+M]$ with $M \ll L_N$)—full-period orthogonality is unavailable:
1. **Drift vs. Incidence Mixing:** In the prefix sawtooth discrepancy
   $$L_N(M, c) = \sum_{n=1}^M s_{N,c}(n) - M \sum_{d=1}^N \frac{c(d)}{d} = \sum_{d=2}^N c(d)\left(\left\lfloor \frac{M}{d} \right\rfloor - \frac{M}{d}\right),$$
   every divisor $d > M$ contributes a non-zero linear drift $-M c(d)/d$ even before its first divisibility jump $\lfloor M/d \rfloor$ switches on.
2. **Non-Commutativity of Shift and Cutoff:** Additive translations $n \mapsto n + h$ do not preserve the finite divisor space $\operatorname{span}\{\mathbf{1}_{d \mid n} : d \le N\}$, and boundary terms at window endpoints dominate naive remainder expansions whenever $M \ll N^2$.
3. **Multi-Lag & Multi-Depth Coupling:** Evaluating correlations across $k$-tuples $(n+h_1, \dots, n+h_k)$ or across multiplicative depths $\omega(q) = k$ requires exact finite-horizon operator factorizations rather than asymptotic mode-by-mode limits.

**Bézout–Valuation Incidence (BVI)** provides the unconditional, finite-horizon algebraic and spectral toolkit for these regimes.

---

### Current closing target and known endpoint (19 October 2026)

The pure-interior receiver in
[`PronicPotentialSelfCancellationAndInteriorGradientConservation.lean`](PronicPotentialSelfCancellationAndInteriorGradientConservation.lean)
requires
$$\forall\delta>0\;\exists\varepsilon\in(0,\delta)\;\exists B_\varepsilon<\infty\;\forall T\ge1:
\quad\sum_{n=1}^{T}\frac{I_\varepsilon(n)^2}{n(n+1)}\le B_\varepsilon.$$
Here $I_\varepsilon$ is `pmBezoutInteriorPrefix`. The constant may depend on damping.

The actual PM source and its discrete energy are already controlled for every
$\varepsilon\ge1/2$, including the endpoint:
[`PMPowerDampedMobiusEndpoint.lean`](../RHTower/PMPowerDampedMobiusEndpoint.lean),
[`PMPowerDampedMobiusDiscreteEnergy.lean`](../RHTower/PMPowerDampedMobiusDiscreteEnergy.lean).
`exists_pmBezoutInteriorPronicEnergy_budget_of_half_le` transports that result to
the interior energy. The unresolved range is $0<\varepsilon<1/2$, ultimately at
arbitrarily small damping. A bound at a fixed damping below $1/2$ would already
have a nontrivial zero-free-half-plane consequence; it is not routine bookkeeping.

Uniform control in the natural Ramanujan cutoff $Q$ is a sufficient route to
source admission. Source admission alone does not establish uniform control of
that approximation sequence. Do not identify this stronger variance premise with
the already proved source-energy endpoint.

## 2. Core Objects & Lean Vocabulary

When searching (`scripts/formal_tools.py research`) or writing Lean proofs in BVI, use these canonical definitions rather than re-defining them:

| Mathematical Object | Formula / Meaning | Canonical Lean Identifier |
| :--- | :--- | :--- |
| Pointwise truncated divisor sum | $s_{N,c}(k) = \sum_{d \le N,\, d \mid k} c(d)$ | `sieveSeq N c k` |
| Finite harmonic mean | $\mathcal{H}_N(c) = \sum_{d=1}^N \frac{c(d)}{d} = Y_{N,c}(1)$ | `finiteHarmonicSum N c` |
| Selberg multiples coordinate | $Y_{N,c}(q) = \sum_{q \mid d \le N} \frac{c(d)}{d}$ | `selbergMultiplesCoord N c q` |
| Finite Ramanujan inverse weight | Weight $c$ realizing prescribed $Y_{N,c}(q)$ on $[1, N]$ | `pmRamanujanResidueCoeff Y N` |
| Centered period variance (lag 0) | $\operatorname{Var}(N, c) = \sum_{q=2}^N \varphi(q) Y_{N,c}(q)^2$ | `sieveVariance N c` / `periodCovariance N c 0` |
| Centered lag-$h$ period covariance | $\operatorname{Cov}_h(N, c)$ over $1 \dots N!$ | `periodCovariance N c h` |
| Centered lag-1 covariance | $\operatorname{Cov}_1(N, c) = \sum_{q=2}^N \mu(q) Y_{N,c}(q)^2$ | `sieveSuccessorCovariance N c` |
| Discrete primitive ($H^{-1}$) energy | $\mathcal{E}_{\mathrm{prim}}(N, c) = \frac{1}{12}\sum_{q=2}^N J_2(q) Y_{N,c}(q)^2$ | `sievePrimitiveEnergy N c` |
| Normalized lag-$h$ eigenvalue | $\lambda_q(h) = \frac{c_q(h)}{\varphi(q)} = \frac{\mu(q/\gcd(q,h))}{\varphi(q/\gcd(q,h))}$ | `sieveLagMultiplier q h` |
| Valuation visibility clock | $\tau_{\mathrm{vis}}(q) = q / \operatorname{rad}(q)$ (minimal lag with $\lambda_q(h) \ne 0$) | `lagVisibilityClock q` |
| Prefix sawtooth discrepancy | $L_N(M, c) = \sum_{d=2}^N c(d)(\lfloor M/d \rfloor - M/d)$ | `sievePrefixDiscrepancy N M c` |
| Active centered sawtooth sum | $\sum_{d \le N,\, d \mid k} c(d)\,\widetilde{\psi}(m/d)$ | `activeCenteredSawtoothSum N c m k` |
| Bézout interior sawtooth | Sawtooth sum over $d \le N$ with $d \nmid n$ and $d \nmid (n+1)$ | `bezoutInteriorSawtoothSum N c n` |
| Prefix $L^2$ energy | $\mathcal{E}_N(M; c) = \sum_{k=1}^M s_{N,c}(k)^2$ | `sieveL2PrefixEnergy N M c` |
| Renormalized prefix correlation defect | $\widetilde{\mathcal{D}}_N(M; c) = \sum_{k=1}^M s_{N,c}(k)(s_{N,c}(k+1) - s_{N,c}(k))$ | `sieveRenormalizedPrefixDefect N M c` |
| Short-window correlation defect | $\widetilde{\mathcal{D}}_N(M_0+M; c) - \widetilde{\mathcal{D}}_N(M_0; c)$ on $[M_0+1, M_0+M]$ | `shortWindowRenormalizedDefect N M₀ M c` |
| Multiplicative / radical state | $\sigma_N(k) = \operatorname{lcm}\{d \le N : d \mid k\}$, $\operatorname{rad}_N(k) = \gcd(k, N\#)$ | `horizonObservationState N k` / `horizonRadicalState N k` |
| Non-periodic pronic Gram matrix | $\mathcal{G}(e_1, e_2) = \sum_{M=1}^\infty \frac{\mathbf{1}_{e_1 \mid M+1}\mathbf{1}_{e_2 \mid M+1}}{M(M+1)}$ | `pronicGramMatrix e₁ e₂` |
| Energy-centered pronic Gram matrix | $\mathcal{G}^{\mathrm{ec}}(e_1, e_2) = \langle f_{e_1}^{\mathrm{ec}}, f_{e_2}^{\mathrm{ec}} \rangle_{\ell^2(\mu_{\mathrm{pr}})}$ | `pmRamanujanEnergyCenteredGram e₁ e₂` |
| Natural-cutoff cofactor weight | $c_{\varepsilon,Q}(d)$ producing $Y_{Q+1,c}(q)=\operatorname{Re}\sum_{m\ge1}\mu(qm)(qm)^{-1-\varepsilon}$ for $1\le q\le Q+1$, and zero outside that range; it is not the coefficient $\mu(q)q^{-\varepsilon}$ | `pmCofactorDivisorWeight ε Q` / `selbergMultiplesCoord_pmCofactorDivisorWeight` |
| `ker P` endpoint projection | $c - c(1)\mathbf{1}_{d=1} + \bigl(c(1) - \mathcal{H}_N(c)\bigr)\mathbf{1}_{d=1}$ annihilating $\mathcal{H}_N$ | `kerPEndpointWeight N c` |
| Barban–Vehov mollifier weight | $\Lambda_X(d) = \mu(d)\log(X/d)\mathbf{1}_{1 \le d \le X}$ (and normalized $/ \log X$) | `barbanVehovWeight X` / `normalizedBarbanVehovWeight X` |
| Deletion-averaged divisor source | $\frac{\Lambda(k) - b_X(k)}{\log M - \log X}$ annihilating $2 \le k \le X$ | `DeletionAveragedDivisor.divisorSource X M` |
| Pronic log-convolution deficit | $\log N \cdot \mathcal{E}_\varepsilon(N) - (\operatorname{Cov}_{\mathrm{dil}} + \operatorname{Cov}_{\mathrm{pref}} + \operatorname{Cov}_{\mathrm{forc}}) \ge 0$ | `pmPronicLogDeficit ε N` |
| Least Bézout successor seed | Least positive $(a, b)$ with $p a = q b + 1$ ($1 \le a \le q$) | `leastSuccessorSeed p q` / `successorLeastSeedResonance r p q` |
| $k$-tuple prime structure factor | $S_p(H) = p\sum_{r=0}^{p-1} \nu_H(p, r)^2 - k^2$ | `tuplePrimeStructureFactor H p` |

---

## 3. Core Mechanisms (How to Solve Problems in BVI)

### Mechanism 1: Second-Difference + Möbius Lift for Finite-Prefix Inversion
* **Problem:** Recover divisor weights $c(2), \dots, c(N)$ from prefix discrepancies $L_N(M, c)$ on a short prefix $M \in [1, N-1]$ without knowing the linear drift $-M\,\mathcal{H}_N(c)$.
* **How it works:**
  1. Take discrete second differences $\Delta^2 L_N(M, c)$ to annihilate the linear drift $-M\,\mathcal{H}_N(c)$, leaving pure divisibility indicators $\mathbf{1}_{d \mid M}$.
  2. Apply Möbius inversion (`sievePrefixMobiusLift`). For $2 \le d \le N - 1$, this isolates $c(d)$ up to a single rank-1 coupling to the top column $c(N)$.
  3. Over $\mathbb{Z}$, clearing denominators in $A_n(M, d) = d\lfloor M/d \rfloor - M$ ($N = n+1$) produces an exact unimodular factorization $U_n A_n V_n = \operatorname{diag}(1, 2, \dots, n)$ (`integerPrefixMatrix_unimodular_diag`), proving $\det(P_n) = (-1)^n / (n+1)$ and lattice index $n!$.
  4. **Local Conditioning:** Because column $d \le N - 1$ is reconstructed from $M \in [1, d]$ before the top column $N$ enters, interior coefficients obey the cutoff-independent stability bound $|c(d) - b(d)| \le 2\tau(d)\varepsilon$ (`abs_coeff_sub_le_two_mul_card_divisors_of_prefix_close`). For squarefree weights sampled via active sawtooth sums at arbitrary powers $j^m$, the exact attained constant is $\frac{2d}{d-1}(\tau(d) - 1)$ (`bvi_active_power_sampling_sharp_conditioning`).

### Mechanism 2: Finite-Ray Spectral Polytopes in Selberg Coordinates
* **Problem:** Prove sharp universal inequalities between quadratic functionals ($\operatorname{Var}$, $\operatorname{Cov}_1$, $\operatorname{Cov}_2$, $\mathcal{E}_{\mathrm{prim}}$, $k$-tuple variances) valid for all cutoffs $N$ and all weights $c$.
* **How it works:**
  1. Diagonalize each functional in Selberg coordinates $Y_{N,c}(q)^2$ ($q \in [2, N]$), where the mode-$q$ weights are $(\varphi(q), \mu(q), \lambda_2(q), J_2(q)/12)$.
  2. Use arithmetic bounds on $(\varphi(q), \mu(q), \lambda_2(q), J_2(q))$ (such as $\varphi(q) \ge 8$ for odd $q \ge 2$ with $\mu(q) = 1$, and $J_2(q) \ge q\,\varphi(q)$) to show that every mode $q \ge 2$ lies inside a polyhedral cone generated by a small, fixed set of extreme modes:
     * **Lag-1 + Primitive Energy (`SharpPrimitiveEnergySuccessorFrontier`):** Extreme modes $\{2, 3, 4, 6\}$ (`primitiveFrontierWeight`).
     * **Lag-1 + Lag-2 + 3-Tuple $H_3 = (0, 1, 2)$ + Primitive Energy (`TwoLagFiveModePolytopeAndHigherMomentPhaseRecoveryBridge`):** Extreme modes $\{2, 3, 4, 6, 12\}$ (`fiveModeWeight`), giving $0 \le \mathcal{V}_{H_3}(N, c) \le 4\,\operatorname{Var}(N, c)$.
  3. Any linear inequality holds for all $(N, c)$ **if and only if** it holds on those 4 or 5 extreme modes, and `pmRamanujanResidueCoeff` constructs explicit finite weights attaining every point of the cone.

### Mechanism 3: Valuation-Clock Wavelets & Higher-Moment Phase Recovery
* **Problem:** Separate prime-power shells $q = p^a$ from squarefree modes and recover the **signs** of $Y_{N,c}(q)$.
* **How it works:**
  1. **Visibility Clocks:** By Hölder's formula, $\lambda_q(h) \ne 0 \iff \tau_{\mathrm{vis}}(q) = q/\operatorname{rad}(q) \mid h$. On a prime chain $p^b$, the clock difference $\lambda_{p^b}(p^a) - \lambda_{p^b}(p^{a-1})$ (`clockWaveletMultiplier p a`) is non-zero **only** on the two adjacent shells $b \in \{a, a+1\}$ with opposite signs.
  2. **Composite Tensor Splitting (`bvi_composite_clock_wavelet_tensor_and_shell_recovery`):** For coprime moduli and cross-coprime lags, $\lambda_{q_1 q_2}(h_1 h_2) = \lambda_{q_1}(h_1)\lambda_{q_2}(h_2)$. Sampling at the transverse visibility clock $L = \tau_{\mathrm{vis}}(\operatorname{ordCompl}_p(q))$ isolates $v_p(q) \in \{a, a+1\}$ inside any composite modulus $q$.
  3. **Signed Coordinate Readout (`bvi_tripleMoment_recovers_signed_odd_modes`, `bvi_evenPair_sixth_moment_sign_hierarchy`):** Two-point correlations only see $Y_{N,c}(q)^2$. To recover signs, use 3-point translated moments (`tripleMoment`), whose double DFT at $(N!/q, N!/q)$ reads out $Y_{N,c}(q)^3$ for every odd $q \le N$. For even modes $q \in \{6, 10\}$, odd moments vanish and moments of degree $\le 5$ are invariant under $(a, b) \mapsto (a, -b)$, while the zero-lag 6th moment exposes the cubic cross term $960 a^3 b^3$.

### Mechanism 4: Pointwise Bézout Splitting, Short-Window Polarization, and Pronic Duality
* **Problem:** Control shifted correlations and sawtooth sums without averaging over $L_N$.
* **How it works:**
  1. **Pointwise Bézout Disjointness (`UniversalSawtoothInteriorMartingaleAndPostStepCalculus`):** Since $\gcd(n, n+1) = 1$, no divisor $d \ge 2$ divides both $n$ and $n+1$. Splitting $d \le N$ into active at $n+1$, active at $n$, and interior $d \nmid n(n+1)$ cancels the diagonal drift $(s_{N,c}(n+1) - \mathcal{H}_N(c))^2 - s_{N,c}(n)^2$ pointwise in $n$.
  2. **Short-Window Endpoint State Reduction (`bvi_short_window_defect_iso_state_classification`):** On $[M_0+1, M_0+M]$, Dirichlet polarization gives
     $$2\,\widetilde{\mathcal{D}}_N(M_0, M; c) = -E_N(M_0, M; c) + s_{N,c}(M_0+M+1)^2 - s_{N,c}(M_0+1)^2.$$
     The boundary term vanishes for all weights $c$ iff $\sigma_N(M_0+M+1) = \sigma_N(M_0+1)$ (and for all squarefree weights iff $\operatorname{rad}_N(M_0+M+1) = \operatorname{rad}_N(M_0+1)$), replacing period return $L_N \mid M$ by multiplicative fiber return.
  3. **Non-Periodic Pronic Integration (`ShortHorizonPronicDiscrepancyAndVonMangoldtDuality`, `AllDepthHilbertDilationCubeAndHyperCubeGramFactorization`):** Weighting by $\frac{1}{M(M+1)}$ on $[1, \infty)$ turns $L_N(M, c)$ directly into $-\sum_{e=2}^N \Lambda(e) Y_{N,c}(e)$. The pronic Gram matrix splits as $\mathcal{G} = \Lambda\Lambda^\top + \mathcal{G}^{\mathrm{ec}}$ ($\mathcal{G}^{\mathrm{ec}} \succeq 0$) and satisfies the prime-dilation recurrence $\mathcal{G}^{\mathrm{ec}}(pq, pr) + \mathcal{G}^{\mathrm{ec}}(pq, r) + \mathcal{G}^{\mathrm{ec}}(q, pr) = (p-1)\mathcal{G}^{\mathrm{ec}}(q, r) + (p-1)\Lambda(q)\Lambda(r)$, which iterates across all multiplicative depths $k = \omega(m)$ via `pmHyperCubeGramSum`.

### Mechanism 5: Downward Buchstab $L^2$ Telescope, `ker P` Mollifiers, and Cross-Corpus Wall 1 Tools
* **Problem:** Track how prefix energy $\mathcal{E}_N(M; c)$ or energy-centered variance varies with the cutoff $N$, and leverage existing `BiScaleUncertainty`, `RHTower`, and `TransHorizonIncidenceMechanics` results for Wall 1 (`docs/reports/walls/bezout-wall1-programme.md`).
* **How it works:**
  1. **Downward $L^2$ Telescope (`bvi_buchstab_l2_sawtooth_step_and_three_band_energy`):** For $M \le N$, Möbius inversion gives $s_{N,\mu}(k) = \mathbf{1}_{k=1}$ on $[1, M]$, so $\mathcal{E}_M(M; \mu) = 1$. Telescoping downward from $M$ to $N < M$ expresses $\mathcal{E}_N(M; \mu)$ as $1$ minus the horizon steps $n \in [N, M-1]$. At prime steps $p = n+1$, the step couples to $L_n(\lfloor M/p \rfloor, c)$ and obeys universal scale-halving subadditivity $\mathcal{E}_n(M; c) \le \mathcal{E}_{n+1}(M; c) + \mathcal{E}_n(\lfloor M/p \rfloor; c)$.
  2. **Natural-Cutoff Cofactor Identities (`NaturalCutoffMultiDepthCofactorAndConditionalTailBridge`):** For $\varepsilon>0$, prime $p$, and $p\nmid r$, the actual Ramanujan weight satisfies $Y_\varepsilon(pr)=-Y_\varepsilon(r)/(p^{1+\varepsilon}-1)$ (`pmRealRamanujanWeight_prime_mul`). The finite head identity requires $1\le R<p$ and observation horizon $N<p$; it contains a prime head and a cumulative-prefix correction. The complete variance splits into head energy, $(H+1)$ times the squared head mean, and centered tail variance. This is not a one-factor recursion for the complete energy; the head mean and cross-depth costs remain.
  3. **Barban–Vehov / `ker P` Annihilation & Kloosterman / Cotangent / Schur Collar Bridges (`BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge`, `BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge`):**
     * **Tool 1 (`ker P` & Barban–Vehov):** `kerPEndpointWeight N c` annihilates the $e = 1$ harmonic mode so `sieveVariance = selbergTotientDiagonalForm` and `sievePrefixDiscrepancy` is drift-free; `barbanVehovWeight X` vanishes in Selberg coordinates for $X < e \le N$ and achieves $O(1/\log X)$ normalized variance (`sieveVariance_and_bezout_normalizedBarbanVehovWeight_le_inv_log`); `DeletionAveragedDivisor.divisorSource X M` annihilates all composite divisors on $2 \le k \le X$.
     * **Tool 2 (Beurling vs. $\mathbb{Z}$-Lattice Bézout Seeds & Pronic Log Sandwich):** Abstract Beurling systems satisfy Möbius inversion, strict Gibbs log-submodularity, and zero/one/higher large-prime splits (`beurling_universal_gibbs_and_gauge_package`, `beurling_zero_one_higher_large_label_decomposition`), whereas $\mathbb{Z}$-lattice dilation profiles isolate the least positive Bézout successor seed $p a = q b + 1$ (`beurling_invariance_vs_bezout_successor_seed_wall1_bridge`) and satisfy the pronic logarithmic-convolution energy sandwich (`pmPowerDamped_log_covariances_sandwich`).
     * **Tool 3 (Distinct-Modulus Kloosterman & Logarithmic Cotangent Transport):** Complete $\operatorname{lcm}(q+1, r+1)$ Kloosterman blocks vanish for $q \ne r$ with cross-frequency fibre cardinality $\le \gcd(q+1, r+1)$ (`kloosterman_distinct_modulus_terminal_and_gcd_fibre_bridge`), and chronological Kuzmin–Landau cotangent transport on `logarithmicPhase n t` links strictly decreasing harmonic increments to `sourcePhaseDefect σ t M` (`logarithmic_cotangent_transport_and_zeta_source_wall1_bridge`).
     * **Tool 4 (Horizon-Uniform Schur Collar & Damped Radical-Fiber Margin):** `oddProfile_le_four_exp_four_mul_sub` discharges the CHMD Schur ratio constant $\kappa(t) = 4 e^{4t}$ unconditionally (`unconditional_schur_collar_and_low_prime_budget_wall1_bridge`), and `strict_mobius_margin_and_damping_stability_wall1_bridge` transfers the strict defect margin $D_N(M; c_\varepsilon) < -1/2$ across infinite radical fibers and prime powers.

---

## 4. Known Traps & Obstructions (Do Not Fall Into These)

1. **Trap 1 — Combinatorial Pronic Reach $\ne$ Analytic Cancellation:**
   On $n \in [1, M]$, consecutive products $n(n+1)$ can be divisible by $d \in (M, M(M+1)]$. However, a single modulus $d > M$ has $\lfloor M/d \rfloor = 0$ on $[1, M]$ and contributes only deterministic linear drift $-M c(d)/d$ to $L_N(M, c)$. Never claim that $d \mid n(n+1)$ for $d > M$ by itself yields $O(M^{1/2+\varepsilon})$ cancellation.
2. **Trap 2 — Symmetric Return Windows Fail at Length $2N - 4$:**
   Around a common return $R$ ($\forall d \le N,\, d \mid R$), vanishing of $L_N(M, c)$ on the symmetric window $[R - (N-2), R + (N-2)]$ (or on $[R - (N-2), R + (N-3)]$ of length $2N-4$) does **not** force $c(2) = \dots = c(N) = 0$. The second-difference extremizer `returnWindowCriticalKernelWeight N` supported on $\{1, N-2, N-1, N\}$ vanishes identically on $[R - (N-2), R + (N-3)]$. Always use the asymmetric $(2N-3)$-point window $[R - (N-2), R + (N-1)]$.
3. **Trap 3 — Compressed Lag Operators Are Non-Markovian ($\widehat{T}_1^2 \ne \widehat{T}_2$):**
   At mode $p^{a+1}$ ($p$ prime, $a \ge 1$), every positive lag below $p^a$ is invisible, but $\lambda_{p^{a+1}}(p^a) = -1/(p-1) \ne 0$ (`sieveLagMultiplier_prime_pow_revival_at_clock`). Squarefree support does not restore composition: `nonMarkovianLagDefect_first_octave_table` gives $\lambda_q(2)-\lambda_q(1)^2=-3/4$ at both $q=3$ and $q=6$. Replacing $\widehat{T}_h$ by $\widehat{T}_1^h$ requires proving that identity on the signal's actual mode support.
4. **Trap 4 — Quadratic & Odd Moments Are Blind to Even-Mode Sign Flips:**
   All 2-point lag correlations depend only on $Y_{N,c}(q)^2$. On the even-mode sector $q \in \{6, 10\}$ (`evenPairReal a b`), every odd-order translated moment vanishes identically by period-15 antiperiodicity, and every translated moment of degree $\le 5$ is invariant under $(a, b) \mapsto (a, -b)$. Recovering the relative sign requires degree $6$.
5. **Trap 5 — Valuation-Clock Collisions Below $\varphi(p^a)$:**
   Observing $t \mapsto \gcd(k+t, p^a)$ on a window of length $W < \varphi(p^a) = p^a - p^{a-1}$ cannot distinguish $k = 1$ from the clock-shifted state $\ell = 1 + p^{a-1}$ (`gcd_prime_pow_collision_below_totient`). The threshold $W \ge \varphi(p^a)$ (and globally $W \ge \Phi_{\max}(N) = \max_{p^a \le N} \varphi(p^a) < N$) is sharp.
6. **Trap 6 — Losing Signs and Misreading the Damping Quantifiers:**
   Absolute estimates can discard the cancellation between Euler depths. Divergence of their constants as $\varepsilon\downarrow0$ alone does not obstruct the RH receiver. It asks for horizon-uniform finite bounds at arbitrarily small positive dampings, and permits a different bound $B_\varepsilon$ at each damping. Neither a uniform-in-$\varepsilon$ constant nor a particular adjacent-depth pairing method is required. For reference, $\prod_p(1+p^{-1-2\varepsilon})=\zeta(1+2\varepsilon)/\zeta(2+4\varepsilon)$; this product by itself is not an estimate for the complete source energy.
7. **Trap 7 — Purely Multiplicative / Beurling-Invariant Identities Cannot Close Wall 1 Alone:**
   Divisor Möbius inversion, squarefree exponential-Gibbs log-submodularity (`gibbsWeight_mul_lt`), and zero/one/higher large-prime decompositions (`phi_eq_apertureSum_sub_tsum_add`) hold on arbitrary abstract `BeurlingSystem`s (`BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge`). Breaking the Beurling obstruction requires coupling to $\mathbb{Z}$-specific additive successor gaps $p a - q b = 1$ (`leastSuccessorSeed`, `pronicSeq`).

---

## 5. Thematic Map of Key Entry-Point Modules

Start from these entry points for each topic:

* **Initial-Prefix Inversion, Smith Normal Form & Conditioning:**
  * [`SharpInitialPrefixObservabilityAndExactGramDeterminants.lean`](SharpInitialPrefixObservabilityAndExactGramDeterminants.lean) — Rational prefix matrix $P_n$, $\det(P_n) = (-1)^n/(n+1)$, Selberg Gram determinant.
  * [`IntegralPrefixLatticeAndPrimePowerObstructions.lean`](IntegralPrefixLatticeAndPrimePowerObstructions.lean) — Unimodular Smith normal form $U_n A_n V_n = \operatorname{diag}(1, \dots, n)$ and $\ker(A_n \bmod p^a)$.
  * [`TranslatedWindowStrideAnnihilationAndLcmReturnObservability.lean`](TranslatedWindowStrideAnnihilationAndLcmReturnObservability.lean) — $2\tau(d)$ prefix conditioning and translated-window stride annihilation.
* **Return Windows, Sub-Horizon Phase Observability & Short-Window Defects:**
  * [`ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean`](ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean) — Return-window reflection law, $2N-3$ injectivity, and the $2N-4$ extremizer.
  * [`TwoLagFiveModePolytopeAndHigherMomentPhaseRecoveryBridge.lean`](TwoLagFiveModePolytopeAndHigherMomentPhaseRecoveryBridge.lean) — Sub-$N$ totient threshold $\Phi_{\max}(N) < N$ and exact $\frac{2d}{d-1}(\tau(d)-1)$ active-sawtooth power conditioning.
  * [`ClockWaveletTensorBuchstabL2TelescopeAndShortWindowBridge.lean`](ClockWaveletTensorBuchstabL2TelescopeAndShortWindowBridge.lean) — Short-window iso-state classification ($\widetilde{\mathcal{D}}_N(M_0, M; c) \le 0 \iff \sigma_N(M_0+M+1) = \sigma_N(M_0+1)$), downward Buchstab $L^2$ step laws, and composite clock-wavelet tensors.
* **Spectral Polytopes, Multi-Lag Cones & $k$-Tuple Admissibility:**
  * [`SharpPrimitiveEnergySuccessorFrontier.lean`](SharpPrimitiveEnergySuccessorFrontier.lean) — The 4-mode $\{2, 3, 4, 6\}$ frontier for $(\operatorname{Var}, \operatorname{Cov}_1, \mathcal{E}_{\mathrm{prim}})$.
  * [`TwoLagFiveModePolytopeAndHigherMomentPhaseRecoveryBridge.lean`](TwoLagFiveModePolytopeAndHigherMomentPhaseRecoveryBridge.lean) — The 5-mode $\{2, 3, 4, 6, 12\}$ cone for $(\operatorname{Var}, \operatorname{Cov}_1, \operatorname{Cov}_2, \mathcal{V}_{H_3}, \mathcal{E}_{\mathrm{prim}})$ and 3rd/6th-moment signed coordinate recovery.
  * [`TupleAdmissibilityCollisionEnergyAndHardyLittlewoodCoercivity.lean`](TupleAdmissibilityCollisionEnergyAndHardyLittlewoodCoercivity.lean) — General $k$-tuple Hardy–Littlewood sum-of-squares identity and $S_p(H) \ge k^2/\varphi(p)$ coercivity.
* **Lag Operator Algebra & Visibility Clocks:**
  * [`ArithmeticLagSchedulesAndSharpRecoveryHorizon.lean`](ArithmeticLagSchedulesAndSharpRecoveryHorizon.lean) — Visibility clock $\tau_{\mathrm{vis}}(q) = q/\operatorname{rad}(q)$ and quadratic mode recovery.
  * [`NonMarkovianLagOperatorAlgebraAndPrimePowerRevival.lean`](NonMarkovianLagOperatorAlgebraAndPrimePowerRevival.lean) — Prime-power revival at its visibility clock and squarefree counterexamples to the lag semigroup law.
* **Non-Periodic Pronic Gram Matrix, Multi-Depth Factorization & Cross-Corpus Wall 1 Bridges:**
  * [`UniversalSawtoothInteriorMartingaleAndPostStepCalculus.lean`](UniversalSawtoothInteriorMartingaleAndPostStepCalculus.lean) — Pointwise Bézout interior sawtooth and drift-square cancellation.
  * [`EnergyCenteredPronicGramPositivityAndVonMangoldtLowerBound.lean`](EnergyCenteredPronicGramPositivityAndVonMangoldtLowerBound.lean) — Rank-1 von Mangoldt + PSD energy-centered split $\mathcal{G} = \Lambda\Lambda^\top + \mathcal{G}^{\mathrm{ec}}$.
  * [`AllDepthHilbertDilationCubeAndHyperCubeGramFactorization.lean`](AllDepthHilbertDilationCubeAndHyperCubeGramFactorization.lean) — All-depth $2^k$ Hilbert dilation hypercube factorization of $\mathcal{G}^{\mathrm{ec}}$.
  * [`NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean`](NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean) — Restricted prime-cofactor identities and the complete head/mean/tail variance decomposition.
  * [`DilationSuccessorLeastSeedResonance.lean`](DilationSuccessorLeastSeedResonance.lean) & [`DilationSuccessorDigammaRenormalization.lean`](DilationSuccessorDigammaRenormalization.lean) — Integer dilation jump sectors, least Bézout seed resonance, and digamma finite-part renormalization.
  * [`RamanujanRadicalDilationReduction.lean`](RamanujanRadicalDilationReduction.lean) — Exact reduction of the original rational dilation profile: with $s=\operatorname{rad}(r)$ and $v=r/s$, $\Phi_r(p/q)=v\Phi_s(p/q)$. Reuses the valuation clock and totient quotient; individual finite sectors still require their physical cutoff correction.
  * [`DilationClockSectorBoundaryAndSuccessorTransport.lean`](DilationClockSectorBoundaryAndSuccessorTransport.lean) — Exact signed sector reduction with boundary term $v(1/(T+1)-v/(H+1))M_s(h,T)$, where $T=\lfloor H/v\rfloor$. At $H=v(T+1)-1$, the radical's successor sector transports to original physical lag $v$.
  * [`DilationClockSuccessorSeedCoupling.lean`](DilationClockSuccessorSeedCoupling.lean) — Least-seed coupling of the actual profile at its physical visibility clock, with the full signed complement retained. The radical seed is nonzero exactly for coprime scales.
  * [`DilationClockRelativeGapAndSignedComplement.lean`](DilationClockRelativeGapAndSignedComplement.lean) — The literal clock-successor sector has relative-gap and inverse-scale bounds. Its finite signed complement approximates the original profile at the same physical cutoff; nonzero least-seed amplitude alone gives no uniform lower bound.
  * [`DilationClockComplementPrimeSurvival.lean`](DilationClockComplementPrimeSurvival.lean) — Arbitrarily large nearby prime pairs have a single clock-successor sector tending to zero while the retained finite signed complement approaches the positive diagonal Gram. The cutoff and sector costs admit an explicit relative-gap plus inverse-scale estimate.
  * [`PronicResidueGapEnergyAndPrimePairDistance.lean`](PronicResidueGapEnergyAndPrimePairDistance.lean) — Exact residue-gap energy bounds; `sum_Ico_reciprocal_pronic` exports the existing interval identity $\sum_{n=a}^{b-1}1/(n(n+1))=1/a-1/b$ for $0<a\le b$.
  * [`BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge.lean`](BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge.lean) — `ker P` endpoint projection, Barban–Vehov $O(1/\log X)$ mollifier variance, Levinson GCD-power quadratic form, Vasyunin pronic tail Gram producer, distinct-modulus Kloosterman GCD fibres, and pronic logarithmic-convolution energy sandwich.
  * [`BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge.lean`](BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge.lean) — Abstract Beurling Gibbs/aperture laws vs. $\mathbb{Z}$-lattice Bézout successor seeds, Kuzmin–Landau cotangent transport on `logarithmicPhase`, unconditional $\kappa(t) = 4e^{4t}$ Schur collar ratio, and uniform positive-damping stability on radical fibers.
