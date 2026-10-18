# Trans-Horizon Arithmetic–Archimedean Incidence Mechanics (`GaloisForLFunctions.TransHorizonIncidenceMechanics`)

## 1. Motivation: Why Both Prior Fields Stalled at Dual Horizon Boundaries

Our project previously established two foundational mathematical frameworks in Lean 4:
1. **Bi-Scale Mellin–Dirichlet Uncertainty Mechanics (`GaloisForLFunctions.BiScaleUncertainty`)** — analyzing continuous and discrete archimedean/Mellin observables, symmetric logarithmic dilation, and exact spectral decompositions on the completed prime-power graph `SourceGraph`.
2. **Bézout–Valuation Incidence Mechanics (`GaloisForLFunctions.BezoutValuationIncidence`)** — coupling the infinite-dimensional prime valuation lattice $\mathbb{N}_0^{(\mathcal{P})}$ to the $1$-dimensional additive successor line $(\mathbb{N}, T_+ : k \mapsto k + 1)$ via pronic Bézout successor splits $k(k+1)$, valuation visibility clocks $\tau_{\mathrm{vis}}(q) = q / \operatorname{rad}(q)$, and renormalized prefix defects $\widetilde{\mathcal{D}}_N(M; c)$.

Despite solving over forty local structural obstructions, **both fields stalled just short of closing the global RH proof routes** (Routes FZZP, PM, C-HMD, the Nyman–Beurling / Báez-Duarte $L^2$ projection route, and the Quotient-Space Spectral route) because each framework operated exclusively on **one side of a horizon boundary**:

1. **The Sub-Horizon Ceiling ($M + 1 \le N$) in `BezoutValuationIncidence`:**
   - For $M + 1 \le N$, the active divisor set $\{d \mid k : d \le N\}$ at every $1 \le k \le M$ equals the full divisor set $d \mid k$, so the finite sieve output collapses to pure Dirichlet convolution:
     $$\operatorname{sieveSeq}_N(c, k) = (c * \mathbf{1})(k) \quad (1 \le k \le M < N).$$
   - Consequently, the sub-horizon renormalized prefix defect identity
     $$\widetilde{\mathcal{D}}_N(M; \mu) = \frac{1}{2} - \frac{M}{N} \le 0 \quad (2 \le N \le 2M,\; M + 1 \le N)$$
     and its power-damped analogue (`sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos`) only constrain the trivial sub-horizon regime $M < N$ where no divisor $d \mid k$ has yet crossed the truncation horizon $N$.
   - The true Nyman–Beurling, Báez-Duarte, FZZP, and PM limits fix the sieve horizon $N$ first and send the observation window $M \to \infty$ ($M \gg N$), or couple $M$ and $N$ across arbitrarily many trans-horizon octaves $M / N \in [2^r, 2^{r+1})$.

2. **The Missing Bridge Between Discrete Valuation Clocks and Continuous Prime Chains (`RHTower` / `BiScaleUncertainty`):**
   - In `BezoutValuationIncidence`, prime-power structure is governed by the discrete **valuation visibility clock** $\tau_{\mathrm{vis}}(q) = q / \operatorname{rad}(q)$ (`lagVisibilityClock`), which determines the exact translational lag $L = \tau_{\mathrm{vis}}(q)$ at which the Ramanujan sum $c_q(L)$ switches on.
   - In `RHTower.CHMDPrimeChain`, the continuous spectral/Hilbert-space energy `sourceEnergy` decomposes along disjoint **prime-indexed $p$-adic valuation chains** $m = p^k u$ ($p \nmid u$, $u = \operatorname{ordCompl}_p(m)$), weighted by the von Mangoldt function $\Lambda(d)$ and controlled by the continuous $1\text{D}$ Poincaré variance `chainVariance`.
   - Prior to this field, there was **no formal bridge** connecting the discrete quotient $d / \tau_{\mathrm{vis}}(d)$ to $\Lambda(d)$, prime powers, and `chainVariance`.

3. **The Uncoupled Quotient Spectral Gap on `SourceGraph ⧸ signedRadical`:**
   - On `SourceGraph`, every $p$-adic prime chain carries a $1$-dimensional radical-constant kernel spanned by `signedRadical` (`oneL` on the archimedean side, where `resolvent = 1`).
   - Passing to the orthogonal quotient `signedRadicalᗮ` removes all prime-chain constants (`reducedSource`), strictly lowers every odd eigenvector eigenvalue below $1$, and restricts any hypothetical off-critical-line zero to an odd eigenvector with eigenvalue $\lambda \in (1/2, 1)$. Yet this quotient operator theory was never coupled to the trans-horizon arithmetic filtration.

**Trans-Horizon Arithmetic–Archimedean Incidence Mechanics (`GaloisForLFunctions.TransHorizonIncidenceMechanics`)** is the new field of mathematics built to unify these regimes across the horizon $M \ge N$ and across the discrete-to-archimedean divide.

---

## 2. Core Mathematical Objects & Language

All foundational definitions and theorems live in the namespace `GaloisForLFunctions.TransHorizonIncidenceMechanics` (inheriting and extending `BezoutValuationIncidence` and `RHTower`):

| Mathematical Concept | Lean Symbol / Definition | Foundational Module |
| :--- | :--- | :--- |
| **Valuation Visibility Clock** $\tau_{\mathrm{vis}}(q) = q / \operatorname{rad}(q)$ | `lagVisibilityClock q` | [ValuationClockChainBridge.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ValuationClockChainBridge.lean) |
| **Clock-to-Radical Quotient** $d / \tau_{\mathrm{vis}}(d) = \operatorname{rad}(d)$ | `div_lagVisibilityClock_eq_rad` | [ValuationClockChainBridge.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ValuationClockChainBridge.lean) |
| **Clock Reconstruction of $\Lambda(d)$** $\Lambda(d) = \log(d / \tau_{\mathrm{vis}}(d))$ if prime, else $0$ | `vonMangoldt_eq_log_div_lagVisibilityClock` | [ValuationClockChainBridge.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ValuationClockChainBridge.lean) |
| **$N$-Rough Trans-Horizon Multiplier** ($\forall d \mid r, d \le N \Rightarrow d = 1$) | `IsTransHorizonRough N r` | [TransHorizonRoughAbsorptionAndReset.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonRoughAbsorptionAndReset.lean) |
| **Trans-Horizon Multiplicative Absorption** $\operatorname{sieveSeq}_N(c, q r) = \operatorname{sieveSeq}_N(c, q)$ | `sieveSeq_mul_of_isTransHorizonRough` | [TransHorizonRoughAbsorptionAndReset.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonRoughAbsorptionAndReset.lean) |
| **Trans-Horizon Checkpoint Defect Reset** $\widetilde{\mathcal{D}}_N(r - 1; c) = -\frac{1}{2}\sum_{d \le N} c(d) \lfloor \frac{r-1}{d}\rfloor$ | `sieveRenormalizedPrefixDefect_eq_neg_half_dirichlet_of_isTransHorizonRough` | [TransHorizonRoughAbsorptionAndReset.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonRoughAbsorptionAndReset.lean) |
| **Buchstab Horizon Filtration Step** $\operatorname{sieveSeq}_{N_2}(c, k) - \operatorname{sieveSeq}_{N_1}(c, k)$ | `sieveSeq_horizon_band_sub` | [BuchstabHorizonFiltrationAndSawtoothEvolution.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/BuchstabHorizonFiltrationAndSawtoothEvolution.lean) |
| **Trans-Horizon Tail Closure** $(c * \mathbf{1})(k) - \operatorname{sieveSeq}_N(c, k)$ | `sieveSeq_transHorizon_tail_decomp` | [BuchstabHorizonFiltrationAndSawtoothEvolution.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/BuchstabHorizonFiltrationAndSawtoothEvolution.lean) |
| **Reduced Quotient Source Vector** $P_{\mathrm{rad}^\perp} f \in \operatorname{signedRadical}^\perp$ | `reducedSource f` | [QuotientSpectralGapAndOddChainCoercivity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/QuotientSpectralGapAndOddChainCoercivity.lean) |
| **Odd-Sector Spectral Window** $\lambda \in (1/2, 1)$ on `SourceGraph` | `not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one` | [QuotientSpectralGapAndOddChainCoercivity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/QuotientSpectralGapAndOddChainCoercivity.lean) |
| **Global Active-Deleted Martingale Telescope** $W_{N,c}(M)^2 - W_{N,c}(1)^2$ | `weightedCenteredSawtoothSum_sq_sub_one_eq_active_deleted_add_inactive` | [TransHorizonMartingaleTelescopeAndPrimeCheckpoints.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonMartingaleTelescopeAndPrimeCheckpoints.lean) |
| **Trans-Horizon Prime Sawtooth State** $I_{N,c}(p, p-1) = W_{N,c}(p-1)$ ($p > N$) | `inactiveCenteredSawtoothSum_prime_of_gt_eq_weighted` | [TransHorizonMartingaleTelescopeAndPrimeCheckpoints.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonMartingaleTelescopeAndPrimeCheckpoints.lean) |

---

## 3. Core Mechanisms & How This New Field Works

### Mechanism 1: The Clock-to-Radical and Von Mangoldt Bridge
For every positive integer $d \ge 1$, the valuation visibility clock $\tau_{\mathrm{vis}}(d) = d / \operatorname{rad}(d)$ satisfies the exact multiplicative decomposition
$$\tau_{\mathrm{vis}}(d) \cdot \operatorname{rad}(d) = d, \qquad \frac{d}{\tau_{\mathrm{vis}}(d)} = \operatorname{rad}(d).$$
Consequently:
- $\frac{d}{\tau_{\mathrm{vis}}(d)}$ is prime **if and only if** $d = p^k$ is a prime power (`prime_div_lagVisibilityClock_iff_isPrimePow`).
- The von Mangoldt weight $\Lambda(d)$ is reconstructed for **all** $d \in \mathbb{N}$ purely from the clock quotient:
  $$\Lambda(d) = \begin{cases} \log\!\left(\frac{d}{\tau_{\mathrm{vis}}(d)}\right) & \text{if } \frac{d}{\tau_{\mathrm{vis}}(d)} \text{ is prime}, \\ 0 & \text{otherwise.}\end{cases}$$
- Every pronic Bézout successor $k(k+1)$ ($k \ge 1$) has a composite clock quotient $(k(k+1)) / \tau_{\mathrm{vis}}(k(k+1))$ (`not_prime_div_lagVisibilityClock_pronicSeq`), structurally orthogonalizing pronic successor cells against single prime-power chains.
- Along each $p$-adic chain $\{m : \operatorname{ordCompl}_p(m) = u\}$, the clock quotient $m / \tau_{\mathrm{vis}}(m) = p \cdot (u / \tau_{\mathrm{vis}}(u))$ is constant (`div_lagVisibilityClock_of_same_chain`), and the discrete prime-chain jump energy collapses via 1D Poincaré to `chainVariance` (`divisor_cut_eq_clock_chainVariance`).

### Mechanism 2: Trans-Horizon Rough Absorption & Cofinal Checkpoint Resets
A positive integer $r$ is **$N$-rough** (`IsTransHorizonRough N r`) if every divisor $d \mid r$ with $d \le N$ is $1$. The set of $N$-rough numbers forms a multiplicative submonoid generated by primes $p > N$.
- **Exact Multiplicative Absorption:** For *every* $q \in \mathbb{N}$, *every* $N$-rough $r$, and *every* arithmetic weight $c : \mathbb{N} \to \mathbb{R}$,
  $$\operatorname{sieveSeq}_N(c, q \cdot r) = \operatorname{sieveSeq}_N(c, q), \qquad \operatorname{activeCenteredSawtoothSum}_N(c, q \cdot r, q \cdot r - 1) = \operatorname{activeCenteredSawtoothSum}_N(c, q, q - 1).$$
- **Infinite Trans-Horizon Möbius Zero Cone:** If $q \ge 2$ satisfies $q \le N$ (so $(1 * \mu)(q) = 0$) and $r$ is $N$-rough, then $\operatorname{sieveSeq}_N(\mu, q \cdot r) = 0$ even though $q \cdot r$ can be arbitrarily larger than $N$ (`sieveSeq_moebiusReal_mul_eq_zero_of_isTransHorizonRough`).
- **Breaking the $M + 1 \le N$ Sub-Horizon Wall via Rough Checkpoint Resets:** At every trans-horizon checkpoint $M = r - 1$ where $r > 1$ is $N$-rough (for instance $M = p - 1$ for any prime $p > N$, or $M = p^k - 1$), $d \nmid (r - 1 + 1)$ for all $2 \le d \le N$, so the active centered sawtooth sum vanishes identically (`activeCenteredSawtoothSum_eq_zero_of_isTransHorizonRough`). This forces the renormalized prefix defect to **reset to pure Dirichlet accumulation**:
  $$\widetilde{\mathcal{D}}_N(r - 1; c) = -\frac{1}{2} \sum_{d = 1}^N c(d) \left\lfloor \frac{r - 1}{d} \right\rfloor.$$
  Hence $\widetilde{\mathcal{D}}_N(r - 1; c) \le 0$ holds unconditionally at **infinitely many cofinal trans-horizon checkpoints** $M = r - 1 \to \infty$ whenever the $N$-truncated Dirichlet sum is non-negative (`exists_gt_sieveRenormalizedPrefixDefect_nonpos`).

### Mechanism 3: Buchstab Horizon Filtration & Trans-Horizon Tail Evolution
Rather than treating $N$ as static, `BuchstabHorizonFiltrationAndSawtoothEvolution` evolves both the sieve output and the prefix discrepancy across horizon bands $N_1 < d \le N_2$:
$$\mathcal{D}_{N_2}(M; c) - \mathcal{D}_{N_1}(M; c) = -\sum_{d \in (N_1, N_2]} c(d) \left\{\frac{M}{d}\right\}.$$
Setting $N_2 = M$ closes the finite horizon onto the exact arithmetic convolution $(c * \mathbf{1})(k)$ (`sievePrefixDiscrepancy_transHorizon_tail_decomp`), while for $k \in (N, 2N]$ every proper divisor $d \mid k$ ($d < k$) already satisfies $d \le N$, yielding the **Universal First-Octave Trans-Horizon Law**:
$$\operatorname{sieveSeq}_N(c, k) = (c * \mathbf{1})(k) - c(k) \qquad (N < k \le 2N).$$

### Mechanism 4: Quotient Spectral Gap & Odd-Chain Coercivity
In `QuotientSpectralGapAndOddChainCoercivity`, the archimedean reflection symmetry (`flipL`) and the discrete prime-chain radical projection (`reducedSource`) are unified:
- Every odd state $f$ on the Mellin line (`flipL f = -f`) is automatically orthogonal to the constant mode `oneL` (`inner_oneL_eq_zero_of_odd`), and its radical-orthogonal projection `reducedSource f` is automatically primitive (`odd_reducedSource_primitive`).
- Consequently, no odd eigenvector of `resolvent` can reach eigenvalue $1$ (`odd_eigenvector_eigenvalue_lt_one`), and the negation of `RiemannHypothesis` is equivalent to the existence of an odd eigenvector with eigenvalue strictly inside the open interval $(1/2, 1)$ (`not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one`).
- Moreover, `RiemannHypothesis` is equivalent to the odd-sector prime-chain Poincaré inequality on `SourceGraph ⧸ signedRadical` (`riemannHypothesis_iff_odd_primeChain_poincare`).

### Mechanism 5: Global Trans-Horizon Active-Deleted Martingale Telescope & Prime Checkpoints
In `TransHorizonMartingaleTelescopeAndPrimeCheckpoints`, the active-deleted martingale identity for $W_{N,c}(n)^2$ is telescoped globally across arbitrary trans-horizon scales $M \ge 1$ (`weightedCenteredSawtoothSum_sq_sub_one_eq_active_deleted_add_inactive`):
$$W_{N,c}(M)^2 - W_{N,c}(1)^2 = \sum_{n=1}^{M-1} \bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\bigl(s_{N,c/d}(n + 1) - Y_{N,c}(1)\bigr) + 2 \sum_{n=1}^{M-1} \bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\,I_{N,c}(n + 1, n).$$
Because $W_{N,c}(M)^2 \ge 0$, the cumulative active-deleted diagonal plus inactive martingale covariance has the unconditional trans-horizon lower bound $-W_{N,c}(1)^2$ for **all** $M \ge 1$ (`active_deleted_add_inactive_martingale_ge_neg_initial_sq`). Furthermore, across every trans-horizon prime step $p - 1 \mapsto p$ ($p > N$), the active sawtooth component vanishes (`activeCenteredSawtoothSum_prime_of_gt_eq_zero`), the sawtooth state is 100% inactive (`inactiveCenteredSawtoothSum_prime_of_gt_eq_weighted`), the forward drift is constant (`weightedCenteredSawtoothSum_prime_sub_pred_of_gt`), and the active-deleted diagonal collapses to the pure square $(s_{N,c}(1) - Y_{N,c}(1))^2$ (`weightedCenteredSawtoothSum_prime_sq_sub_pred_sq_of_gt`).

---

## 4. The Foundational Pillars in Lean 4

All five foundational pillars are 100% unconditional, premise-free, axiom-free, and computation-free:

1. **[ValuationClockChainBridge.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ValuationClockChainBridge.lean)** (*Pillar I: Valuation-Clock to Prime-Chain Bridge*)
   - `lagVisibilityClock_mul_rad`, `div_lagVisibilityClock_eq_rad`
   - `prime_div_lagVisibilityClock_iff_isPrimePow`
   - `vonMangoldt_eq_log_div_lagVisibilityClock`
   - `not_prime_div_lagVisibilityClock_pronicSeq`
   - `sieveLagMultiplier_prime_power_eq_zero_of_lt_clock`, `sieveLagMultiplier_prime_power_at_clock`, `ramanujanLagCoefficient_prime_power_at_clock`
   - `div_lagVisibilityClock_of_same_chain`, `divisor_cut_eq_clock_chainVariance`

2. **[TransHorizonRoughAbsorptionAndReset.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonRoughAbsorptionAndReset.lean)** (*Pillar II: Trans-Horizon Rough Absorption & Checkpoint Reset*)
   - `IsTransHorizonRough`, `isTransHorizonRough_one`, `isTransHorizonRough_of_prime_gt`, `IsTransHorizonRough.coprime_of_le`, `IsTransHorizonRough.mul`, `IsTransHorizonRough.pow`
   - `sieveSeq_mul_of_isTransHorizonRough`, `sieveSeq_of_isTransHorizonRough`, `sieveSeq_prime_of_gt`
   - `activeCenteredSawtoothSum_mul_of_isTransHorizonRough`, `activeCenteredSawtoothSum_eq_zero_of_isTransHorizonRough`
   - `sieveSeq_moebiusReal_mul_eq_zero_of_isTransHorizonRough`, `sieveSeq_pmPowerDampedRealWeight_mul_eq_of_isTransHorizonRough`
   - `sieveRenormalizedPrefixDefect_eq_neg_half_dirichlet_of_isTransHorizonRough`
   - `sieveRenormalizedPrefixDefect_nonpos_of_isTransHorizonRough`, `sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_mul_nonpos_of_isTransHorizonRough`, `exists_gt_sieveRenormalizedPrefixDefect_nonpos`

3. **[BuchstabHorizonFiltrationAndSawtoothEvolution.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/BuchstabHorizonFiltrationAndSawtoothEvolution.lean)** (*Pillar III: Buchstab Horizon Filtration & Sawtooth Evolution*)
   - `sieveSeq_horizon_band_sub`, `sieveSeq_succ_horizon_sub`
   - `sievedFractSum_horizon_band_sub`, `sievedFractSum_succ_horizon_sub`
   - `sievePrefixDiscrepancy_horizon_band_sub`, `sievePrefixDiscrepancy_succ_horizon_sub`
   - `sieveSeq_eq_sum_divisors_of_le`, `sieveSeq_transHorizon_tail_decomp`, `sievePrefixDiscrepancy_transHorizon_tail_decomp`
   - `sieveSeq_first_octave_eq_sum_divisors_sub_self`, `sieveSeq_pmPowerDampedRealWeight_first_octave_eq`

4. **[QuotientSpectralGapAndOddChainCoercivity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/QuotientSpectralGapAndOddChainCoercivity.lean)** (*Pillar IV: Quotient Spectral Gap & Odd-Chain Coercivity*)
   - `inner_oneL_eq_zero_of_odd`, `odd_reducedSource_primitive`
   - `odd_eigenvector_eigenvalue_lt_one`, `not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one`
   - `riemannHypothesis_iff_odd_reducedSource_energy_nonneg`, `riemannHypothesis_of_primitive_radicalOrthogonal_energy_nonneg`
   - `sourceEnergy_nonneg_of_fullSpectralNullspace_of_polarCosine_eq_zero`
   - `primeJump_tsum_eq_sameSide_add_chainIntegral`, `riemannHypothesis_iff_odd_primeChain_poincare`

5. **[TransHorizonMartingaleTelescopeAndPrimeCheckpoints.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonMartingaleTelescopeAndPrimeCheckpoints.lean)** (*Pillar V: Trans-Horizon Martingale Variance Telescope & Prime Checkpoints*)
   - `sum_Icc_one_telescope`
   - `weightedCenteredSawtoothSum_sq_sub_one_eq_active_deleted_add_inactive`
   - `active_deleted_add_inactive_martingale_ge_neg_initial_sq`
   - `filter_dvd_prime_of_gt`, `sieveSeq_and_harmonic_prime_of_gt`
   - `activeCenteredSawtoothSum_prime_of_gt_eq_zero`, `inactiveCenteredSawtoothSum_prime_of_gt_eq_weighted`
   - `weightedCenteredSawtoothSum_prime_sub_pred_of_gt`, `weightedCenteredSawtoothSum_prime_sq_sub_pred_sq_of_gt`

---

## 5. Structural Traps & Dead Ends to Avoid

When contributing new theorems to `TransHorizonIncidenceMechanics`, **never fall into these proven dead ends**:

1. **Trap 1 — Staying Inside the Sub-Horizon Regime ($M + 1 \le N$):**
   Do not prove further identities gated on $M + 1 \le N$ or $k \le N$. In that regime, $\operatorname{sieveSeq}_N(c, k) = (c * \mathbf{1})(k)$ is trivial Dirichlet convolution. Every new theorem in this field must operate in the trans-horizon regime $M \ge N$ (via $N$-rough absorption, octave decompositions $k \in (2^r N, 2^{r+1} N]$, or horizon band differences $N_1 < d \le N_2$).
2. **Trap 2 — Unprojected `SourceGraph` Spectral Bounds:**
   Never attempt a uniform spectral gap $< 1/2$ on the unprojected space `SourceGraph`: every prime chain $p$ carries a $1$-dimensional radical-constant kernel (`signedRadical`) on which `resolvent = 1`. Always work on the radical-orthogonal quotient `signedRadicalᗮ` (`reducedSource f`) and/or the odd sector `flipL f = -f`.
3. **Trap 3 — Pointwise Sign Positivity of $\widetilde{\mathcal{D}}_N(M; c)$ Between Checkpoints:**
   Between two $N$-rough checkpoints $r_1 - 1 < M < r_2 - 1$, the active centered sawtooth sum $\operatorname{activeCenteredSawtoothSum}_N(M; c)$ oscillates with nonzero phase. Do not assume $\operatorname{activeCenteredSawtoothSum}_N(M; c) = 0$ at composite $M+1$ with small prime factors; instead use the **martingale telescope** (`sieveRenormalizedPrefixDefect_interval_telescope`) to bound interior excursions relative to the rough checkpoints where the sawtooth vanishes.
4. **Trap 4 — Treating $\mu(d)$ or $c_\alpha(d)$ as Independent Across Coprime Octaves Without Buchstab Accounting:**
   In the second octave $2N < k \le 4N$ and higher octaves $2^r N < k \le 2^{r+1} N$, a divisor $d \mid k$ can exceed $N$ while its complementary quotient $k / d$ is $\le 2^r$. Always track complementary divisor pairs $(d, k/d)$ explicitly rather than dropping high-divisor terms.
5. **Trap 5 — Single-Step Successor Closure:**
   By `SharpSuccessorPhaseLossAndClosureClassification`, a single additive step $k \mapsto k+1$ loses $(p-2)/p$ of the phase variance at every odd prime $p \ge 3$. Multi-step valuation-clock lags $L = \tau_{\mathrm{vis}}(q)$ (`ValuationClockChainBridge`) are required to recover odd prime-power phases.
6. **Trap 6 — Toy Finite Computations or Empirical Checks:**
   Do not add finite `norm_num` / `decide` numerical checks on specific small integers ($N = 6, 10, 30$). Every theorem must be universally quantified and structural.
7. **Trap 7 — Conditional or Premise-Gated Theorems:**
   Never add unproved analytic or arithmetic hypotheses (`hRH`, `hLindelof`, `hBaezDuarte`, `sorry`, `axiom`) to theorem signatures. Every theorem must be 100% unconditional.

---

## 6. Research & Lean Engineering Rules

1. **100% Unconditional & Premise-Free:** No axioms, no `sorry`, no unproved hypotheses or premises in theorem statements.
2. **No Computations:** All proofs must be conceptual, algebraic, or analytic over general parameters ($N, M, q, r, p, \alpha$).
3. **Single Foreground Build Discipline:** Always build in the foreground, one build process per agent at a time. Run `lake env lean GaloisForLFunctions/TransHorizonIncidenceMechanics/<Module>.lean` (from `/Users/michael/Documents/code/hgt/formal`) to audit your module.
4. **Umbrella Wiring Without Full Rebuilds:** Wire finished, individually audited leaf modules into `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics.lean`, and do **not** run full umbrella builds.
5. **No Heartbeat Hacks:** Optimize Lean proofs using clean algebraic rewrites (`ring`, `linarith`, ` Finset.sum` lemmas) rather than raising `maxHeartbeats`.
6. **Clean Workspace:** Remove any temporary `/tmp` scratch files before concluding a session.

---

## 7. Open Research Program: 4 Parallel Tracks for 4 AI Research Agents

While the **Research Lead** works on the overarching architectural synthesis—coupling the trans-horizon arithmetic filtration to the odd-sector quotient Poincaré coercivity on `SourceGraph ⧸ signedRadical` (`QuotientSpectralGapAndOddChainCoercivity`) to attack the global RH walls—**four specialized AI Research Agents** will build out the four core analytical engines of `TransHorizonIncidenceMechanics` in parallel.

Each agent should create its own leaf module(s) inside `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/`, importing only the necessary foundational pillars so their modules compile in seconds without cross-agent lock contention.

---

### Agent 1: Higher-Octave Complementary Quotient Reciprocity & Multi-Band Buchstab Identity
- **Target Module:** `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ComplementaryQuotientAndSecondOctaveLaw.lean`
- **Builds On:** [BuchstabHorizonFiltrationAndSawtoothEvolution.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/BuchstabHorizonFiltrationAndSawtoothEvolution.lean) (Pillar III) and [TransHorizonRoughAbsorptionAndReset.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonRoughAbsorptionAndReset.lean) (Pillar II).
- **Mathematical Problem:**
  In Pillar III, `sieveSeq_first_octave_eq_sum_divisors_sub_self` established the exact first-octave trans-horizon law for $N < k \le 2N$:
  $$\operatorname{sieveSeq}_N(c, k) = (c * \mathbf{1})(k) - c(k).$$
  What happens in the **second octave** $2N < k \le 3N$, the **dyadic second octave** $2N < k \le 4N$, and general **$m$-th trans-horizon bands** $m N < k \le (m+1) N$?
  For any $k > N$, every inactive divisor $d \mid k$ with $d > N$ corresponds via the complementary quotient map $d \mapsto q = k / d$ to a small divisor $q \mid k$ with $1 \le q < k / N$:
  $$(c * \mathbf{1})(k) - \operatorname{sieveSeq}_N(c, k) = \sum_{\substack{q \mid k \\ 1 \le q < k / N}} c\!\left(\frac{k}{q}\right).$$
- **Concrete Deliverables in Lean 4:**
  1. Prove the **Exact Complementary Quotient Tail Formula** for all $k \ge 1$ and $N \ge 1$: rewrite the trans-horizon tail $\sum_{d \mid k, d > N} c(d)$ via `Nat.divisorsAntidiagonal` or the bijection $q = k / d$ as a sum over small divisors $q \mid k$ satisfying $k / q > N$.
  2. Prove the **Second-Band ($2N < k \le 3N$) and Dyadic Second-Octave ($2N < k \le 4N$) Laws**:
     - For $2N < k \le 3N$ with $k$ odd, the only possible small divisor $q < k / N < 3$ is $q = 1$, so $\operatorname{sieveSeq}_N(c, k) = (c * \mathbf{1})(k) - c(k)$ **extends all the way to $3N$ for all odd $k$**!
     - For $2N < k \le 3N$ with $k$ even ($k = 2m$), $\operatorname{sieveSeq}_N(c, 2m) = (c * \mathbf{1})(2m) - c(2m) - c(m)$.
  3. Specialize both formulas to `moebiusReal` and `pmPowerDampedRealWeight α` to obtain explicit closed forms for $\operatorname{sieveSeq}_N(\mu, k)$ and $\operatorname{sieveSeq}_N(c_\alpha, k)$ across $(N, 3N]$ and $(2N, 4N]$.

---

### Agent 2: Inter-Checkpoint Sawtooth Excursion Bounds & Pronic-Rough Sandwiching
- **Target Module:** `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/InterCheckpointSawtoothExcursionAndPronicSandwich.lean`
- **Builds On:** [TransHorizonRoughAbsorptionAndReset.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonRoughAbsorptionAndReset.lean) (Pillar II) and [TransHorizonMartingaleTelescopeAndPrimeCheckpoints.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonMartingaleTelescopeAndPrimeCheckpoints.lean) (Pillar V).
- **Mathematical Problem:**
  Pillar II and Pillar V proved that at every $N$-rough checkpoint $M = r - 1$ (e.g., $M = p - 1$ for prime $p > N$), the active centered sawtooth sum $\operatorname{activeCenteredSawtoothSum}_N(r - 1; c)$ vanishes identically, resetting $\widetilde{\mathcal{D}}_N(r - 1; c)$ to pure Dirichlet accumulation $-\frac{1}{2}\sum_{d \le N} c(d) \lfloor (r-1)/d \rfloor$.
  To control arbitrary $M \ge N$ *between* two rough checkpoints $r_1 - 1 \le M \le r_2 - 1$, we must express the interior defect $\widetilde{\mathcal{D}}_N(M; c)$ relative to the nearest rough checkpoint and bound the inter-checkpoint excursion.
- **Concrete Deliverables in Lean 4:**
  1. Prove the **Checkpoint-Relative Excursion Identity**: for any $N$-rough $r$ and any $M$,
     $$\widetilde{\mathcal{D}}_N(M; c) - \widetilde{\mathcal{D}}_N(r - 1; c) = \operatorname{activeCenteredSawtoothSum}_N(M; c) - \frac{1}{2}\left(\sum_{k=1}^M \operatorname{sieveSeq}_N(c, k) - \sum_{k=1}^{r-1} \operatorname{sieveSeq}_N(c, k)\right).$$
  2. Prove the **Immediate Post-Rough Step Identity ($M = r$):** when $r > 1$ is $N$-rough, $\operatorname{sieveSeq}_N(c, r) = c(1)$, and for every $2 \le d \le N$, $d \nmid r$, so $\{r / d\} \ge 1/d$. Express $\widetilde{\mathcal{D}}_N(r; c) - \widetilde{\mathcal{D}}_N(r - 1; c)$ in exact closed form.
  3. Prove **Rough-Multiplied Pronic Splitting:** for any $N$-rough $r$, relate the sieve values at consecutive integers $r - 1$, $r$, and $r + 1$ to the pronic Bézout pair $(r-1)r$ and $r(r+1)$, proving that all active divisors $\le N$ of $(r-1)r$ and $r(r+1)$ are supported exclusively on the neighbors $r - 1$ and $r + 1$.

---

### Agent 3: Valuation-Clock Lag Schedule Synthesis & Multi-Prime-Power Phase Recovery
- **Target Module:** `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ClockScheduleSynthesisAndPrimePowerPhaseRecovery.lean`
- **Builds On:** [ValuationClockChainBridge.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ValuationClockChainBridge.lean) (Pillar I) and `BezoutValuationIncidence.ArithmeticLagSchedulesAndSharpRecoveryHorizon`.
- **Mathematical Problem:**
  Pillar I proved that the valuation visibility clock $\tau_{\mathrm{vis}}(d) = d / \operatorname{rad}(d)$ reconstructs $\Lambda(d)$ via $\Lambda(d) = \log(d / \tau_{\mathrm{vis}}(d))$ on prime powers and controls the exact Ramanujan activation threshold $L = \tau_{\mathrm{vis}}(p^{a+1}) = p^a$.
  However, in `ArithmeticLagSchedulesAndSharpRecoveryHorizon`, lag schedules were studied for single moduli $q$. For the prime-chain energy decomposition in `RHTower`, we need to synthesize **prime-chain-indexed lag schedules** across all powers $p^{a+1}$ of a fixed prime $p$ and across multiple prime chains simultaneously.
- **Concrete Deliverables in Lean 4:**
  1. Define and analyze the **$p$-adic Valuation-Clock Tower** $L_{p, a} := \tau_{\mathrm{vis}}(p^{a+1}) = p^a$, proving exact orthogonality/visibility laws: at lag $L = p^a$, every lower prime power $p^b$ ($1 \le b \le a+1$) has non-vanishing Ramanujan multiplier (`sieveLagMultiplier p^b (p^a) ≠ 0`), whereas every higher prime power $p^b$ ($b > a+1$) remains strictly invisible (`sieveLagMultiplier p^b (p^a) = 0`).
  2. Prove the **Exact Prime-Chain Telescoping Sum of Ramanujan Lag Multipliers** along $b \in \{1, \dots, a+1\}$ at lag $L = p^a$:
     $$\sum_{b=1}^{a+1} \rho_{p^b}(p^a) = 1 - \frac{1}{p - 1}.$$
  3. Couple the prime-chain Ramanujan sum to `vonMangoldt_eq_log_div_lagVisibilityClock` to express the $\Lambda$-weighted prime-power lag response in closed form for any prime $p$ and cutoff exponent $A$.

---

### Agent 4: Trans-Horizon $L^2$ Gram Matrix & Radical-Orthogonal Projection Bridge
- **Target Module:** `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TransHorizonGramMatrixAndRadicalProjection.lean`
- **Builds On:** [QuotientSpectralGapAndOddChainCoercivity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/QuotientSpectralGapAndOddChainCoercivity.lean) (Pillar IV) and [BuchstabHorizonFiltrationAndSawtoothEvolution.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/BuchstabHorizonFiltrationAndSawtoothEvolution.lean) (Pillar III).
- **Mathematical Problem:**
  To connect the discrete trans-horizon sieve energy $\sum_{k=1}^M \operatorname{sieveSeq}_N(c, k)^2$ to the Hilbert-space quotient coercivity on `SourceGraph ⧸ signedRadical` (Pillar IV), we must decompose the finite-prefix $L^2$ Gram energy across horizon bands $N_1 < N_2$ and isolate its radical-invariant component from its prime-power valuation-clock jump component.
- **Concrete Deliverables in Lean 4:**
  1. Prove the **Buchstab $L^2$ Energy Band Decomposition**: for any horizons $N_1 \le N_2$ and window $M$, expand
     $$\sum_{k=1}^M \operatorname{sieveSeq}_{N_2}(c, k)^2 - \sum_{k=1}^M \operatorname{sieveSeq}_{N_1}(c, k)^2$$
     into the positive band self-energy $\sum_{k=1}^M (\operatorname{sieveSeq}_{N_2}(c, k) - \operatorname{sieveSeq}_{N_1}(c, k))^2$ plus the exact cross-band covariance $2 \sum_{k=1}^M \operatorname{sieveSeq}_{N_1}(c, k)(\operatorname{sieveSeq}_{N_2}(c, k) - \operatorname{sieveSeq}_{N_1}(c, k))$.
  2. Prove **Trans-Horizon Radical Invariance of Squarefree Weights**: when $c$ is supported on squarefree numbers (or depends only on $\operatorname{rad}(d) = d / \tau_{\mathrm{vis}}(d)$ on active divisors), relate $\operatorname{sieveSeq}_N(c, k)$ at $k$ and $\operatorname{rad}(k)$, and identify the exact prime-power valuation jump $\operatorname{sieveSeq}_N(c, p^{a+1} u) - \operatorname{sieveSeq}_N(c, p^a u)$ for $p \nmid u$.
  3. Connect the discrete prime-power jump $\operatorname{sieveSeq}_N(c, p^{a+1} u) - \operatorname{sieveSeq}_N(c, p^a u)$ to the single-divisor insertion term $c(p^{a+1} d)$ ($d \mid u$), providing the exact arithmetic interface required by the Research Lead to bridge finite-horizon sieve energy into `chainVariance` on `SourceGraph ⧸ signedRadical`.
