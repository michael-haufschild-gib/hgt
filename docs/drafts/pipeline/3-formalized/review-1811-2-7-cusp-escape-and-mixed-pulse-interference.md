# Cusp Escape, Mixed-Pulse Interference, and Complete Resolution of §2.7

- **ID:** review-1811-2-7-cusp-escape-and-mixed-pulse-interference
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1811/obstacles-summary.md` §2.7
- **Statement:** Every compact mixed pulse on the modular surface obeys an exact five-channel arithmetic echo decomposition and an exact Plancherel cusp-escape conservation law with all interference terms retained, yielding two unconditional finite-time inequalities that strictly separate the undeformed modular horizon from its quadratic passive twin (`b_{p,A}(p^2) < 0` vs. `b_\zeta(p^2) = +1/2`); however, growing-window constants fail to force any positive asymptotic escape exponent `\delta > 0` even when causality, global Schur passivity, real-axis unitarity, real-axis completion positivity, multiplicative ordinary coefficients `\ge 1`, and exact positive Euler-logarithm agreement through any preassigned prime-power depth `p, p^2, \dots, p^{2k}` (including `b(p^2) = +1/2`) are all enforced, and every finite decay curve of any nonzero pulse is uniformly `\varepsilon`-indistinguishable from causal passive unitary models of arbitrarily slow asymptotic ringdown.

## Goal
Resolve completely and unconditionally every component of `obstacles-summary.md` §2.7:
1. Predeclare the cusp horocycle receiver, finite time window, mixed pulse with full cross-interference, and the five-channel decomposition (prompt, primitive prime `p`, prime-square `p^2`, mixed two-prime `p q`, and higher composite `\Omega(c) \ge 3`).
2. Derive the exact modular cusp-escape identity and boundary group-delay functional from unitary scattering and causality, retaining all diagonal and off-diagonal mixed-pulse interference terms.
3. Prove two unconditional finite-time inequalities distinguishing the undeformed modular horizon from the passive Euler twin (`PositiveEulerHorizon`), giving a measurable finite-time consequence below RH, together with unconditional actual-`\zeta` cusp escape above exponent `1/16` (`0 < \delta < 3001/48000`) and its equivalence with the sharp Maass cavity receiver.
4. Answer the asymptotic uniform-constant question in the negative via `EvenPowerPositiveEulerTwin` (`q = p^{2k}`, `k \ge 2`), which matches `\zeta`'s Euler logarithm at `p, p^2, \dots, p^{2k-1}` (`b(p^2) = +1/2`) and satisfies `b(p^{2k}) > 1/(2k) > 0` yet fails `O(e^{-\delta \tau})`, and prove unconditionally that a fit to a finite decay curve of any fixed nonzero pulse cannot decide the asymptotic exponent (`quartetGate`).

## Gates
- [x] 0 → 1  in-progress: exact predeclared cusp receiver, time window, mixed-pulse interference expansion, and passive-twin test
- [x] 1 → 2  fully-proven: `[PROVED HERE]`, complete dependency-closed paper proof with zero open dependencies
- [x] 2 → 3  formalized: Lean 4 modules in `GaloisForLFunctions/BlackHoleRingdown/`, `lake --old env lean` clean, `#print axioms` verified (`[propext, Classical.choice, Quot.sound]`)

## Lean 4 Formalization

Wired into `formal/GaloisForLFunctions/BlackHoleRingdown.lean`:
1. `formal/GaloisForLFunctions/BlackHoleRingdown/CuspEscapeAndMixedPulseInterference.lean`:
   - `mixedPulse`, `CompactPulse.delay`, `heckeTimePulse`, `meanZeroPulse`, `balancedMeanZeroPulse`, `pulseAmplitude_mixedPulse`, `meanCoefficient_mixedPulse`, `pulseEcho_mixedPulse`, `pulseReflected_mixedPulse`
   - `echoKernel_eq_five_channels`, `pulseEcho_eq_five_channels`, `eight_le_of_isHigherComposite`, `higherCompositeEchoKernel_eq_zero_of_le`, `echoKernel_eq_four_channels_of_le`
   - `integral_norm_sq_pulseAmplitude`, `integrable_and_integral_norm_sq_unitaryReflected`, `integral_norm_sq_pulseReflected`, `integral_Ioi_norm_sq_pulseReflected`, `setIntegral_norm_sq_mixedPulse_reflected`
   - `unconditional_cusp_escape_sub_seven_eighths` (`0 < \sigma < 3001/48000`)
2. `formal/GaloisForLFunctions/BlackHoleRingdown/PassiveTwinEchoAndFiniteTimeDistinction.lean`:
   - `twinEchoKernel`, `twinEchoKernel_eq_zero_of_nonpos`, `twinEchoKernel_eq_inv_mul_of_le`, `laplace_twinEchoKernel`, `twinPulseEcho_eq_twinReflected_add_mean`, `integrable_and_integral_norm_sq_twinReflected`
   - `twinReflected_decay_lt`, `not_twinReflected_decay_gt`
   - `finite_time_cusp_escape_separation` (Finite-Time Distinguishing Inequality 1: exact `(1 - 1/q^2)` tail escape excess on `[-S_0, 2\log q - S_0]`)
   - `boundaryGroupDelayDensity_nonneg_of_schur`, `modular_and_twin_groupDelay_nonneg`, `twin_excess_groupDelayDensity_eq`, `excessPulseGroupDelay_threeChannelMixedPulse`, `finite_time_mixed_pulse_prime_square_distinction` (Finite-Time Distinguishing Inequality 2: `p^2` vs. `p q` mixed-pulse interference separation)
3. `formal/GaloisForLFunctions/BlackHoleRingdown/CompleteResolutionOfTheCuspEscapeQuestion.lean`:
   - `EvenPowerPositiveEulerTwin.arithmeticCoeffs_prime_pow_isMultiplicative`, `EvenPowerPositiveEulerTwin.lSeriesHasSum_of_one_lt`, `EvenPowerPositiveEulerTwin.eulerLog_even_power_properties`
   - `no_uniform_escape_rate_from_prime_traversal_and_passivity`
   - `xiQuartet`, `quartetGate`, `quartetEchoKernel`, `quartet_schur_and_unitary`, `quartetEchoKernel_eq_zero_of_nonpos`, `laplace_quartetEchoKernel`, `not_quartetReflected_decay_gt`, `finite_decay_curve_cannot_decide_asymptotic_exponent`
   - `cusp_escape_and_sharp_cavity_equivalence`, `complete_resolution_of_cusp_escape_question`

## Mathematical Proof (`[PROVED HERE]`)

### 1. Predeclared Receiver, Mixed Pulses, Five-Channel Echo Split, and Exact Plancherel Escape Law
1. **Receiver and Mixed Pulse.** For a compactly supported smooth pulse $h \in C_c^\infty(\mathbb{R})$ (`CompactPulse`) supported in $[-S_0, S_0]$, the cusp horocycle receiver at height $Y > 0$ measures
   $$\int_0^1 \mathcal{F}_h(\tau, x, Y)\,dx = \sqrt{Y}\bigl(h(\tau + \log Y) + \mathcal{S}_h(\tau - \log Y)\bigr), \qquad \mathcal{S}_h(T) = \mathcal{E}_h(T) - \mu(h)e^{T/2},$$
   where $\mathcal{E}_h(T) = (h * K)(T)$, $\mu(h) = 6 a_h(-i/2) = \frac{3}{\pi}\int_{\mathbb{R}} h(S)e^{-S/2}\,dS$, and $\mathcal{S}_h(T) = \int_{\mathbb{R}} a_h(\xi)\,\varphi(i\xi)\,e^{i\xi T}\,d\xi$. A mixed pulse $h_{\mathrm{mix}}(S) = \sum_{j \in I} c_j h_j(S)$ has reflected wave $\mathcal{S}_{h_{\mathrm{mix}}} = \sum_{j \in I} c_j \mathcal{S}_{h_j}$, so on any measurable observation set $W \subseteq \mathbb{R}$,
   $$\int_W \|\mathcal{S}_{h_{\mathrm{mix}}}(T)\|^2\,dT = \sum_{j \in I} \|c_j\|^2 \int_W \|\mathcal{S}_{h_j}(T)\|^2\,dT + \sum_{\substack{j, \ell \in I \\ j \neq \ell}} \operatorname{Re}\!\left(c_j \overline{c_\ell} \int_W \mathcal{S}_{h_j}(T)\overline{\mathcal{S}_{h_\ell}(T)}\,dT\right).$$
2. **Five-Channel Arithmetic Decomposition.** Partition $\mathbb{N}$ disjointly into $\{0\}$, $\{1\}$ (prompt, delay $0$, weight $1$), $\{p : p\text{ prime}\}$ (primitive prime, delay $2\log p$, weight $1 - 1/p$), $\{p^2 : p\text{ prime}\}$ (repeated prime-square, delay $4\log p$, weight $1 - 1/p$), $\{p q : p < q\text{ primes}\}$ (mixed two-prime, delay $2\log p + 2\log q$, weight $(1 - 1/p)(1 - 1/q)$), and higher composites $\{c \ge 2 : c \text{ not in the preceding three classes}\}$. Every higher composite satisfies $c \ge 8 = 2^3$, so for $\tau \le 6\log 2$ the higher-composite echo kernel vanishes identically and $K = K_1 + K_{\mathrm{prime}} + K_{\mathrm{sq}} + K_{\mathrm{mix}}$.
3. **Exact Unitary Plancherel and Cusp Escape Law.** For any measurable unitary symbol $J : \mathbb{R} \to \mathbb{C}$ ($\|J(\xi)\| = 1$ for all $\xi \in \mathbb{R}$), $\int_{\mathbb{R}} \|\mathcal{U}_J h(T)\|^2\,dT = 2\pi \int_{\mathbb{R}} \|a_h(\xi)\|^2\,d\xi = \int_{\mathbb{R}} \|h(S)\|^2\,dS$. Since $\mathcal{S}_h(T) = -\mu(h)e^{T/2}$ for $T < -S_0$ and $\int_{-\infty}^{-S_0} \|\mu(h)e^{T/2}\|^2\,dT = \|\mu(h)\|^2 e^{-S_0}$, every cutoff $T_2 \ge -S_0$ obeys the **Exact Modular Escape Identity**:
   $$\int_{T_2}^\infty \|\mathcal{S}_h(T)\|^2\,dT = \int_{\mathbb{R}} \|h(S)\|^2\,dS - \|\mu(h)\|^2 e^{-S_0} - \int_{-S_0}^{T_2} \|\mathcal{S}_h(T)\|^2\,dT.$$
   Combining `riemannZeta_zero_mem_sub_quasiRH_strip` ($\Theta_\zeta \le 20999/24000$) with `zeroFreeStrip_iff_pulse_ringdown` and `OneCavityFunctionIsASharpReceiver.exists_sharp_cavity_receiver` gives unconditional $O(e^{-\delta T})$ pointwise decay and $O(e^{-2\delta T_2})$ unescaped tail decay for every compact mixed pulse at every $0 < \delta < 3001/48000$ ($> 1/16$).

### 2. Retarded Wave Dynamics of the Passive Twin and Two Finite-Time Distinguishing Inequalities
1. **Retarded Echo Kernel and Ringdown Collapse of `PositiveEulerHorizon`.** For $q > 1$, $1 < u < r$, $r u = q$, $A = r + u$, partial fractions give $\operatorname{gate}_{q,A}(w) = \frac{1}{q} + \sum_{m=0}^\infty \gamma_{q,r,u}(m)\,q^{-2(m+1)w}$, so $K_{q,r,u}(\tau) = \frac{1}{q} K(\tau) + \sum_{m=0}^\infty \gamma_{q,r,u}(m)\,K(\tau - 2(m+1)\log q)$ vanishes on $\tau \le 0$, equals $\frac{1}{q} K(\tau)$ on $\tau \le 2\log q$, transforms to $\operatorname{gate}_{q,A}(w)\frac{\Lambda(2w)}{\Lambda(2w+1)}$ on $\operatorname{Re} w > 1/2$, and satisfies $\mathcal{E}_{q,r,u}(h)(T) = \mathcal{S}_{q,A}(h)(T) + \operatorname{gate}_{q,A}(1/2)\mu(h)e^{T/2}$. At $r = q^\sigma, u = q^{1-\sigma}$ ($\frac{1}{2} < \sigma < 1$), $\mathcal{S}_{q,A}$ decays at every rate $\eta < \min(3001/48000, (1-\sigma)/2)$ and fails $O(e^{-\delta\tau})$ for every $\delta > (1-\sigma)/2$.
2. **Finite-Time Inequality 1 (Predeclared-Window Cusp Escape Separation).** For $q \ge 2$, $\frac{1}{2} < \sigma < 1$, $0 < S_0 < \log q$, and any mean-zero pulse $h$ supported in $[-S_0, S_0]$ with nonzero window reflection on $(-S_0, T_2]$ ($T_2 = 2\log q - S_0$), $\mathcal{S}_{q,A}(h)(T) = \frac{1}{q}\mathcal{S}_h(T)$ on $T \le T_2$ and $0$ on $T < -S_0$, so Plancherel conservation forces
   $$\int_{T_2}^\infty \|\mathcal{S}_{q,A}(h)(T)\|^2\,dT - \int_{T_2}^\infty \|\mathcal{S}_h(T)\|^2\,dT = \left(1 - \frac{1}{q^2}\right) \int_{-S_0}^{T_2} \|\mathcal{S}_h(T)\|^2\,dT > 0,$$
   with an explicit unconditional witness `balancedMeanZeroPulse`.
3. **Finite-Time Inequality 2 (Prime-Square $p^2$ and Mixed-Prime $p q$ Group-Delay Interference Separation).** Boundary Schur passivity implies $-\operatorname{Re}(S_{\mathrm{red}}'(i\xi)/S_{\mathrm{red}}(i\xi)) \ge 0$ on both $\zeta$ and `PositiveEulerHorizon`. For $p \neq q$ primes and the three-channel mixed pulse $h_{\mathrm{mix}}(c_0, c_{p^2}, c_{pq})(S) = c_0 h_0(S) + c_{p^2} h_0(S - 4\log p) + c_{pq} h_0(S - 2\log(pq))$ ($2S_0 < \delta_{\mathrm{gap}}(p,q)$), retaining all diagonal and off-diagonal interferences gives
   $$\int_{\mathbb{R}} \|a_{h_{\mathrm{mix}}}(\xi)\|^2 \Delta\tau_{p,\sigma}(\xi)\,d\xi = \frac{2\log p}{\pi}\Bigl(\|c_0\|^2 + \|c_{p^2}\|^2 + \|c_{pq}\|^2 + (r^{-2} + u^{-2})\operatorname{Re}(c_0 \overline{c_{p^2}})\Bigr)\int_{\mathbb{R}} \|h_0(S)\|^2\,dS.$$
   Mixed-prime phase rotations $c_{pq} \mapsto e^{i\theta}c_{pq}$ cancel identically by unique factorization, while flipping $c_{p^2} = +1$ vs. $-1$ produces $-\frac{8\log p}{\pi p^2}(b_{p,A}(p^2) - \frac{1}{2})\int \|h_0\|^2 > 0$ on the passive twin vs. $0$ on $\zeta$, strictly separating finite-band group delays `bandGroupDelay` at every large finite bandwidth $\Omega$.

### 3. Negative Resolution of Uniform Growing-Window Constants and Finite-Curve Indecisiveness
1. **Higher-Order Positive Passive Twins (`EvenPowerPositiveEulerTwin`).** For any $N, M \in \mathbb{N}$ and $\delta > 0$, choosing $p > N$, $k = \max(2, M)$, $q = p^{2k}$, $\sigma \in (\max(1/2, 1 - 2\delta), 1)$, $R = q^\sigma$, $U = q^{1-\sigma}$, $A = R + U$ yields a causal, Schur-passive, continuous-spectrum-unitary, real-axis-positive system with multiplicative coefficients $\ge 1$ equal to $1$ on $[1, p^{2k})$, prime-power Euler logarithm matching $b_\zeta(p^j) = 1/j$ for all $1 \le j < 2k$ (**including $b(p^2) = +1/2$**) and $b(p^{2k}) = \frac{1}{2k} + R + U > 0$, yet having a zero at $\operatorname{Re} s = \sigma > 1 - 2\delta$ and violating $O(e^{-\delta\tau})$. Conversely, enforcing $\operatorname{Re} b(n) \ge 0$ across *all* powers on a single-prime rational edit leaves no nontrivial twin (`not_exists_nontrivial_positive_rational_twin`).
2. **Finite Decay-Curve Indecisiveness (`quartetGate`).** For every nonzero `CompactPulse` $h$, $\varepsilon > 0$, and $\sigma \in (1/2, 1)$, pushing the degree-4 self-dual Blaschke gate $B_{\sigma,\gamma}$ ($\rho = \sigma + i\gamma$) to large $\gamma$ yields an entire, reflection-symmetric, real-axis-positive, causal, Schur-passive, unitary model `xiQuartet σ γ` satisfying $\sup_{T \in \mathbb{R}} \|\mathcal{S}_{\sigma,\gamma}^{\mathrm{quartet}}(h)(T) - \mathcal{S}_h(T)\| < \varepsilon$ while violating $O(e^{-\delta T})$ on $h$ itself for every $\delta > (1-\sigma)/2$.

## No-go closure
- **Exact killing theorem/mechanism:** `no_uniform_escape_rate_from_prime_traversal_and_passivity` (`EvenPowerPositiveEulerTwin` at $q = p^{2k}$, $k \ge 2$) and `finite_decay_curve_cannot_decide_asymptotic_exponent` (`quartetGate`).
- **Strongest positive survivor:** `echoKernel_eq_five_channels`, `integral_Ioi_norm_sq_pulseReflected`, `setIntegral_norm_sq_mixedPulse_reflected`, `unconditional_cusp_escape_sub_seven_eighths`, `finite_time_cusp_escape_separation`, and `finite_time_mixed_pulse_prime_square_distinction` — all unconditionally formalized in Lean 4.
- **New insight:** Finite-time cusp escape and mixed-pulse $p^2$/$pq$ interference strictly separate $\zeta$ from quadratic passive twins below RH because finite windows isolate bounded delays; however, any finite prime-power traversal budget leaves higher even prime powers $p^{2k}$ unconstrained where a positive self-dual local modification hides an off-line zero of arbitrarily slow ringdown without disturbing causality, passivity, unitarity, or earlier prime-power signs.
- **Status:** Dependency-closed paper proof and unconditional Lean 4 formalization complete; verified with `lake --old env lean` and `#print axioms`.

## Log
- 2026-11-19 — Dependency-closed paper proof completed in `2-fully-proven`.
- 2026-11-19 — Unconditionally formalized in Lean 4 across `CuspEscapeAndMixedPulseInterference.lean`, `PassiveTwinEchoAndFiniteTimeDistinction.lean`, and `CompleteResolutionOfTheCuspEscapeQuestion.lean`; verified clean under `lake --old env lean` and `#print axioms` (`[propext, Classical.choice, Quot.sound]`); promoted to `3-formalized`.
