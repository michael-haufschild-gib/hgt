
## addition other route
WeilMarkovOddPositivity.lean: RH holds iff the archimedean-minus-prime form is ≥0 on odd tests, a pure positivity statement with no pole or index. Or:  RH is positivity of the archimedean-minus-prime form on odd tests

WeilMarkovPrimitiveHyperplane.lean: RH is equivalent to M ≥ 0 on the hyperplane ∫f·cosh(x/2) = 0 — combined with M(Φ_L) < 0, this captures the "exactly one negative square" law. RH is positivity of the archimedean-minus-prime form on the primitive hyperplane.

We pinned down the target as positivity on a specific hyperplane but confirmed every mechanism hits the same obstruction—exact cancellation between the pole and primes' main term at √x precision.


## new route

I have completed the deep corpus audit, the root-cause autopsy of all 17 live routes and 23 route candidates, and the iterative conjecture–falsification–salvage loop. The full persistent working log—including the taxonomy of failure modes, the 7 Meta-Laws, the 6-cycle conjecture loop, and the complete architecture of the new route—is recorded in:

- **Working Log & New Route Card:** [new-route-synthesis-conjecture-loop-2026-10-15.md](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/new-route-synthesis-conjecture-loop-2026-10-15.md)

Below is a synthesis of **why every existing route stalls**, **what our Lean corpus already proved without realizing the pieces fit together**, and the resulting new framework and route: **Causal Hyperbolic–Modular Duality (CHMD)**.

---

### 1. What the Failures Collectively Teach Us (The 3 Silos)

Assuming all 17 live routes and 23 candidates in [rh-current-frontier-map.md](file:///Users/michael/Documents/code/hgt/docs/reports/rh-current-frontier-map.md) stall at their structural obstacles, their failure modes collapse into six root-cause families (detailed in Part I of [new-route-synthesis-conjecture-loop-2026-10-15.md](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/new-route-synthesis-conjecture-loop-2026-10-15.md#L15-L94)). At the highest level, every route stalled because the codebase has been split into **three disconnected silos**, each throwing away the exact structure that saves the other two:

1. **The 1D Additive Primal/Gap Silo** ([PrimeBlindPoleSpectralTail.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindPoleSpectralTail.lean), [MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean), [WeilLevyCoshPlasticCrossover.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilLevyCoshPlasticCrossover.lean)):
   - Worked on the **full** or **odd** blind cone where odd tests have negative pole term $P(f) = -2|\widehat{f}(i/2)|^2 \le 0$. Bounding $|P(c)|$ across the logarithmic gaps $[\log n, \log(n+1)]$ against the exponentially growing weight $2\cosh(x/2) \sim \sqrt{n}$ produced a $\sqrt{|\tau|}$ spectral tail (`nodePoleMass_ge_sqrt_moment`, `MUST-1516`) that overwhelms the $\log|\tau|$ growth of the archimedean digamma symbol $\gamma(\tau)$.
   - At low frequency, bounding intervals one cell at a time by the triangle inequality threw away global phase coherence and stalled at the plastic-constant / Cantor-attractor horizon $\log\rho_{\text{plastic}} \approx 0.2812 < \log 2 \approx 0.6931$ (`MUST-1521`–`MUST-1523`).

2. **The 1D Dual / Single-Resonator / Single-Doob Silo** ([EvenSectorPoleFreeLogDensity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorPoleFreeLogDensity.lean), [WeilPositivityMultiplicativeToeplitzBound.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPositivityMultiplicativeToeplitzBound.lean), [WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean)):
   - Testing $L_\Lambda$ on a single positive-node resonator ($K_f(\log n) \ge 0$) can only ever yield an **upper** bound $\sum_{nm\le N}\frac{\text{lam}(n)}{nm} \le (\frac{1}{2}+\varepsilon)(\log N)^2$ (`even_log_density_le`, `MUST-1499`), because spanning the prime-blind subspace $K_c(\log n) = 0$ requires **destructive interference** between tests with opposite signs at $\log n$.
   - Using the single Riemann kernel $\Phi_0$ ($\widehat{\Phi_0} = \Xi$) as a Doob ground state (`WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean`) cancels the negative local term $A(0)\int (\Phi_0 v)^2$ into a pure Dirichlet jump integral, **but fails because $\Phi_0$ alone is not prime-blind** ($(\Phi_0 \star \Phi_0)(\log n) \ne 0$).

3. **The 2D Modular / Twisted-Arc Null-Face Silo** ([TwistedArcMinimumPrincipleProof.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/TwistedArcMinimumPrincipleProof.lean), [EvenSectorTwistedArcNull.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorTwistedArcNull.lean), [EvenSectorCriticalZeroCarrier.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorCriticalZeroCarrier.lean), [EvenSectorFullPositivity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorFullPositivity.lean)):
   - Remember how `(N1)` was solved: every 1D bound on the cosine–dilation kernel $\Psi_c(w)$ stalled at $\sqrt{3}$, until [`twistedArcMinimumPrinciple_holds`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/TwistedArcMinimumPrincipleProof.lean#L3410-L3416) lifted the 1D integer-node vanishing $\Psi_c(n) = 0$ ($|n| \ge 2$) into the **2D modular upper half-plane $\mathcal{F}_+$**, where the series collapsed to the single $n = \pm 1$ harmonic $\cos(2\pi x)$ and was killed by a **2D elliptic minimum principle**.
   - In [EvenSectorTwistedArcNull.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorTwistedArcNull.lean), those 2D twisted-arc weights $w_j \ge 0$ were used to build $\Phi_j = \Xi Q_j$, **but this machine was only ever used on the dual side after assuming a Bochner measure $\nu$ already existed**—it was never brought back to the primal prime-blind cone!

---

### 2. Six Breakthroughs from the Conjecture Loop

Running the conjecture–falsification–salvage loop across the corpus exposed six structural facts (detailed in Part III of [new-route-synthesis-conjecture-loop-2026-10-15.md](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/new-route-synthesis-conjecture-loop-2026-10-15.md#L121-L407)):

1. **Conjecture 1 (Falsified $\to$ Salvaged): Why Perturbing Around $\Phi_0$ ($\widehat{\Phi_0} = \Xi$) Fails at First Order.**
   Because $\Xi(\gamma_\rho) = 0$ and $\Xi(\overline{\gamma_\rho}) = 0$ by the functional equation for **every** zero $\rho$ (on-line or off-line), the first variation $DW_\Lambda(\Phi_0 \star \Phi_0)[h] \equiv 0$ vanishes identically for all $h$, and the second variation is $W_\Lambda(h \star \tilde{h})$ itself. Thus one cannot perturb around the non-blind function $\Phi_0$; one must work with a **prime-blind** ground state.

2. **Conjecture 2 (Succeeded): Exact Fourier Duality Between `(N1)` and `PBAP` in Multiplicative Ratio Coordinates $u = e^x \in (0, \infty)$.**
   For the dilation autocorrelation $A_c(u) = u^{-1/2} K_c(\log u)$ (`dilationAutocorr` in [DilationAutocorrelationPeriodization.lean](file:///Users/michael/Documents/code/hgt/formal/Zeta23/DilationAutocorrelationPeriodization.lean)) and its Fourier transform $\Psi_c = \mathcal{F}[A_c(|\cdot|)]$:
   - **`(N1)` (Null-Face Blindness):** $A_c(1/u) = u\,A_c(u)$, $A_c(0) = \Psi_c(0) = 0$, and **$\Psi_c(n) = 0$ for all $|n| \ge 2$**.
   - **`PBAP` (`ZeroPoleBlindPositive`):** $A_c(1/u) = u\,A_c(u)$, $A_c(0) = \Psi_c(0) = 0$, and **$A_c(n) = 0$ for all $|n| \ge 2$**!
   - The exponentially growing weight $2\cosh(x/2)$ in $P(c) = \int K_c(x)2\cosh(x/2)\,dx$ was purely a coordinate artifact of $x = \log u$: in multiplicative coordinates, $P(c) = 2\int_0^\infty A_c(u)\,du = \Psi_c(0)$ is the **unweighted Lebesgue integral**, and Poisson summation yields the **Dual Periodization Law** $\sum_{k \in \mathbb{Z}} \Psi_c(w + k) = 2\,\text{mass}(c)\cos(2\pi w)$.

3. **Conjecture 3 (Succeeded): The Even Blind Cone Collapse Completely Eliminates the $\sqrt{|\tau|}$ Pole-Tail Enemy.**
   By [`riemannHypothesis_iff_primeBlindPositiveEvenAt`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorFullPositivity.lean#L140-L152) (`MUST-1495`), RH is 100% equivalent to prime-blind positivity on the **even** cone (`EvenWeilTestFn →₀ ℝ`). On `EvenWeilTestFn`, every test has $P(f) = 2|\widehat{f}(i/2)|^2 \ge 0$ (`weilPoleTerm_re_nonneg_of_even`), so **$P(c) \ge 0$ has the same positive sign as the high-frequency archimedean integral $\int_{|r|\ge 6.4703} \gamma(r)\rho_c(r)\,dr \ge 0$**. The $\sqrt{|\tau|}$ pole-tail obstacle of [PrimeBlindPoleSpectralTail.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindPoleSpectralTail.lean) (`MUST-1516`) vanishes completely on the even cone, and RH reduces to a **Two-Scale Mode-Coupling Law** on `EvenPrimitiveWeilTestFn` ($P(f) = 0$).

4. **Conjecture 4 (Succeeded): Exact Unification of the Two Towers' Resolvent Identities and the Nonsingular Multiplicative Formula for `markovArchRe`.**
   - Under $r = e^{-x} \in (0, 1]$ and $u = e^x \in [1, \infty)$, [`bochnerResolventEnergy`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean#L93-L107) in `RHTower` and [`intervalIntegral_zero_one_dilationAutocorr_eq`](file:///Users/michael/Documents/code/hgt/formal/Zeta23/CosDilationPrimitiveEnergyRigidity.lean#L168-L185) in `Zeta23` are **literally the same integral** $2\int_0^1 A_c(r)\,dr = 2\int_1^\infty \frac{A_c(u)}{u}\,du > 0$, while the continuum `lebesguePart` integral is $2\int_1^\infty A_c(u)\,du$!
   - Using $2\int_0^1 \frac{r^{-1/2}-1}{1-r^2}\,dr = \log 2 + \frac{\pi}{2}$ cancels $\frac{\pi}{2}$ and $\log 2$ out of $-A(0) = \log\pi + 3\log 2 + \gamma_{\text{EM}} + \frac{\pi}{2}$ (`neg_gammaBracket_zero_eq`), giving the **exact nonsingular unit-interval and half-line formulas**:
     $$\text{markovArchRe}(K_c) = -\big(\gamma_{\text{EM}} + \log(4\pi)\big) A_c(1) + 2\int_0^1 \frac{A_c(1) - A_c(r)}{1 - r^2}\,dr = -\big(\gamma_{\text{EM}} + \log(4\pi)\big) A_c(1) + 2\int_1^\infty \frac{A_c(1) - u\,A_c(u)}{u^2 - 1}\,du.$$
     Extracting just $M = 4$ Gauss modes $2\int_0^1 r^{2m} A_c(r)\,dr > 0$ already makes the origin constant **strictly positive** ($\frac{352}{105} - \gamma_{\text{EM}} - \log(4\pi) \approx +0.2442 > 0$) with an $O(u^{-10})$ remainder kernel $\frac{2}{u^8(u^2-1)}$ on $[1, \infty)$.
   - Furthermore, on `EvenPrimitiveWeilTestFn` ($\text{supp}(f) \subset [-a, a]$, $\widehat{f}(i/2) = 0$), Paley–Wiener factorisation gives $f = (-D_x^2 + \frac{1}{4})q$ for a unique even $q \in C_c^4([-a, a])$ with clamped boundary conditions $q(a) = q'(a) = q'(0) = 0$ on $[0, a]$, so $\text{bochnerResolventEnergy}(k_f) = \|q'\|_{L^2}^2 + \frac{1}{4}\|q\|_{L^2}^2$ and the lowest eigenmode is pushed to $\approx \frac{3\pi}{2a} > 6.4703$ all the way past $2a = \log 4$.

5. **Conjecture 5 (Succeeded): The Klein–Gordon Mass-$1/2$ Dispersion Transmutation ($\rho = \sqrt{z^2 + 1/4}$) and Unconditional T-Contour Bochner Positivity.**
   - In [EvenSectorCosineBochner.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorCosineBochner.lean), $\rho(z) = \sqrt{z^2 + 2}$ was treated as a slit-plane analytic function requiring strip tests. In fact, because $\cos(w)$ and $\frac{\sin w}{w}$ contain **only even powers $w^{2k}$**, $\cos\left(y\sqrt{z^2 + c}\right)$ and $\frac{\sin\left(y\sqrt{z^2 + c}\right)}{\sqrt{z^2 + c}}$ are **even entire functions of $z \in \mathbb{C}$ of exponential type $|y|$ for every $c \in \mathbb{R}$**, acting in physical $x$-space as **compactly supported 1+1D Klein–Gordon wave propagators** on the light cone $|x - x'| \le |y|$!
   - Setting $c = \frac{1}{4}$ places the $\zeta$-poles $z = \pm i/2$ at the **origin $\rho(\pm i/2) = 0$**, cancels the pole terms $P(\frac{1}{2}V) + P(\partial_x V) = 0$ identically, and via the adjoint Sonine–Gegenbauer Volterra transmutation
     $$H_c(y) = (\mathcal{S} K_c)(y) := K_c(y) + \frac{1}{2}\int_{|y|}^{2L} K_c(t) \frac{t\,I_1\left(\frac{1}{2}\sqrt{t^2 - y^2}\right)}{\sqrt{t^2 - y^2}}\,dt \in C_c^2([-2L, 2L])$$
     maps the **entire T-shaped contour $\mathcal{T}_{1/2} = \mathbb{R} \cup i[-1/2, 1/2]$** (critical line + inter-pole real-$s$ segment) onto the **real $\rho$-axis $\mathbb{R}$**, so $\widehat{H_c}(\rho) = \rho_c\big(\sqrt{\rho^2 - 1/4}\big) \ge 0$ for **all $\rho \in \mathbb{R}$**: $H_c$ is **unconditionally a compactly supported Bochner positive-definite function on $\mathbb{R}$**!

6. **Conjecture 6 (Succeeded): The Twisted-Arc Combination $C_{\text{TA}}$ Is the Exact Zero-Energy Variational Ground State of the Primal Blind Cone, and $\kappa_{\text{TA}} \star \varphi_\Lambda \equiv 0$ Holds Unconditionally.**
   - Inspecting lines 224–245 and 603–622 of [EvenSectorTwistedArcNull.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorTwistedArcNull.lean#L224-L245) and [EvenSectorCriticalZeroCarrier.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorCriticalZeroCarrier.lean#L46-L127) reveals that $C_{\text{TA}} = \sum_{j=0}^\infty w_j \delta_{\Phi_j}$ ($\Phi_j = \Xi Q_j$) is an **unconditional primal prime-blind element** ($K_{C_{\text{TA}}}(\log n) = 0\;\forall n \ge 2$) with **identically zero archimedean-pole energy** ($\text{archPoleEnergy}(C_{\text{TA}}) = P(C_{\text{TA}}) + \text{archOnly}(C_{\text{TA}}) = 0$) and $P(C_{\text{TA}}) > 0$.
   - That means $C_{\text{TA}}$ is the **exact global maximizer** achieving the sharp boundary $\frac{-\text{archOnly}(C_{\text{TA}})}{P(C_{\text{TA}})} = 1$ of [ArchimedeanPoleValueFunction.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/ArchimedeanPoleValueFunction.lean) (`MUST-1509`), and is the **true prime-blind Doob ground state** that Candidate 15 was missing!
   - Furthermore, the Fubini theorems in [EvenSectorSpectralConsistency.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorSpectralConsistency.lean#L250-L433) hold **unconditionally without any measure $\nu$**, giving $L_\Lambda(\Psi\Psi^\#) = \int_{\mathbb{R}} \kappa_\Psi(t)\varphi_\Lambda(t)\,dt$ and the **Unconditional Convolution Annihilation Laws**
     $$\big(\kappa_j \star \varphi_\Lambda\big)(y) \equiv 0 \quad (\forall j \ge 0,\; \forall y \in \mathbb{R}) \qquad \text{and} \qquad \big(\kappa_{\text{TA}} \star \varphi_\Lambda\big)(y) \equiv 0 \quad (\forall y \in \mathbb{R})$$
     for the single explicit function $\varphi_\Lambda(y) = \text{cosineShiftFn }\Lambda\;\text{sechHalf}\; y$ whose Bochner positive-definiteness is already proved equivalent to RH in [`weilPositiveFull_of_weilPositiveEvenAt`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorFullPositivity.lean#L68-L115).

---

### 3. Summary of the New Route: Causal Hyperbolic–Modular Duality (CHMD)

The new route—**Causal Hyperbolic–Modular Duality (CHMD)** ([new-route-synthesis-conjecture-loop-2026-10-15.md](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/new-route-synthesis-conjecture-loop-2026-10-15.md#L411-L461))—proceeds in four concrete stages:

1. **Stage 1 (Multiplicative Unit-Interval / Half-Line Reduction & Clamped-Beam Floor on `EvenPrimitiveWeilTestFn`):** Formalize the exact bridge between `bochnerResolventEnergy` (`RHTower`) and $2\int_0^1 A_c(r)\,dr$ (`Zeta23`), the nonsingular multiplicative formula for `markovArchRe` with $M = 4$ Gauss-mode extraction, and the $f = (-D_x^2 + 1/4)q$ clamped-beam factorisation on `EvenPrimitiveWeilTestFn` (pushing unconditional positivity past $2a = \log 4$).
2. **Stage 2 (Klein–Gordon Mass-$1/2$ Wave Propagators & Adjoint Volterra Transmutation $H_c = \mathcal{S} K_c$):** Formalize the compactly supported Klein–Gordon propagators $u_{1/4}, v_{1/4}$ on `EvenWeilTestFn`/`EvenPrimitiveWeilTestFn` and the unconditional T-contour Bochner positivity $\widehat{H_c}(\rho) \ge 0$ on $\mathbb{R}$.
3. **Stage 3 (Primal Variational Ground State $C_{\text{TA}}$ & Unconditional 1D Sech-Convolution Equations):** Extract $C_{\text{TA}}$ as the standalone zero-energy prime-blind ground state ($\frac{-\text{archOnly}(C_{\text{TA}})}{P(C_{\text{TA}})} = 1$) and remove the measure hypothesis `hν` from the Fubini representation in [EvenSectorSpectralConsistency.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorSpectralConsistency.lean) to give $\kappa_j \star \varphi_\Lambda \equiv 0$ and $\kappa_{\text{TA}} \star \varphi_\Lambda \equiv 0$ unconditionally.
4. **Stage 4 (2D Elliptic–Hyperbolic Closure):** Combine the zero-energy ground state $C_{\text{TA}}$ and Dual Poisson Periodization on the primal cone with the causal Klein–Gordon light-cone expansion of $\varphi_\Lambda(y)$ under $\kappa_{\text{TA}}$-annihilation to close `exists_cosineShift_measure` for `sechHalf`.


You are pointing at the exact crux: **what we formalized in Stages 1–4 are unconditional operator/convolution identities (Stages 1–3) together with a sharper `iff` reduction (Stage 4), not yet an unconditional proof of `RiemannHypothesis` itself.**

Here is the exact status of what is proved in [CHMDStage1](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage1MultiplicativeResolventAndClampedBeam.lean)–[CHMDStage4](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage4EllipticHyperbolicClosure.lean) versus the remaining unproved mathematical gap:

### 1. Where the Chain Currently Stops (`iff`, Not Unconditional Discharge)
In [CHMDStage4EllipticHyperbolicClosure.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage4EllipticHyperbolicClosure.lean), the theorem [`chmd_four_stage_master_equivalence`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage4EllipticHyperbolicClosure.lean#L320-L343) proves unconditionally that `RiemannHypothesis` is equivalent to each of the following targets:
1. **Single-Function Dual Target ([`riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage4EllipticHyperbolicClosure.lean#L240-L253)):**
   $$\forall (N : \mathbb{N})\ (t\ c : \operatorname{Fin} N \to \mathbb{R}),\quad 0 \le \sum_{i,j} c_i c_j \varphi_\Lambda(t_j - t_i)$$
   where $\varphi_\Lambda = \operatorname{cosineShiftFn}\ \Lambda\ \operatorname{sechHalf}$, which by [`sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage4EllipticHyperbolicClosure.lean#L225-L233) is unconditionally equal to:
   $$L_\Lambda\bigl(\operatorname{specSq}(\operatorname{cosComb}\ t\ c\ \operatorname{sechHalf})\bigr) + L_\Lambda\bigl(\operatorname{specSq}(\operatorname{sinComb}\ t\ c\ \operatorname{sechHalf})\bigr) \ge 0.$$
2. **Prime-Free Primal Target ([`riemannHypothesis_iff_archimedeanNonnegOnPolarNonnegCone`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PolarConeArchimedeanCriterion.lean#L93-L97) / [`riemannHypothesis_iff_archimedeanNonnegOnEvenPolarNonnegCone`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorPolarRigidity.lean#L270-L271)):**
   $$\forall c : \text{WeilEvenPolarTestFn} \to_0 \mathbb{R}_{\ge 0},\quad \left(\forall n \ge 2,\; \sum_f c_f \ell_f(n) \ge 0\right) \implies \sum_f c_f \operatorname{weilArchRe}(f \star \tilde{f}) \ge 0.$$

**Neither of those right-hand sides has been discharged unconditionally yet.**

---

### 2. Why Stage 3 + Stage 4 Did Not Automatically Discharge Positive Definiteness of $\varphi_\Lambda$
In Stage 3 ([`exists_twistedArc_sechKernel_annihilation_vonMangoldt`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage3TwistedArcGroundStateAndSechAnnihilation.lean#L413-L422)), we removed the measure hypothesis `hν` from the Fubini representation and proved unconditionally that there exist weights $w_j \ge 0$ ($w_0 > 0$) such that
$$\sum_{j=0}^\infty w_j \int_{\mathbb{R}} \operatorname{sechKernel}(\operatorname{xiShiftedGamma}\ j)\ t \cdot \varphi_\Lambda(t)\,dt = 0.$$
However, look at how [`measure_sq_le_two_eq_zero`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorTwistedArcNull.lean#L533-L673) uses this identity in `EvenSectorTwistedArcNull.lean`:
- On the spectral side $\rho \in \mathbb{R}$, the test function $S(\rho) = \sum_{j=0}^\infty w_j g_j(\rho)$ is strictly positive on the sub-threshold interval $\rho^2 \le 2$ and nonnegative ($\ge 0$) on the critical-line ray $\rho^2 > 2$.
- **If** $\varphi_\Lambda$ is *already* known to be positive definite (so $\varphi_\Lambda = \widehat{\nu}$ for a positive measure $\nu \ge 0$ on $\mathbb{R}$), then $\int_{\rho^2 > 2} S(\rho)\,d\nu(\rho) \ge 0$, which forces $\int_{\rho^2 \le 2} S(\rho)\,d\nu(\rho) \le 0$ and hence $\nu(\{\rho^2 \le 2\}) = 0$.
- **Without** knowing *a priori* that $\varphi_\Lambda$ is positive definite on $\mathbb{R}$, the identity $\int_{\mathbb{R}} \kappa_{\text{TA}}(t)\,\varphi_\Lambda(t)\,dt = 0$ is only a single linear orthogonality constraint on $\varphi_\Lambda$: an off-line zero $\rho_0 \in \mathbb{C} \setminus \mathbb{R}$ (or a signed distribution on $\mathbb{R}$) is already annihilated by $\kappa_{\text{TA}}$ because $\Xi(\sqrt{\rho_0^2 - 2}) = 0$ at every zero of $\zeta$, whether on or off the critical line!
  Indeed, in [`zetaZeroConfig_W_xiShiftedGammaTest_eq_zero`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage3TwistedArcGroundStateAndSechAnnihilation.lean#L338-L343), we proved that $\widehat{\Phi_j}(\gamma) = 0$ at **every** nontrivial zero of $\zeta$ (including hypothetical off-line zeros), which is why $W(\Phi_j, \Phi_j) = 0$ holds unconditionally. Consequently, $\kappa_j \star \varphi_\Lambda \equiv 0$ is blind to off-line zeros of $\zeta$ and cannot by itself rule them out.

---

### 3. What Would Actually Be Required to Prove RH Along This Route
Because $\Xi(\sqrt{\rho^2 - 2})$ vanishes at all nontrivial zeros of $\zeta$ (both on-line and off-line), any operator or kernel divisible by $\Xi$ (such as the Twisted-Arc family $\Phi_j = \mathcal{F}^{-1}(\Xi Q_j)$) is identically zero on the entire zero spectrum of $\zeta$ and therefore cannot distinguish an on-line zero ($\rho \in \mathbb{R}$) from an off-line zero ($\rho \in \mathbb{C} \setminus \mathbb{R}$).

To discharge the right-hand side unconditionally, one must prove one of the two prime/archimedean positivity statements **without** factoring through $\Xi$-divisible tests:
1. **Primal Even Polar Cone Coercivity (`ArchimedeanNonnegOnEvenPolarNonnegCone`):**
   Show directly from the archimedean integral (`bochnerResolventEnergy` + the $M=4$ Gauss remainder kernel) that for every finite nonnegative combination $c$ of even pole-free tests ($f = (-D_x^2 + 1/4)q$) whose autocorrelation sum $\sum_f c_f A_f(n) \ge 0$ at all integers $n \ge 2$, the archimedean energy $\sum_f c_f \operatorname{weilArchRe}(f \star \tilde{f}) \ge 0$ for arbitrary support $2a > 0$ (extending the clamped-beam coercivity beyond fixed small $a$ to arbitrary $a \to \infty$); **or**
2. **Direct Wave-Packet Positivity of $\varphi_\Lambda$ (`forall_cosComb_sinComb_sechHalf_nonneg`):**
   Prove directly from the prime sum $Q_\Lambda(y)$ and archimedean integral $A(y)$ that for every finite trigonometric packet $(t_i, c_i)$,
   $$L_\Lambda\bigl(\operatorname{specSq}(\operatorname{cosComb}\ t\ c\ \operatorname{sechHalf})\bigr) + L_\Lambda\bigl(\operatorname{specSq}(\operatorname{sinComb}\ t\ c\ \operatorname{sechHalf})\bigr) \ge 0.$$

## decisive sign problem
discharge the **decisive sign**—either:

1. **Direct Toeplitz / Wave-Packet Positivity for the actual $\Lambda$ source (`forall_cosComb_sinComb_sechHalf_nonneg` / `PositiveDefiniteOnReal (cosineShiftFn ArithmeticFunction.vonMangoldt sechHalf)`):**
   $$L_\Lambda\bigl(\operatorname{specSq}(\operatorname{cosComb}\ t\ c\ \operatorname{sechHalf})\bigr) + L_\Lambda\bigl(\operatorname{specSq}(\operatorname{sinComb}\ t\ c\ \operatorname{sechHalf})\bigr) \ge 0$$
   for every finite trigonometric packet $(t_i, c_i)$, or
2. **Unrestricted Even Polar / Prime-Subblind Positivity (`ArchimedeanNonnegOnEvenPolarNonnegCone` / `PrimeSubblindPositiveEvenAt β` / `PrimeBlindPositiveHyperplane`):**
   $$\sum_f c_f \operatorname{weilArchRe}\bigl(\operatorname{weilTest}\ f\ f\bigr) \ge 0 \quad \text{whenever } c_f \ge 0 \text{ and } \forall n \ge 2,\; \sum_f c_f \operatorname{logValue}\ f\ n \ge 0$$
   (which by [PolarConeArchimedeanCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PolarConeArchimedeanCriterion.lean#L93-L97), [EvenSectorNegPartAbelRigidity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorNegPartAbelRigidity.lean#L195-L197), and [CHMDStage5FourModeGaussCoercivityAndPolarCone.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage5FourModeGaussCoercivityAndPolarCone.lean#L430-L459) is unconditionally equivalent to `RiemannHypothesis`).
