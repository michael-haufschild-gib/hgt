# Hard Obstacles to an Unconditional Lean Proof of the Riemann Hypothesis (18 Oct 2026)

## Executive Diagnostic: Why Existing Mathematics and Our Two New Lean Frameworks Have Not Yet Closed RH

Our Lean 4 codebase has built an extensive network of unconditional receiver bridges (`riemannHypothesis_iff_...` and `riemannHypothesis_of_...`) across **27 Live Routes** and **18 Route Candidates** ([rh-current-frontier-map.md](file:///Users/michael/Documents/code/hgt/docs/reports/rh-current-frontier-map.md)), catalogued **15 structural Walls** ([walls-ledger.md](file:///Users/michael/Documents/code/hgt/docs/reports/walls-ledger.md)), and developed two new mathematical frameworks in Lean:
1. **Bi-Scale Uncertainty (`BSU`)** ([formal/GaloisForLFunctions/BiScaleUncertainty/README.md](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/README.md), [BiScaleUncertainty.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty.lean) — 458 Lean modules).
2. **Bézout–Valuation Incidence (`BVI`)** ([formal/GaloisForLFunctions/BezoutValuationIncidence/README.md](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/README.md), [BezoutValuationIncidence.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence.lean) — 40 Lean modules).

Yet **not a single wall has been removed end-to-end**, and **every unconditional producer theorem has stopped one step short of the receiver gate**. Before examining each of the 15 walls, 27 live routes, and 18 candidates individually, it is essential to understand why the two new frameworks—despite solving major local bottlenecks—failed to cross the final threshold:

### 1. Why `BiScaleUncertainty` (458 Modules) Failed to Close `RW`, `EWU`, `OWU`, `HF`, `WL`, and `CHMD`
`BiScaleUncertainty` successfully eliminated several technical blockers that previously looked fatal:
- It replaced non-compact $H^1$ derivative collars with derivative-free Krein collar transport ([KreinCollarTransport.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/KreinCollarTransport.lean)).
- It bypassed the $4\log 2 / 5 < \log 2$ non-dyadic interpolation trap via folded collar interpolation ([FoldedCollarResolution.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/FoldedCollarResolution.lean)).
- It reduced origin-budget telescoping to $O(n^{-3/2})$ via $\varpi_n = \sqrt{2}n(n^{-1/2} - (n+1)^{-1/2})$ ([OriginBudgetConcentration.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/OriginBudgetConcentration.lean)).
- It built explicit factorial-grid Müntz-ramp prime-blind profiles and canonical polar repairs ([FactorialMuntzCompletion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzCompletion.lean), [FactorialMuntzAnalyticRepair.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzAnalyticRepair.lean)).

**Why it still hit a hard mathematical barrier:**
1. **Single-Autocorrelation Exclusion ([FactorialBiNullObstruction.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/FactorialBiNullObstruction.lean), [CausalTentBochnerDecomp.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/CausalTentBochnerDecomp.lean), Wall 13):** Any profile $F$ that vanishes on the factorial prime grid while killing the origin ($F(0)=0$) and retaining top support value $F(T)\ne 0$ violates the Bochner inequality $|F(T)| \le F(0)$. Thus the causal-tent and factorial-Müntz profiles are **differences** $R_1 - R_2$ of two positive-definite autocorrelations. Each half has individual Weil energy $\Theta(\sqrt{N}) \to +\infty$, so the small difference $O(\log N/\sqrt{N})$ does not orient either autocorrelation or arbitrary test functions.
2. **Scale Separation of the Polar Loss ([FactorialPolarGramScaleSeparation.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/FactorialPolarGramScaleSeparation.lean)):** On the two-ray span of the factorial Müntz ramp and causal tent, the positive polar loss $2|\widehat{F}(i/2)|^2$ scales as $\frac{1}{4}\frac{\log(n+2)}{n+1}$, whereas the mixed Gram interaction is $o(1/(n+1))$. Thus $2\times 2$ Gram determinant decoupling (`A ≥ M²/(4D)`) fails asymptotically because the negative pole term dominates the off-diagonal coupling by a factor of $\log n$.
3. **Unconditional RH-Nonselectivity of Repaired Factorial Tails ([FactorialMuntzTailWeilGrowth.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailWeilGrowth.lean)):** When the pole is killed by the canonical polar repair (`factorialMuntzSmoothedTail`), the resulting profile has **strictly positive zero-side energy** and unconditional complete Weil energy $\ge \frac{\log(n+1)}{2048(n+1)} > 0$ (`factorialMuntzSmoothedTail_weil_log_rate`, `factorialMuntzSmoothedTail_weil_eventually_pos`) **whether RH is true or false**. Why? Because the archimedean logarithmic energy grows as $\frac{1}{2}\log(n+1)\|F\|_2^2$ while off-line zero readouts decay as $O((n+1)^{-1/2})$ relative to the tail mass $\Theta((n+1)^{-1})$. The repaired family is dominated by high-frequency archimedean energy and cannot detect off-line zeros!
4. **Origin-Defect and Polar-Escape Obstructions ([InfiniteGridStrictEnergyLoss.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/InfiniteGridStrictEnergyLoss.lean), [DistantCopySharpness.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/DistantCopySharpness.lean), [NyquistPolarSourceEscape.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/NyquistPolarSourceEscape.lean)):** Smooth all-grid-blind sources can converge strongly in $L^2$ and uniformly in autocorrelation while strictly losing positive Lévy energy at the origin ($t=0$ concentration), and polar-balanced distant copies can converge to nonpolar limits.
5. **Shift-Gauge Blindness ([EvenSectorBlindGroundShiftInvariance.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/EvenSectorBlindGroundShiftInvariance.lean)):** Subtracting $m(a)\|Ju\|^2$ cancels any constant shift $C$ of the ground operator identically on the form domain, making the de Branges / Farkas ground-state identity blind to the sign of $m(a)$.

### 2. Why `BezoutValuationIncidence` (40 Modules) Failed to Close `MC`, `CTF`, `PM (FZZ-P)`, and `BVI`
`BezoutValuationIncidence` was engineered specifically to bypass the four classic traps of Wall 1 and Wall 11:
- Unlike pure multiplicative convolution, the successor shift $k \mapsto k+1$ satisfies $\gcd(k, k+1) = 1$, which **fails for generic Beurling generalized number systems** (`beurling_countermodel_breaks_successor_coprimality` in [PronicWindowCeilingAndBeurlingDiscrimination.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PronicWindowCeilingAndBeurlingDiscrimination.lean)).
- It operates at a single character (modulus $1$, shift $0$) without Dirichlet family averaging.
- It reaches the pronic ceiling $M(M+1) > M^2$ ($\theta = 2 > 1$), exceeding the $\theta = 1$ Fouvry–Iwaniec / Bombieri–Friedlander–Iwaniec barrier.
- It breaks the totient degeneracy $\varphi(4) = \varphi(6) = 2$ of Wall 11 via the Bézout eigenvalue $\varphi(e) - \mu(e)$, which takes value $2$ at $e=4$ and $1$ at $e=6$ (`wall11_totient_degeneracy_broken_by_bezout` in [RamanujanRestorationAndBezoutDiagonal.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/RamanujanRestorationAndBezoutDiagonal.lean)).

**Why it still hit a hard mathematical barrier:**
1. **Total Prime-Power Annihilation on Pronic Successor Pairs ([BezoutValuationCore.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/BezoutValuationCore.lean)):** Because $\gcd(d_1, d_2) = 1$ on any centered successor pair with $d_1, d_2 \ge 2$, the product $d_1 d_2$ has at least two distinct prime factors, so $\Lambda(d_1 d_2) = 0$ identically (`vonMangoldt_pronicSeq_eq_zero`). Pronic pairs never land on prime powers; they only see composite products.
2. **Sharpness of the Universal Two-Lag and Primitive-Energy Cones ([ExactSuccessorMomentRegionAndUniversalInequalities.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ExactSuccessorMomentRegionAndUniversalInequalities.lean), [SharpPrimitiveEnergySuccessorFrontier.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SharpPrimitiveEnergySuccessorFrontier.lean)):** Modes $\{1,2,6\}$ realize the entire universal cone $2H^2 \le Q_{\mathrm{Sel}} + Q_{\mathrm{Bez}}$ and $2Q_{\mathrm{Bez}} \le Q_{\mathrm{Sel}} + H^2$, while modes $\{2,3,4,6\}$ realize the exact primitive-energy facets $\max(5V+2C, 6V+4C, 6V+12C)/12$ (`sievePrimitiveEnergy_first_facet`, `_second_facet`, `_third_facet`). No stronger universal inequality in Selberg variance $V$, successor covariance $C$, and primitive energy exists for general sieve weights.
3. **3/4 One-Step Phase Loss & Parity-Only Closure ([OptimalSuccessorPredictionAndExactPhaseLoss.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/OptimalSuccessorPredictionAndExactPhaseLoss.lean), [SharpSuccessorPhaseLossAndClosureClassification.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SharpSuccessorPhaseLossAndClosureClassification.lean)):** The optimal divisor-sieve predictor of $k \mapsto k+1$ is the coprimality operator, which has spectrum $\mu(q)/\varphi(q)$ on Selberg coordinates (`selbergMultiplesCoord_coprimalitySuccessor`) and **loses at least $3/4$ of all variance above parity ($q \ge 3$) at every single step** (`successorPhaseLoss_bounds`). Iterating one-step prediction contracts variance by $4^{-m}$ and is NOT true $m$-step translation (`TrueTranslationPredictionAndExactCompression.lean`). Exact closure under succession holds only for weights supported on $\{1,2\}$.
4. **Visibility Horizon Explosion for Prime Powers ([ValuationVisibilityClockAndRamanujanSupport.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ValuationVisibilityClockAndRamanujanSupport.lean), [ArithmeticLagSchedulesAndSharpRecoveryHorizon.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ArithmeticLagSchedulesAndSharpRecoveryHorizon.lean)):** Under true $h$-lag translation, mode $q$ is visible if and only if its visibility clock $q/\operatorname{rad}(q)$ divides $h$ (`sieveLagMultiplier_ne_zero_iff`). Thus squarefree modes are visible at $h=1$, but prime powers $p^{a+1}$ are completely invisible until lag $h = p^a$ (`sieveLagScheduleRecovers_iff`), requiring a consecutive lag horizon of $\sup_{q \le N} q/\operatorname{rad}(q) \ge 2^{\lfloor \log_2 N\rfloor - 1} \sim N/2$.
5. **Terminal-Prime Blowup and Sub-Horizon Restriction ([PrimeTailCalibrationAndMobiusDefect.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PrimeTailCalibrationAndMobiusDefect.lean), [PowerDampedRenormalizedDefectAndPronicCeiling.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PowerDampedRenormalizedDefectAndPronicCeiling.lean)):** For literal $\mu$, the unrenormalized combined LCM+Bézout defect at $M=N$ equals $N\cdot \text{successorReserve} - 1$, which grows linearly with terminal-prime mass and beats every $N^\alpha$ ($\alpha < 1$). Subtracting $M\cdot \text{successorReserve}$ yields exact non-positivity $-\frac{1}{2}\sum(\Delta g)^2 + \frac{1}{2}(g(M+1)^2-1) \le 0$, **but only in the sub-horizon regime $M+1 \le N$** (`renormalizedCombinedDefect_nonpos`) where every integer $k \le M+1$ is sieve-complete ($g(k) = \sum_{d\mid k}\mu(d) = 0$ for $k \ge 2$).
6. **The Inactive Sawtooth Martingale Drift ([ActiveDeletedMartingaleAndShiftedEulerConvergence.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ActiveDeletedMartingaleAndShiftedEulerConvergence.lean), [ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.lean)):** To reach RH via `MC` or `CTF`, one must control the trans-horizon regime $M \gg N$ (or $N \to \infty$ with damping $\varepsilon \downarrow 0$). In that regime, active divisor squares cancel 100% against the active martingale jump, and the positive active drift converges via $\zeta(1+\varepsilon)\zeta(1+2\varepsilon)/\zeta(2+2\varepsilon)$ with rate $+1/2$. However, the **inactive centered sawtooth martingale drift** across composite integers $M > N$ with divisors $> N$ remains an uncancelled oscillatory sum whose uniform control as $\varepsilon \to 0^+$ is equivalent to RH.

---

## Part I: Detailed Analysis of the 15 Walls

Below, every wall in [walls-ledger.md](file:///Users/michael/Documents/code/hgt/docs/reports/walls-ledger.md) is analyzed with its Lean anchors, why all attempts failed so far, what makes the obstacle hard, the split between **"Just Work" (Solvable)** vs. **"Requires New Mathematics"**, and whether overcoming it can still end in a dead end.

---

### Wall 1: The Square-Root Barrier in Prime Counting
- **Statement & Lean Anchors:** $\psi(x) - x = O(x^{1/2+\varepsilon})$ (or $M(x) = O(x^{1/2+\varepsilon})$). Anchored in `RiemannHypothesis_iff_vonMangoldt_remainder`, `riemannHypothesis_of_dyadic_log_moment_bound`, `riemannHypothesis_of_subexponential_cesaro_tail`, `NyquistBandwidthRigidity`, and `Zeta23Countermodel`.
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - *Parity problem (Selberg):* Combinatorial sieves cannot distinguish integers with an even vs. odd number of prime factors, allowing zero-saving bounds at best.
  - *Bilinear exponent barrier:* Type I/II exponential sum estimates require factoring variables into $m n \sim x$ and applying Cauchy–Schwarz, which squares the diagonal contribution and freezes the level of distribution at $\theta = 1$ (or $\theta = 4/7, 17/30$ with Kloosterman sums) for fixed moduli—equivalent only to $\operatorname{Re}(\rho) < 1 - c/\log(|\gamma|+2)$, never $\operatorname{Re}(\rho) \le 1/2$.
  - *Nyquist lag-frequency law:* Controlling zeroes up to height $T$ requires prime-lag data up to $e^T$, where the trivial prime sum is $O(e^{T/2})$ while individual zero contributions are $O(1)$.
  - *Why `BVI` did not finish it:* `BVI` broke the $\theta=1$ ceiling on pronic windows $M(M+1) > M^2$ ($\theta = 2$) and eliminated Beurling countermodels via $\gcd(k, k+1)=1$, but its renormalized defect is non-positive only for $M+1 \le N$; above the sieve horizon $M > N$, inactive sawtooth drift revives the exact square-root cancellation problem.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing the missing converse direction in Lean (`RH → dyadic_band_energy_bound`, i.e., Cramér's $L^2$ explicit-formula bound) so the dyadic band-energy bridge is an `↔` rather than a one-way `←`.
    2. Replacing the classical `Littlewood_converse` hypothesis parameter in [PowerSavingIncrementCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PowerSavingIncrementCriterion.lean) and [PrimeTailCalibrationAndMobiusDefect.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PrimeTailCalibrationAndMobiusDefect.lean) with the corpus's existing unconditional Mellin–Landau bridge `riemannHypothesis_of_mertens_weighted_L2` / `riemannHypothesis_of_cesaro_mobius_bound`.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **non-Cauchy–Schwarz bilinear or incidence cancellation mechanism** that bounds the trans-horizon inactive sawtooth martingale drift (or Type II sums at a single modulus $q=1$, shift $t=0$) with $x^{1/2+o(1)}$ savings without doubling variables or losing $3/4$ of variance per successor step.
- **Dead-End Assessment:** **Not a dead end.** Overcoming Wall 1 unconditionally is literally equivalent to RH (`RiemannHypothesis_iff_vonMangoldt_remainder`). However, any attempt to overcome it via pure multiplicative sieves (ignoring additive succession) is a proven dead end due to Beurling countermodels.

---

### Wall 2: The Jensen Gap Between $|\zeta|^2$ and $\log|\zeta|$
- **Statement & Lean Anchors:** Balazard–Saias–Yor integral $\int_{\mathbb{R}} \frac{\log|\zeta(1/2+it)|}{1/4+t^2}\,dt = 2\pi \sum_{\operatorname{Re}\rho > 1/2} \log\left|\frac{\rho}{1-\rho}\right| = 0 \iff \text{RH}$ (`BalazardSaiasYorIntegral`, `OuterFactorRigidity`, `CanonicalOuterFactor`).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - Mean-value theorems and trace formulas compute $\int |\zeta(1/2+it)|^{2k}\,dt$ (moments of powers), whereas BSY requires the expectation of $\log|\zeta|$.
  - Because $\log$ is **concave**, Jensen's inequality gives $\mathbb{E}[\log|\zeta|^2] \le \log \mathbb{E}[|\zeta|^2]$, which is an **upper bound** on the BSY sum, whereas proving RH (given non-negativity of the Blaschke terms $\log|\rho/(1-\rho)| > 0$) requires either an exact identity $= 0$ or a lower bound on the outer factor's boundary value relative to interior growth.
  - Worse, any inner–outer factorization on $\operatorname{Re} s > 1/2$ hides off-line zeros inside the Blaschke product, which has modulus $1$ everywhere on $\operatorname{Re} s = 1/2$ and is completely invisible to boundary modulus measurements $|\zeta(1/2+it)|$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing the classical BSY Hardy-space Poisson–Jensen integral identity in Lean (`BSYIntegral = 2π ∑ log|ρ/(1-ρ)|`) so that route candidate `FEL` and outerness criteria connect directly to `RiemannHypothesis` without external premise wrappers.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **replica-limit or non-perturbative reverse-Jensen / Szegő-entropy theorem** for Dirichlet series with Euler products that evaluates $\lim_{k \to 0^+} \frac{\partial}{\partial k} \int |\zeta(1/2+it)|^{2k} w(t)\,dt$ exactly (or proves outerness of $(s-1)\zeta(s)/s^2$ on $\operatorname{Re} s > 1/2$ without prior zero-freeness).
- **Dead-End Assessment:** **High dead-end risk for pure boundary-modulus methods.** Because a Blaschke factor has $|B(1/2+it)| = 1$ identically, no functional of $|\zeta(1/2+it)|$ alone can ever detect an off-line zero unless paired with interior phase/argument data at $\operatorname{Re} s > 1/2$.

---

### Wall 3: Local Zero Clustering
- **Statement & Lean Anchors:** Up to $O(\log \gamma_0)$ zeros in an interval of length $O(1/\log \gamma_0)$ near height $\gamma_0$ defeat Turán power-sum lower bounds (`ZeroClusteringTuranBarrier`, `VerticalTransferDecay`).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - Suppose an off-line zero $\rho_0 = \beta_0 + i\gamma_0$ ($\beta_0 > 1/2$) exists. To convert it into a contradiction with exponential-sum bounds on $\sum_{n \le x} n^{-i\gamma_0}$, one must isolate $\rho_0$ from the $N \asymp \log \gamma_0$ nearby zeros in the local Riemann–von Mangoldt cluster.
  - By Turán's power-sum method, isolating one term from $N$ complex terms loses a factor of $(c/N)^N \asymp \gamma_0^{-c \log\log \gamma_0}$.
  - Meanwhile, Vinogradov–Korobov exponential sums only save $\exp(-c'(\log \gamma_0)^{1/3})$ or $\gamma_0^{-c'/\log\log \gamma_0}$, which is **exponentially weaker** than the Turán cluster penalty $\gamma_0^{-c \log\log \gamma_0}$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing explicit finite-cluster Turán lower-bound constants in Lean to sharpen quantitative zero-free region reductions.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Either (i) an **unconditional local zero-repulsion / Montgomery pair-correlation law** valid at *every* individual height $\gamma_0$ (not just in $t$-average) that prevents $O(\log \gamma_0)$ clustering around a putative off-line zero, or (ii) a **non-local multi-zero coherent resonator** whose lower bound does not decay exponentially in the cluster multiplicity $N$.
- **Dead-End Assessment:** **Single-height vertical transfer (`s = 1 + i\gamma_0 \to \beta_0 + i\gamma_0`) is a structural dead end** as long as only single-zero Turán isolation is used, because cluster multiplicity grows with $\gamma_0$.

---

### Wall 4: The Axis Is Outside the Zero Set (Hermite–Biehler / Jensen–Pólya / de Bruijn–Newman)
- **Statement & Lean Anchors:** Differential operators $P(D)\Xi(t)$, heat flows $e^{u D^2}\Xi(t)$, and Hermite–Biehler shifts $\Xi(z - i\alpha)$ strictly shrink off-real strip widths $\Delta \to \sqrt{\Delta^2 - \delta^2}$, never reaching $\Delta = 0$ in finite time (`HermiteBiehlerStripShrinkage`, `DeBruijnNewmanBackwardHeatObstruction`, `HorizontalCollisionSingularity`).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - Forward Pólya–Jensen multipliers $\cos(\delta D)\Xi$ and forward heat flow $t > 0$ pull zeros *toward* the real axis; to show $\Xi_0$ has real zeros from $\Xi_t$ ($t > 0$), one must run the heat equation **backward**, which is exponentially ill-posed on high frequencies.
  - Rodgers–Tao proved $\Lambda_{\mathrm{dBN}} \ge 0$, which sits on the *trivial* side of $\Lambda_{\mathrm{dBN}} \le 0$ (RH).
  - In Hermite–Biehler space $E(z) = \Xi(z - i\alpha)$, evaluating on the symmetry axis $z \in \mathbb{R}$ corresponds to $s = 1/2 + \alpha$, which lies strictly to the right of the critical line for $\alpha > 0$. As $\alpha \to 0^+$, $E(z) \to \Xi(z)$ becomes real on $\mathbb{R}$, so the Hermite–Biehler phase $\theta'(x)$ degenerates identically to $0$ (`WardOrientationDegeneracy`).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Completing finite-degree Jensen polynomial hyperbolicity certificates in Lean for fixed degrees $d$ and shifts.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **renormalized limit for the $\alpha \to 0^+$ Ward/Hermite–Biehler phase** (dividing by $\alpha$ before taking $\alpha \to 0^+$) where the resulting Cauchy–Riemann boundary derivative $-\operatorname{Re}(\xi'/\xi)(1/2+it)$ is proved globally non-negative—or an arithmetic invariant that prohibits the horizontal collision singularity at $\Lambda_{\mathrm{dBN}} > 0$.
- **Dead-End Assessment:** **Any finite-order differential multiplier $P(D)\Xi$ or forward heat flow is a proven dead end** (`StripShrinkageNoGo`); it can never reach $\Delta = 0$ from $\Delta > 0$ in finite time.

---

### Wall 5: No Frobenius, No $\mathbb{F}_1$
- **Statement & Lean Anchors:** Over $\mathbb{Q}$, there is no geometric Frobenius endomorphism, no curve $C \times C$ with intersection theory, and taking tensor powers $\zeta(s)^d$ yields the exact same zero set with scaled multiplicities (`TwinRigidityZetaPower`, `SelbergClassDegreeOneTensorTrap`).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - Weil's proof for curves over $\mathbb{F}_q$ uses two independent inputs: (1) a genuine endomorphism $\mathrm{Frob}_q$ whose fixed-point Lefschetz trace is $\sum_{x \in C(\mathbb{F}_{q^n})} 1$, and (2) Deligne/Castelnuovo–Severi positivity on $C \times C$ (or amplification via high tensor powers $\mathrm{Sym}^d H^1$ where $\mathrm{Frob}_q$ eigenvalues $\alpha_i^d$ separate in modulus).
  - For $\zeta(s)$ over $\mathbb{Q}$, the "primes" $\log p$ are not fixed points of an operator on a known cohomology space; rather, the Weil explicit formula defines a quadratic form whose positivity *is* RH.
  - Furthermore, because $\zeta(s)$ has degree $1$ in the Selberg class, its $d$-th power $\zeta(s)^d$ has $\log(\zeta^d) = d \log \zeta$, scaling all zero multiplicities by $d$ without separating off-line zeros from critical-line zeros (`TwinRigidityZetaPower`).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing the algebraic K-theory / Bost–Connes / Witt-vector functoriality bridges in Lean so candidate spaces (`SC`, `HF`) have clean categorical interfaces.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **genuine non-linear or higher-rank amplification functor on $\zeta(s)$** (not $\zeta(s)^d$, which is linear in $\log \zeta$) or an **arithmetic cohomology space with an independently positive intersection pairing** whose Lefschetz trace reproduces the explicit formula without circularly defining the inner product as the Weil form.
- **Dead-End Assessment:** **Tensor-power amplification of $\zeta(s)$ alone ($\zeta^d$) is a 100% proven dead end** (`TwinRigidityZetaPower`).

---

### Wall 6: The Probability Cone (Positivity Only in Absolute Convergence $\operatorname{Re} s > 1$)
- **Statement & Lean Anchors:** Probabilistic representations of $\zeta(s)$ (compound Poisson distributions of $\log \zeta(\sigma + it)$, Bost–Connes KMS states at $\beta > 1$, positive Euler-product weights) exist only for $\sigma > 1$ and break down across the pole $s = 1$ (`ProbabilityConeBreakdown`, `AbsoluteConvergenceGate`).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - For $\sigma > 1$, $\log \zeta(\sigma + it) = \sum_{p, k} \frac{p^{-k\sigma}}{k} e^{-it k \log p}$ has positive coefficients, making $\zeta(\sigma+it)$ an infinitely divisible characteristic function.
  - For $1/2 < \sigma < 1$, $\sum p^{-\sigma} = \infty$, the pole at $s=1$ must be subtracted, and analytic continuation replaces positive series with conditionally convergent oscillatory sums or signed analytic continuations where Markov/Bochner positivity no longer holds a priori.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Completing Lean proofs of compound-Poisson / Lévy–Khintchine identities on the half-plane $\operatorname{Re} s > 1$ and their boundary limits where known.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **pole-subtracted renormalization of the Euler product** that preserves a positivity-improving (Markov or completely positive) structure across $\sigma = 1$ down to $\sigma = 1/2$ without relying on zero-freeness to define the logarithm.
- **Dead-End Assessment:** **Direct analytic continuation of $\sigma > 1$ probability measures across $s=1$ without pole-cancellation structure is a dead end** because the pole $s=1$ forces a negative mode (`CoshMass` in `CHMD` or polar loss in `WL`).

---

### Wall 7: Statistical and Almost-All Results (Density-Zero Exceptional Sets)
- **Statement & Lean Anchors:** Moments in $t$-aspect, Bagchi's universality theorem (`BagchiErgodicBridge`), and zero-density estimates control *almost all* heights $T$ or *almost all* characters in a family, leaving a density-zero exceptional set where off-line zeros can hide.
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - Bagchi's theorem equates RH to the self-return of $\zeta(s + i\tau)$ in vertical $T$-mean (`meanSquareReturn`), where the limit $\liminf_{T\to\infty} \frac{1}{T}\int_0^T$ averages over $\tau \in [0, T]$.
  - A single off-line zero $\rho_0 = \beta_0 + i\gamma_0$ is a **localized defect** at height $\gamma_0$ unless translated by $\tau$ into the strip, where detecting its presence in the $L^2$ norm of $\zeta(s+i\tau) - \zeta(s)$ requires controlling the coupled prime-phase Kronecker approximation and the long-range tail $\sum_{n > N} n^{-s-i\tau}$ simultaneously.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing quantitative Kronecker–Weyl equidistribution and truncated Dirichlet polynomial mean-value theorems in Lean for `BAG`.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **deterministic de-averaging / rigidity principle** (or an unconditional Kronecker-to-tail transfer law in `BAG`) showing that an off-line zero creates a positive-density or non-vanishing global obstruction that cannot hide in a measure-zero exceptional set.
- **Dead-End Assessment:** **Pure $t$-moment bounds ($\int_0^T |\zeta|^{2k} \ll T(\log T)^{k^2}$) and pure zero-density estimates $N(\sigma, T) \ll T^{c(1-\sigma)}$ are dead ends for proving RH** unless $N(\sigma, T) < 1$ is achieved uniformly for all $T$.

---

### Wall 8: Infinitesimal Admixture (Weil Cone Singleton Rigidity)
- **Statement & Lean Anchors:** The cone of positive Weil weights with pole residue $1$ is the singleton $\{\Lambda\}$ (`eq_vonMangoldt_of_weilPositiveFull`, `PrimeBlindLevelCertificateSqueeze`). For any RH-free baseline weight $\lambda_0$ and any fixed $t \in (0, 1]$, positivity of $\lambda_t = t\Lambda + (1-t)\lambda_0$ is already equivalent to full RH (`InfinitesimalAdmixtureEquivalence`).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - One cannot prove RH by starting at an "easy" positive weight $\lambda_0$ and deforming continuously to $\Lambda$, nor by showing $\Lambda$ is "close" to a smooth archimedean weight: the Weil cone has **empty interior** around $\Lambda$ and is a single point!
  - In [PrimeBlindLevelCertificateSqueeze.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindLevelCertificateSqueeze.lean), the finite-level certificate sets $\operatorname{levelCertificates}(L)$ shrink to $\{\Lambda\}$ as $L \to \infty$, which means if RH were false, $\operatorname{levelCertificates}(L)$ would simply become **empty** for large $L$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. None—this wall is already completely formalized in Lean (`eq_vonMangoldt_of_weilPositiveFull` and `tendsto_levelCertificates_apply`).
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Any constructive sequence of weights $\mu_L \in \operatorname{levelCertificates}(L)$ must **literally synthesize the exact discontinuous prime-power spikes $\Lambda(n)$** as $L \to \infty$, rather than approximating $\Lambda$ by smooth archimedean weights.
- **Dead-End Assessment:** **Any homotopy / perturbation / convex-combination route $\lambda_t = t\Lambda + (1-t)\lambda_0$ is a 100% proven dead end** (`CANNOT-38`).

---

### Wall 9: The Temperedness Gate (The $\zeta(s-a)\zeta(s+a)$ Countermodel)
- **Statement & Lean Anchors:** For $a \in (0, 1/2)$, $Z_a(s) = \zeta(s-a)\zeta(s+a)$ has an Euler product of degree 2, functional equation $s \leftrightarrow 1-s$, polynomial vertical growth, and strictly non-negative Dirichlet log-derivative coefficients $\Lambda_a(n) = 2\Lambda(n)\cosh(a\log n) \ge 0$, yet has off-line zeros at $\operatorname{Re} s = 1/2 \pm a$ (`Zeta23Countermodel`, `ShiftedZetaProductCountermodel`).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - Any proof strategy that only uses: (i) Euler product factorization, (ii) functional equation $s \leftrightarrow 1-s$, (iii) polynomial growth in $|t|$, and (iv) point-wise non-negativity $\lambda(n) \ge 0$ of the explicit-formula prime weights **must fail**, because $Z_a(s)$ satisfies all four and violates RH!
  - The only features distinguishing $\zeta(s)$ from $Z_a(s)$ are:
    1. **Temperedness / Ramanujan bound:** $\Lambda(p^k) = \log p$ is constant in $k$ (bounded by $\log n$), whereas $\Lambda_a(p^k) = 2\log p \cosh(ak\log p)$ grows like $n^a$.
    2. **Simple pole at $s=1$:** $\zeta(s)$ has a single pole at $s=1$ (polar weight $\cosh(x/2)$), whereas $Z_a(s)$ has poles at $1\pm a$ (polar weight $\cosh((1/2+a)x) + \cosh((1/2-a)x)$).
    3. **Additive succession / ring structure of $\mathbb{Z}$:** `CHMDPrimeChainVariance` ($\Lambda(p^r) = \log p$ constant along prime-power chains) and `BezoutValuationIncidence` ($\gcd(k, k+1) = 1$) explicitly use $\Lambda(p^r) = \log p$ and integer succession.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Auditing and tagging every remaining candidate module against the `Zeta23Countermodel` in Lean to automatically reject any premise that holds for $Z_a(s)$.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A mechanism that makes the **temperedness equality $\Lambda(p^r) = \log p$ (constant in $r \ge 1$) and the exact pole location $s=1$** do quantitative coercivity work on the sub-threshold window modes (e.g., via `CHMDPrimeChainSourceFactorization` or `BVI` valuation clocks).
- **Dead-End Assessment:** **Any route that does not distinguish $\Lambda(p^r) = \log p$ from $2\log p\cosh(ar\log p)$ (and simple pole at $s=1$ from split poles $1\pm a$) is a guaranteed dead end.**

---

### Wall 10: The Oscillation–Transport Dichotomy
- **Statement & Lean Anchors:** Vaughan's identity and Vinogradov–Korobov bound oscillating sums $\sum_{m \le M} \mu(m) e(x/m)$ ($x \ne 0$) which carry no pole data; zero-detecting Dirichlet/Mellin sums $\sum \mu(m) m^{-s}$ are non-oscillating in $x$, and transporting between them via Mellin/incomplete-gamma transforms introduces a stationary-phase pole contribution that swamps the VK saving (`OscillationTransportDichotomy`).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - Additive phases $e(\alpha m)$ or $e(x/m)$ are almost orthogonal to multiplicative characters $m^{-i\gamma}$ unless $\gamma \asymp x/m$, where stationary phase converts the additive oscillation into a Mellin integral whose contour crosses the pole $s=1$ (or where the incomplete-gamma kernel has exponential growth on off-line zeros).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing explicit stationary-phase and Mellin–Barnes contour exchange identities in Lean for `EGC` and `MSC`.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **pole-neutral arithmetic transport kernel** (or discrete incidence identity on $\mathbb{N}$ prior to Mellin transform) that transfers cancellation from additive phases to multiplicative frequencies $m^{-i\gamma}$ without crossing the $s=1$ pole or inflating the kernel norm exponentially in $|\gamma|$.
- **Dead-End Assessment:** **Naive Mellin inversion of Vinogradov–Korobov / Weyl sums is a proven dead end.**

---

### Wall 11: Node Criticality (`PrimeBlindPositiveOn S ↔ RH ∧ PrimePowers ⊆ S`)
- **Statement & Lean Anchors:** In [PrimeBlindNodeCriticality.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindNodeCriticality.lean) and [CHMDCriticalBandReduction.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDCriticalBandReduction.lean), the archimedean + polar quadratic form is non-negative on tests vanishing on a set $S \subset (0, \infty)$ **if and only if** RH holds **and** $S$ contains **every** prime-power logarithm $k\log p$ (`PrimePowers ⊆ S`). Deleting even a single prime power (e.g., $\log 4 = 2\log 2$) makes the form strictly negative (`not_primeBlindPositiveOn_diff_singleton`), while composite nodes like $\log 6$ are redundant (`primeBlindPositiveOn_insert_composite`).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - This wall destroys any hope of proving prime-blind positivity by a "coarse density" or "prime-only ($k=1$)" argument: the quadratic form has **zero slack** on the infinite-dimensional `signedRadical`, and every single prime power $p^k$ ($k \ge 1$) is individually load-bearing!
  - Moreover, why does $\log 4$ matter while $\log 6$ does not, even though $4 < 6$ and $\varphi(4) = \varphi(6) = 2$? Because $\Lambda(4) = \log 2 > 0$ whereas $\Lambda(6) = 0$.
  - *What `BVI` achieved and why it didn't finish Wall 11:* `BezoutValuationIncidence` proved that the Bézout coprime incidence form has eigenvalue $\varphi(e) - \mu(e)$, which equals $2 - 0 = 2$ at $e=4$ and $2 - 1 = 1$ at $e=6$ (`wall11_totient_degeneracy_broken_by_bezout`), and that the valuation visibility clock $q/\operatorname{rad}(q)$ equals $2 > 1$ at $q=4$ vs. $1$ at $q=6$ (`ValuationVisibilityClockAndRamanujanSupport.lean`). However, this separation lives in the discrete factorial-period sieve coordinates and has **not yet been mapped into the continuous archimedean-minus-pole form** to enforce node criticality at $\log(p^k)$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Quotienting the `CHMD` and `EWU` forms by the explicit zero-energy `signedRadical` (`CHMDCriticalBandReduction.lean`) across all downstream receiver modules so that trivial zero-slack modes are factored out cleanly.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **continuous-to-discrete incidence bridge** that couples the `BVI` valuation clock $q/\operatorname{rad}(q)$ (or the `CHMDPrimeChainVariance` prime-power chain decomposition) directly to the continuous archimedean-minus-pole form on tests vanishing on $\operatorname{PrimePowers}$.
- **Dead-End Assessment:** **Any prime-blind positivity proof that treats the exclusion grid $S = \{k\log p\}$ merely through its asymptotic counting function $\psi(x) \sim x$ or omits higher prime powers $p^k$ ($k \ge 2$) is a 100% proven dead end** (`not_primeBlindPositiveOn_primesOnly`).

---

### Wall 12: The Forced Dual Measure (Zero Relative Slack on Near-Null Tests)
- **Statement & Lean Anchors:** By Hahn–Banach / Farkas / Krein–Milman (`PrimeBlindDualCone`, `EvenSectorFullPositivity`, `ParitySectorJointRigidity`), the unique positive measure certifying prime-blind positivity is the **critical-line zero counting measure** $\sum_{\rho} m_\rho \delta_{\gamma_\rho}$ (or equivalently on the arithmetic side, the singleton weight $\Lambda$). Near-null tests oscillating at zero frequencies $\gamma_\rho$ have archimedean energy + prime energy equal to the polar mass with **zero relative slack**.
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - Every convex-duality, Farkas-lemma, or Krein-extension reformulation (`EWU`, `OWU`, `HF`, `WL`) simply translates "the primal form is $\ge 0$ on prime-blind tests" into "there exists a positive dual witness $\lambda \ge 0$ interpolating the archimedean-minus-pole functional on prime-power lags."
  - Because the dual witness is uniquely forced to be $\lambda = \Lambda$ (or on the spectral side, the positive critical-line zero measure $\nu_S \ge 0$), **passing to the dual cone does not create slack or make the problem easier**—it just restates RH (`chmd-revisit.md` Hole 4).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. None—the dual-cone equivalences are already completely formalized in Lean (`EvenSectorFullPositivity`, `OddSectorRigidity`, `ParitySectorJointRigidity`).
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **direct primal coercivity theorem on the quotient `SourceGraph ⧸ signedRadical`** (or a nonlinear arithmetic invariant outside the linear explicit formula) that proves positivity without appealing to Hahn–Banach witness existence.
- **Dead-End Assessment:** **Pure convex-duality / Farkas / Hahn–Banach reformulations without a new non-linear arithmetic input are a proven dead end** (they are circular rephrasings of the same quadratic signature).

---

### Wall 13: Cone Mismatch (Pointwise Positive Cone vs. Bochner Autocorrelation Cone)
- **Statement & Lean Anchors:** The explicit formula requires positivity on the **Bochner convolution cone** $\{f \star \tilde{f}\}$, whereas prime-blind or Markov-contraction arguments naturally control the **pointwise positive cone** $\{F \ge 0\}$ (`ConeMismatchObstruction`, `FactorialBiNullObstruction`, `CausalTentBochnerDecomp`, `chmd-revisit.md` Phase 3).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - A test $F = f \star \tilde{f}$ that is prime-blind ($F(k\log p) = 0$) and pointwise non-negative ($F \ge 0$) can only avoid prime powers if $\operatorname{supp}(f)$ has diameter $< \log 2$, where $F$ is supported in $(-\log 2, \log 2)$—the trivial prime-free archimedean window where positivity holds unconditionally and says nothing about RH!
  - Conversely, as soon as $\operatorname{supp}(F)$ reaches beyond $\log 2$ and vanishes at $\{k\log p\}$ with $F(0)=0, F(T)\ne 0$ (as in `BiScaleUncertainty`'s factorial bi-null and causal-tent profiles), $F$ **must change sign** and cannot be a single autocorrelation $f \star \tilde{f}$ (`FactorialBiNullObstruction`).
  - In `CHMD` Doob coordinates (`chmd-revisit.md` §3), the exact same cone mismatch appears under the Beurling–Deny map $v \mapsto |v|$: the Markov jump energy $\mathcal{E}_{\mathrm{arch}}(v) + \mathcal{E}_{\mathrm{prime}}(v)$ contracts under $v \mapsto |v|$, and Perron–Frobenius forces the ground state $1$ to be simple ($\mu < 1$ on $1^\perp$), **but $v \mapsto |v|$ maps an orthogonal/odd vector $v \perp 1$ out of the primitive hyperplane $1^\perp$ into the pointwise positive cone $|v| \ge 0$**, losing the spectral gap between $\mu < 1$ (pole at $s=1$) and $\mu \le 1/2$ (RH)!
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. None—both the Bochner decomposition of causal tents (`CausalTentBochnerDecomp.lean`) and the unconditional Perron–Frobenius simplicity of eigenvalue $1$ (`eq_smul_oneL_of_resolvent_eq`, `eigenvalue_lt_one_of_primitive` in [CHMDEvenSectorPointSpectrum.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDEvenSectorPointSpectrum.lean#L408-L436)) are already proved in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **sign-sensitive / odd-sector Poincaré inequality** (or non-commutative operator factorization $L - 1 = B^* B$ on $1^\perp \cap (\text{signedRadical})^\perp$) that preserves orthogonality to the ground state $1$ without mapping $v \mapsto |v|$.
- **Dead-End Assessment:** **Any argument relying on $F \ge 0$ pointwise on $(-\log 2, \log 2)$ or on Beurling–Deny contraction $v \mapsto |v|$ alone is a 100% proven dead end** (`chmd-revisit.md` Phase 3 & 4).

---

### Wall 14: The Size Law ($S(t) \notin L^1$ and Infinite Deficiency of the Prime Perturbation)
- **Statement & Lean Anchors:** $\int_A^T |S(t)|\,dt \ge c T/\log T \to \infty$ (`SizeLawObstruction`, `UnitaryScatteringPhaseDecoupling`, `TraceClassPerturbationNoGo`).
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - Because the zero-counting remainder $S(t) = \frac{1}{\pi}\arg \zeta(1/2+it)$ is not in $L^1(\mathbb{R})$, the primes **cannot** enter as a trace-class, Hilbert–Schmidt, finite-rank, or finite-deficiency Krein perturbation of a smooth archimedean operator.
  - Furthermore, if one writes each Euler factor $(1 - p^{-s})^{-1}$ as a unitary scattering matrix $S_p(t) = \frac{1 - p^{-1/2-it}}{1 - p^{-1/2+it}}$ on the critical line, each $S_p(t)$ is already a pure unimodular phase on $\operatorname{Re} s = 1/2$ and decouples prime-by-prime without constraining global zero locations unless assembled through the non-convergent product over all $p$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing relative-trace / regularized Fredholm determinant $\det_2(I + K)$ identities in Lean for `APF`.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **distributional / $\Theta$-weighted resolvent spectral theory** (like the compact self-adjoint resolvent $R = (1+L)^{-1}$ on $L^2(\Theta\cosh(x/2)\,dx)$ in `CHMD`, where the essential spectrum $[0, 1/2]$ is already controlled unconditionally by `weyl_value_le_half`) combined with a finite-window bound-state elimination theorem.
- **Dead-End Assessment:** **Naive Birman–Krein trace-class scattering or finite-deficiency self-adjoint extension theory without $\Theta$-weighting is a proven dead end.**

---

### Wall 15: Support Versus Positivity (Poincaré–Lelong & Reflection-Even Positivity Blindness)
- **Statement & Lean Anchors:** For *any* holomorphic function $f$, the Poincaré–Lelong current $\frac{i}{\pi}\partial\bar{\partial}\log|f(z)|^2 = \sum_{f(\rho)=0} m_\rho \delta_\rho \ge 0$ is a positive measure regardless of where the zeros $\rho$ lie (`SupportVsPositivityObstruction`, `ReflectionSymmetricKernelPositivity`). Similarly, $(f, g) \mapsto \int \Xi(t-s)f(t)\overline{g(s)}$ is positive-definite for any even real function $\Xi$.
- **Why We and Mathematics Failed So Far / What Makes It Hard:**
  - Positivity of a 2D Riesz/Poincaré–Lelong measure $\Delta \log|\xi(s)| \ge 0$ on $\mathbb{C}$ only says that zeros have positive integer multiplicity $m_\rho \ge 1$; it says **nothing** about whether their support lies on the 1D line $\operatorname{Re} s = 1/2$!
  - Worse, any reflection-symmetric pairing $\widehat{F}(\gamma_\rho)\widehat{F}(\overline{\gamma_\rho}) = |\widehat{F}(\gamma_\rho)|^2 \ge 0$ is non-negative at **every** zero $\gamma_\rho \in \mathbb{C}$ unless the conjugation matches the critical-line involution $\gamma \leftrightarrow \bar{\gamma}$ vs. $-\bar{\gamma}$ (`widehat{F}(\gamma_\rho)\widehat{F}(-\gamma_\rho)` in the Weil explicit formula, where an imaginary part $\gamma_\rho = \alpha + i\beta$ with $\beta \ne 0$ gives an oscillatory/negative contribution $-m_\rho$ on `imVector` in `CHMDCardinalGraphGeometry.lean`).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. None—this distinction is fully understood and formalized (`CHMDCardinalGraphGeometry.lean`).
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - An **involution-sensitive positivity certificate** (respecting $f^\#(x) = \overline{f(-x)}$, i.e., $\widehat{f \star f^\#}(\gamma) = \widehat{f}(\gamma)\overline{\widehat{f}(\bar{\gamma})}$) rather than reflection-even or 2D subharmonic positivity.
- **Dead-End Assessment:** **Any route based purely on 2D subharmonicity $\Delta \log|\Xi| \ge 0$ or reflection-even Gram matrices is a 100% proven dead end.**

---

## Part II: The 27 Live Proof Routes (`docs/reports/rh-current-frontier-map.md`)

For every Live Route (`#1` through `#27`), we list its Lean bridge status, the exact hard obstacles blocking closure, why our Lean corpus and mathematics failed so far, the split into **Solvable ("Just Work")** vs. **Requires New Mathematics**, and its **Dead-End / Viability Assessment**.

---

### 1. `WL` — Weil Lag Function
- **Route Path & Lean Status:** Explicit formula $\to$ prime-blind lag cones & Krein/de Branges collars $\to$ Weil positivity $\to$ RH (`riemannHypothesis_of_archimedean_dominates_polar_on_primeBlind`, `riemannHypothesis_of_weil_positivity`, plus `BiScaleUncertainty` collar modules).
- **Hard Obstacles & Why We Failed So Far:**
  - On any prime-blind autocorrelation $F = f \star \tilde{f}$ supported beyond $\log 2$, we need $Q_{\mathrm{arch}}(F) \ge Q_{\mathrm{pole}}(F)$.
  - `BiScaleUncertainty` proved that factorial-grid Müntz-ramp and causal-tent profiles cannot be single autocorrelations (`FactorialBiNullObstruction`), that the negative polar loss $\frac{1}{4}\frac{\log(n+2)}{n+1}$ dominates the mixed Gram coupling $o(1/(n+1))$ (`FactorialPolarGramScaleSeparation`), and that canonical polar-repaired tails have positive Weil energy unconditionally (`FactorialMuntzTailWeilGrowth`), making them blind to off-line zeros.
  - Furthermore, by `InfiniteGridStrictEnergyLoss`, taking limits of finite-grid prime-blind functions can leak positive Lévy energy into the origin $t=0$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Wiring the remaining 1D collar transport and finite-grid realization lemmas across general (non-factorial) finite lag grids.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **single-autocorrelation prime-blind producer** $F = f \star \tilde{f}$ (not a difference $R_1 - R_2$ of two autocorrelations) that controls origin-concentration energy loss and dominates the $\cosh(t/2)$ polar term uniformly across all prime-power lags $\{k\log p\}$ (Walls 11, 12, 13).
- **Dead-End Assessment:** **Viable receiver, but the factorial Müntz-ramp / causal-tent difference programme is a dead end** because subtracting two autocorrelations of energy $\Theta(\sqrt{N})$ destroys Bochner cone membership.

---

### 2. `RW` — Restricted Weil Ground Energy
- **Route Path & Lean Status:** Compact-window ground-state Rayleigh quotient $E_0(a) = \inf_{\|u\|=1} Q_W(u)$ on $L^2[-a, a]$ $\to$ $E_0(a) \ge 0$ for all $a > 0$ $\to$ RH (`riemannHypothesis_iff_forall_groundEnergy_nonneg`, `BiScaleUncertainty` Krein collar & origin-budget modules).
- **Hard Obstacles & Why We Failed So Far:**
  - For $a \le \frac{1}{2}\log 2$, $E_0(a) \ge 0$ holds unconditionally because $2a < \log 2$ hits no primes.
  - For $a > \frac{1}{2}\log 2$, prime shifts $\log p \le 2a$ and the exponentially growing polar kernel $-\cosh(t/2)$ enter. By Wall 11 (`PrimeBlindNodeCriticality`), $E_0(a)$ has **zero slack** on the critical band (`signedRadical`), and every prime power $p^k \le e^{2a}$ is needed to balance $-\cosh(t/2)$.
  - `BiScaleUncertainty` reduced the origin-collar budget to $O(n^{-3/2})$ (`OriginBudgetConcentration`) and resolved the $4\log 2/5$ non-dyadic interpolation gap (`FoldedCollarResolution`), **but** proved in `EvenSectorBlindGroundShiftInvariance.lean` that subtracting $m(a)\|Ju\|^2$ is shift-gauge invariant ($A + C \mapsto A$), so the ground-state identity alone cannot determine whether the minimum eigenvalue $m(a)$ is $\ge 0$ or $< 0$!
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Extending numerical/rigorous interval-arithmetic certificates for $E_0(a) \ge 0$ on bounded finite windows $a \le A_0$ (e.g., $2a \le \log N_0$).
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - An **asymptotic large-window ($a \to \infty$) coercivity theorem** showing that on the quotient modulo `signedRadical`, the prime-power jump sum $\sum_{p^k \le e^{2a}} \frac{\log p}{p^{k/2}}$ plus the archimedean Lévy form dominates the $\cosh(t/2)$ polar mass for all $a \to \infty$ (Walls 9, 11, 13).
- **Dead-End Assessment:** **Shift-gauge ground-state identities on prime-blind subspaces are a dead end (`EvenSectorBlindGroundShiftInvariance`)**; `RW` can only succeed by directly bounding the full prime+archimedean-minus-pole form as $a \to \infty$.

---

### 3. `FU` — CCM-FU Signed Prime Scheduling
- **Route Path & Lean Status:** Connes–Consani–Moscovici / signed prime-schedule quadratic forms $\to$ cofinal positive-definite prime schedules $\to$ RH (`riemannHypothesis_of_ccm_fu_cofinal_positivity`).
- **Hard Obstacles & Why We Failed So Far:**
  - CCM-style truncated Euler products over finite sets of primes $S$ produce approximate zeros on the critical line only if the cutoff kernel is positive-definite and converges to the full prime sum.
  - By Wall 8 (`InfinitesimalAdmixture`) and Wall 11 (`NodeCriticality`), any signed or truncated prime schedule that deviates from the exact weight $\Lambda(p^k) = \log p$ on any prime power $p^k \le e^{2a}$ either fails positivity on the critical band or fails to converge to the full Weil form without losing origin Lévy energy (`InfiniteGridStrictEnergyLoss`).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing explicit finite-prime Euler-product determinant identities for small prime sets $\{2, 3, 5\}$.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **limit-preserving prime-schedule renormalization** that adds primes $p \to \infty$ while keeping the quadratic form positive on the critical band without triggering `InfiniteGridStrictEnergyLoss` (Walls 8, 11, 14).
- **Dead-End Assessment:** **High dead-end risk** if finite prime truncations are expected to be positive before all prime powers below the window horizon $e^{2a}$ are included (violates Wall 11).

---

### 4. `RP` — Route-P / SP-E History Floor
- **Route Path & Lean Status:** Sequential prime-introduction / filtration history floor $\to$ non-negative martingale/history floor at all horizons $\to$ RH (`riemannHypothesis_of_history_floor_nonneg`).
- **Hard Obstacles & Why We Failed So Far:**
  - When primes (or sieve divisors) are revealed sequentially, one wants the conditional expectation / history energy floor to remain bounded below by the polar target.
  - As shown in `BezoutValuationIncidence` ([PrimeTailCalibrationAndMobiusDefect.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PrimeTailCalibrationAndMobiusDefect.lean) and [ActiveDeletedMartingaleAndShiftedEulerConvergence.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ActiveDeletedMartingaleAndShiftedEulerConvergence.lean)), the active martingale jump cancels the active divisor squares 100%, **but** the inactive centered sawtooth martingale drift across integers $M > N$ with unrevealed prime factors $p > N$ oscillates in sign and carries the entire difficulty of Wall 1.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Connecting the `BVI` active/inactive martingale split (`ActiveDeletedMartingaleAndShiftedEulerConvergence.lean`) directly to the `RP` history-floor definitions in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Controlling the **inactive trans-horizon martingale drift** generated by unrevealed primes $p > N$ on composite numbers $M > N$ (Wall 1).
- **Dead-End Assessment:** **Sub-horizon filtration arguments ($M \le N$) are a dead end for RH** because they are identically tautological ($g(k)=0$ for $2 \le k \le N$); only trans-horizon filtration control ($M \gg N$) carries RH content.

---

### 5. `PA` — Prime–Archimedean Source Passivity
- **Route Path & Lean Status:** Positive-real / passive impedance transfer between the archimedean digamma source and the prime Dirichlet series $\to$ passivity on $\operatorname{Re} s > 1/2$ $\to$ RH (`riemannHypothesis_of_prime_archimedean_passivity`).
- **Hard Obstacles & Why We Failed So Far:**
  - In systems theory, a holomorphic function $Z(s)$ on $\operatorname{Re} s > 1/2$ is positive-real ($\operatorname{Re} Z(s) \ge 0$, Herglotz/Carathéodory) iff it has no poles and no sign reversals of its real part in the half-plane.
  - For $-\frac{\xi'}{\xi}(s)$, passivity on $\operatorname{Re} s > 1/2$ is impossible if $\xi$ has a zero $\rho_0$ with $\operatorname{Re} \rho_0 > 1/2$, because a simple pole $\frac{1}{s-\rho_0}$ winds in phase by $2\pi$ around $\rho_0$ and takes negative real values!
  - However, proving passivity from the arithmetic representation $-\frac{\zeta'}{\zeta}(s) = \sum \Lambda(n)n^{-s}$ hits Wall 6 (the series only converges for $\operatorname{Re} s > 1$) and Wall 12/13 (on test functions, passivity is the exact Weil quadratic form).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Completing the Cayley transform Equivalence between Herglotz passivity ($\operatorname{Re} Z \ge 0$) and Schur contractivity ($|\Theta_{\mathrm{Schur}}| \le 1$) across `PA` and `GTA` in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **state-space realization of the pole-subtracted arithmetic impedance** on $\operatorname{Re} s > 1/2$ whose energy dissipation inequality is proved from multiplicative factorization without assuming zero-freeness (Walls 6, 12, 13).
- **Dead-End Assessment:** **Equivalent to `WL` / `CHMD` under Laplace/Fourier transform; no independent leverage unless paired with a nonlinear multiplicative invariant.**

---

### 6. `MC` — Möbius Cancellation at Half Power
- **Route Path & Lean Status:** Square-root Mertens / Cesàro / Riesz / shifted-exponent Möbius bounds $M(x) = O(x^{1/2+\varepsilon})$ $\to$ analytic continuation of $1/\zeta(s)$ to $\operatorname{Re} s > 1/2$ $\to$ RH (`riemannHypothesis_of_mertens_bound`, `riemannHypothesis_of_cesaro_mobius_bound`, `PowerSavingIncrementCriterion.lean`, `BezoutValuationIncidence` 40-module tower).
- **Hard Obstacles & Why We Failed So Far:**
  - `MC` is the purest arithmetic route and the main target of `BezoutValuationIncidence` (`BVI`).
  - `BVI` proved:
    1. Exact Ramanujan restoration and diagonalization of the Selberg LCM + Bézout coprime quadratic forms (`RamanujanRestorationAndBezoutDiagonal.lean`).
    2. Exact two-moment and primitive-energy cones (`ExactSuccessorMomentRegionAndUniversalInequalities.lean`, `SharpPrimitiveEnergySuccessorFrontier.lean`).
    3. Sharp $3/4$ one-step phase loss above parity (`SharpSuccessorPhaseLossAndClosureClassification.lean`).
    4. Exact visibility clock $q/\operatorname{rad}(q) \mid h$ for true $h$-lag translation (`ValuationVisibilityClockAndRamanujanSupport.lean`, `ArithmeticLagSchedulesAndSharpRecoveryHorizon.lean`).
    5. Exact sub-horizon non-positivity of the renormalized defect for $M+1 \le N$ (`PowerDampedRenormalizedDefectAndPronicCeiling.lean`).
    6. Exact cancellation of active divisor squares against active martingale jumps and $+1/2$ rate convergence of the active shifted Euler product $\tau_\varepsilon\tau_{1+\varepsilon}$ (`ActiveDeletedMartingaleAndShiftedEulerConvergence.lean`, `ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.lean`).
  - **Why `MC` is still blocked:**
    - In [PrimeTailCalibrationAndMobiusDefect.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PrimeTailCalibrationAndMobiusDefect.lean), the raw combined defect at $M=N$ blows up linearly as $N\cdot \text{successorReserve} - 1$ due to terminal primes $p \in (N/2, N]$.
    - When renormalized by subtracting $M\cdot \text{successorReserve}$, the defect is $\le 0$ for $M+1 \le N$, **but** to bound $M(x)$ via [PowerSavingIncrementCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PowerSavingIncrementCriterion.lean), one must bound the **trans-horizon prefix sums $M \gg N$** (where $g_N(k) = \sum_{d \mid k, d \le N} \mu(d)$ is no longer $0$, because $k$ has prime factors $> N$).
    - In that trans-horizon regime, the **inactive centered sawtooth martingale drift** is not controlled by finite-period $N!$ divisibility, and true $h$-lag recovery of prime-power modes up to $M$ requires consecutive lags up to $M/2$ (`sieveLagRecoveryHorizon`).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Eliminating the external `Littlewood_converse` hypothesis in [PowerSavingIncrementCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PowerSavingIncrementCriterion.lean) by wiring it directly to the already-formalized Mellin–Landau bridge in `RHTower`.
    2. Extending the `BVI` shifted-exponent active-martingale identities to arbitrary multi-lag schedules $H \subset \{1, \dots, T\}$.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **trans-horizon sawtooth martingale bound** that controls $\sum_{k=N+1}^M g_N(k)$ (or the inactive sawtooth drift as $\varepsilon \downarrow 0$) across scales $M \in [N, N^2]$ without requiring complete divisibility modulo $N!$ (Walls 1, 10, 11).
- **Dead-End Assessment:** **One of the highest-viability routes in the entire repository, provided we move from sub-horizon ($M \le N$) identities to trans-horizon ($N < M \le N^2$) Buchstab/sawtooth coupling.** Sub-horizon identities alone ($M \le N$) cannot prove RH.

---

### 7. `TT` — Theta-Tail and Heat–Cassini Currents
- **Route Path & Lean Status:** Jacobi theta kernel $\Theta(x)$ & heat–Cassini / Turán determinantal currents $\to$ global sign of the seventh-mode / Cassini heat current $\to$ RH (`riemannHypothesis_of_theta_cassini_positivity`).
- **Hard Obstacles & Why We Failed So Far:**
  - By Wall 4 (`HermiteBiehlerStripShrinkage`), Turán/Cassini inequalities $(\Xi')^2 - \Xi\Xi'' \ge 0$ (Laguerre–Pólya class) are consequences of real-rootedness, not easily provable *before* real-rootedness, because local heat flow only shrinks strip width.
  - On the arithmetic side, expanding the bilinear theta current $\Theta(x+y)\Theta(x-y)$ produces seventh-mode polynomial/exponential head terms near $x \to \infty$ (the pole $s=1$ contribution) that compete with the Gaussian sum over $(m, n) \in \mathbb{N}^2$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing the seventh-mode polynomial/exponential head asymptotics and Poisson summation remainder bounds in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Proving that the **2D lattice theta-Cassini current remains pointwise or integrally positive** after subtracting the $s=1$ pole head, which requires beating Wall 4 (strip shrinkage) and Wall 13 (cone mismatch).
- **Dead-End Assessment:** **Pointwise Cassini/Turán positivity $(\Xi')^2 - \Xi\Xi'' \ge 0$ via heat flow is a dead end (Wall 4)**; only integral/spectral formulations (`CHMD`) survive.

---

### 8. `LA` — Line Anchor
- **Route Path & Lean Status:** Critical-line anchor identities & symmetry-axis energy pinning $\to$ absence of off-line zero pairs $(\rho, 1-\bar{\rho})$ $\to$ RH (`riemannHypothesis_of_line_anchor`).
- **Hard Obstacles & Why We Failed So Far:**
  - Any functional symmetric under $s \leftrightarrow 1-s$ and $s \leftrightarrow \bar{s}$ treats a critical-line pair $(\frac{1}{2}+i\gamma, \frac{1}{2}-i\gamma)$ and an off-line quadrupole $(\beta+i\gamma, 1-\beta+i\gamma, \beta-i\gamma, 1-\beta-i\gamma)$ identically under reflection-even kernels (Wall 15: `SupportVsPositivityObstruction`).
  - Only when paired with the involution-sensitive kernel $\widehat{f}(\gamma_\rho)\widehat{f}(-\gamma_\rho)$ does the off-line quadrupole acquire a negative imaginary mode (`imVector` in `CHMDCardinalGraphGeometry`), which immediately reduces `LA` to `CHMD` / `WL`.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Consolidating the `LA` receiver wrappers into `CHMDCardinalGraphGeometry` so duplicate spectral-pair definitions are unified.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Ruling out the negative-energy cardinal packet `imVector` at $a = \alpha + i\beta$ ($\beta \ne 0$) using multiplicative prime structure (Walls 9, 15).
- **Dead-End Assessment:** **Subsumed by `CHMD`; standalone reflection-symmetric line-anchor arguments are a dead end (Wall 15).**

---

### 9. `TG` — Topological Sub-Unit Gate
- **Route Path & Lean Status:** Argument principle / winding-number quantization $\oint \frac{\xi'}{\xi}\,ds \in 2\pi i \mathbb{Z}_{\ge 0}$ $\to$ sub-unit bound $N_{\mathrm{off}}(T) < 1 \implies N_{\mathrm{off}}(T) = 0$ $\to$ RH (`riemannHypothesis_of_sub_unit_winding`).
- **Hard Obstacles & Why We Failed So Far:**
  - Because the number of zeros in a rectangle is a non-negative integer, any upper bound strictly less than $1$ proves it is $0$.
  - However, by Wall 3 (`ZeroClusteringTuranBarrier`) and Wall 7 (`StatisticalAndAlmostAll`), every known contour or mollifier estimate for $N(\sigma, T)$ has an additive error term that grows with $T$ (or requires averaging over $T$), never achieving $< 1$ on individual rectangles at arbitrary height $T$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing explicit contour-integration / argument-principle rectangle lemmas in Lean for `TG` and `EGC`.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **spectrally localized projection** (such as the finite-rank bound-state inertia count in `CHMDBoundStateInertia.lean`, where each off-line zero contributes integer multiplicity $\ge 1$ to the $(1/2, 1)$ eigenspace of $R = (1+L)^{-1}$) paired with a trace/norm bound $< 1$ on the quotient space (Walls 3, 7, 14).
- **Dead-End Assessment:** **Contour winding-number bounds with mollifiers are a dead end at large $T$**; the only viable version of `TG` is bounding the trace/norm of the `CHMD` bound-state projection above $1/2$ by $< 1$.

---

### 10. `HF` — Positive Hodge Form on Arithmetic Cohomology
- **Route Path & Lean Status:** Quotient of test space by the zero-invisible / prime-blind kernel $\to$ Hodge / Krein self-adjointness and positivity of the induced intersection form $\to$ RH (`riemannHypothesis_of_hodge_form_positivity`, `BiScaleUncertainty` collar optimizer modules).
- **Hard Obstacles & Why We Failed So Far:**
  - We have no independent geometric definition of the "arithmetic cohomology space" $H^1_{\mathrm{arith}}$ other than quotienting the space of test functions by the radical of the Weil explicit formula (Wall 5: `NoFrobeniusNoF1`).
  - When defined as that quotient, proving the induced bilinear form is positive-definite (rather than Lorentzian/Krein-indefinite) is literally equivalent to proving the Weil form has no negative directions (`imVector` from off-line zeros).
  - In `BiScaleUncertainty`, general-grid collar optimizer attainment and Krein collar transport were developed to control the boundary defect of this form, but hit `InfiniteGridStrictEnergyLoss` and `FactorialPolarGramScaleSeparation`.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Proving general-grid collar optimizer attainment in Lean for arbitrary finite prime-power grids.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - An **intrinsic positivity mechanism on the quotient `SourceGraph ⧸ signedRadical`** that does not rely on an non-existent $\mathbb{F}_1$ curve geometry (Walls 5, 11, 12).
- **Dead-End Assessment:** **Purely formal cohomology wrappers around the Weil form provide no new leverage** unless they incorporate the multiplicative divisor-chain structure (`CHMDPrimeChainVariance` / `BVI`).

---

### 11. `CHMD` — Causal Hyperbolic–Modular Duality
- **Route Path & Lean Status:** Jacobi $\Theta(x)$-Doob transform $\to$ reversible Markov jump generator $L = L_{\mathrm{arch}} + L_{\mathrm{prime}}$ on $L^2(\Theta(x)\cosh(x/2)\,dx)$ $\to$ compact self-adjoint resolvent $R = (1+L)^{-1}$ with essential spectrum $[0, 1/2]$ $\to$ RH $\iff$ no bound state of $R$ in $(1/2, 1)$ on $1^\perp$ (equivalently on the odd sector $v(-x)=-v(x)$) (`riemannHypothesis_iff_resolventHalfBound`, `riemannHypothesis_iff_no_odd_bound_state`, `riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare`, `eq_smul_oneL_of_resolvent_eq`, `eigenvalue_lt_one_of_primitive`).
- **Hard Obstacles & Why We Failed So Far:**
  - `CHMD` is the most completely formalized spectral operator reduction in the repository:
    1. It **solved Wall 14 (Size Law / Essential Spectrum):** `weyl_value_le_half` in [CHMDNoWeylAboveThreshold.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDNoWeylAboveThreshold.lean) proves unconditionally that the essential spectrum of $R$ lies in $[0, 1/2]$ (spatial confinement $|x| > R$ comes from $\mathcal{E}_{\mathrm{prime}}$ via the theta harmonic identity in [CHMDFarFieldEnergy.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDFarFieldEnergy.lean); frequency confinement $|r| > T$ on $[-R, R]$ comes from $\mathcal{E}_{\mathrm{arch}}$ in [CHMDWindowLocalization.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDWindowLocalization.lean)).
    2. It **solved the ground eigenvalue $\mu = 1$:** [CHMDEvenSectorPointSpectrum.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDEvenSectorPointSpectrum.lean#L408-L436) proves unconditionally that $\mu = 1$ ($L(1)=0$, the pole at $s=1$) is a simple eigenvalue (`eigenvalue_lt_one_of_primitive`).
    3. It **identified the exact off-line zero obstructions:** Each off-line zero $a = \alpha + i\beta$ ($\beta \ne 0$) creates a smooth `divisorCardinalSource a` whose imaginary part `imVector` has $\operatorname{sourceEnergy}(F.\text{imVector}) = -m_a < 0$ ([CHMDCardinalGraphGeometry.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDCardinalGraphGeometry.lean)).
    4. It **extracted two genuine multiplicative invariants beyond the linear explicit formula:** (a) Zero-silent odd polar positivity $\operatorname{sourceEnergy}(p) = +2\operatorname{polarSine}(p)^2 \ge 0$ ([CHMDFullSpectralPairing.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDFullSpectralPairing.lean)), and (b) Prime-power divisor-chain variance factorization $\mathcal{E}_{\mathrm{prime}} = \sum_N \text{chainVariance}(N)$ using unique factorization $N = mdn$ and $\Lambda(p^r) = \log p$ ([CHMDPrimeChainVariance.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeChainVariance.lean), [CHMDPrimeChainSourceFactorization.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeChainSourceFactorization.lean)).
  - **Why `CHMD` still hit a wall (see [chmd-revisit.md](file:///Users/michael/Documents/code/hgt/docs/reports/chmd-revisit.md)):**
    1. *The Linear vs. Quadratic Cosh-Mass Trap:* Oddness $v(-x) = -v(x)$ kills the linear pole moment $\int \Theta\cosh(x/2)v\,dx = 0$, **not** the quadratic mass $\int \Theta\cosh(x/2)v(x)^2\,dx > 0$ (`Hole 2`).
    2. *The Perron–Frobenius / Beurling–Deny Gap (Wall 13 in Doob coordinates):* While $\mathcal{E}_{\mathrm{arch}}(v) + \mathcal{E}_{\mathrm{prime}}(v)$ decreases under $v \mapsto |v|$, $|v|$ is even and non-negative, so it is no longer orthogonal to $1$. Thus Beurling–Deny + Perron–Frobenius only gives $\lambda_1(L) > 0$ ($\mu < 1$), whereas RH requires the **spectral gap $\lambda_1(L) \ge 1$** ($\mu \le 1/2$) on $1^\perp$!
    3. *Young-Inequality Cusp-to-Window Penalty:* In `CHMDFarFieldEnergy.lean`, proving spatial confinement for $|x| > R$ via Young's inequality charges a negative penalty $-C_\varepsilon \int_{-R}^R v^2\,d\mu$ to the compact window $[-R, R]$, leaving finitely many sub-threshold modes in the box $\{|x| \le R, |r| \le T\}$.
    4. *Zero Slack on `signedRadical` (Wall 11) and Fake-Weight Countermodels (Wall 9):* On `signedRadical`, $\mathcal{E}_{\mathrm{arch}} + \mathcal{E}_{\mathrm{prime}} - \operatorname{CoshMass} = 0$ with zero slack, and any argument that does not use unique factorization / $\Lambda(p^r) = \log p$ fails for fake weights $\tilde{\lambda} \ge 0$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Proving closed-range / spanning of the finite-dimensional bound-state eigenspace in $(1/2, 1)$ by the explicit `divisorCardinalSource` frames in [CHMDCardinalGraphGeometry.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDCardinalGraphGeometry.lean) (currently existence and inertia inequality are proved; spanning is a standard finite-dimensional Fredholm/Paley–Wiener residue exercise).
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Proving the **spectral gap $\lambda_1(L) \ge 1$ on the odd sector modulo `signedRadical`** by coupling the multiplicative prime-power chain variance (`doob_source_eq_chain_variances_sub_cosh`) and the differential-difference equation $(A - 1)(u_{\mathrm{re}} + i u_{\mathrm{im}}) = m_a \cos(\bar{a}x)/\cosh(x/2)$ of a putative off-line cardinal packet to the archimedean jump form $\mathcal{E}_{\mathrm{arch}}$ without Young-inequality leakage (Walls 9, 11, 13).
- **Dead-End Assessment:** **The strongest analytic-spectral route in the corpus.** However, the "small window $2\log 2$ one-signed odd cone" sub-programme is a **proven dead end** (Wall 13), and any $+X - X$ reorganization of the linear explicit formula is a **proven dead end**. Only the multiplicative chain-variance / cardinal-packet contradiction on the quotient space remains viable.

---

### 12. `TH` — Theta Moment Positivity
- **Route Path & Lean Status:** Mellin representation $\Xi(t) = \int_0^\infty \Phi(x)\cos(tx)\,dx$ $\to$ Turán / Hankel / Chebyshev moment positivity of $\Phi(x)$ $\to$ RH (`riemannHypothesis_of_theta_moment_positivity`).
- **Hard Obstacles & Why We Failed So Far:**
  - By Pólya's theorem, Turán inequalities $M_{2k}^2 - M_{2k-2}M_{2k+2} \ge 0$ for all Taylor coefficients of $\Xi(t)$ are necessary for real-rootedness, and each fixed finite Hankel determinant can be verified numerically (`Griffin–Ono–Rolen–Zagier`).
  - However, proving the infinite hierarchy of degree-$d$ Jensen/Hankel determinants simultaneously as $d \to \infty$, $n \to \infty$ hits Wall 4 (any fixed degree $d$ only tests strip width $O(d^{-1/2})$) and Wall 9 (the moment generating function of $\Phi(x)$ is just $\Xi(t)$ itself, whose real-rootedness depends on the multiplicative origin of $\Theta(x) = \sum_{n=1}^\infty e^{-\pi n^2 e^{4x}}$).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing asymptotic Hermite-polynomial approximations for fixed degree $d$ and large shift $n \to \infty$ (the Griffin–Ono–Rolen–Zagier regime) in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Uniform positivity in the **joint scaling regime $d \to \infty$ with $n/d \to 0$** (the regime that actually implies real-rootedness of $\Xi$), which requires an arithmetic identity on $\Theta(x)$ beyond smooth steepest-descent asymptotics (Walls 4, 9).
- **Dead-End Assessment:** **Large-shift $n \to \infty$ asymptotics for fixed $d$ is a dead end for RH** because it holds for arbitrary smooth kernels with Gaussian decay regardless of whether their Fourier transform has off-line zeros!

---

### 13. `RN` — Theta Renewal and Singular Comparison
- **Route Path & Lean Status:** Convolution renewal equation for $\Theta(x)$ against the prime jump measure $\to$ positivity/monotonicity of the renewal resolvent $\to$ RH (`riemannHypothesis_of_theta_renewal_positivity`).
- **Hard Obstacles & Why We Failed So Far:**
  - The theta harmonic identity ([CHMDThetaHarmonicIdentity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDThetaHarmonicIdentity.lean)) states $\sum_{n \ge 2} \frac{\Lambda(n)}{\sqrt{n}}\Theta(x+\log n) = \Theta(x)\cosh(x/2) + S_{\mathrm{arch}}(x)$.
  - As uncovered in [chmd-revisit.md](file:///Users/michael/Documents/code/hgt/docs/reports/chmd-revisit.md#L352), this means $(L_\infty + L_P)\Theta = +\frac{1}{2}\cosh(x/2)\Theta > 0$: $\Theta$ is **subharmonic** (not superharmonic!) for the arithmetic generator, because $\Theta$ annihilates the zeros of $\zeta$ while retaining the pole at $s=1$. Thus the renewal potential has sign $-\frac{1}{2}\cosh(x/2) < 0$, which is the exact negative pole mass in `CHMD`.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Merging the `RN` renewal wrappers with `CHMDThetaHarmonicIdentity.lean`.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Overcoming the subharmonic sign $-\frac{1}{2}\cosh(x/2)$ on $1^\perp$, which is identical to the `CHMD` spectral gap $\lambda_1(L) \ge 1$ (Walls 6, 13).
- **Dead-End Assessment:** **Subsumed by `CHMD`; treating $\Theta$ as a positive superharmonic Barta weight is a proven mathematical error** because $(L_\infty + L_P)\Theta$ has the opposite sign due to the pole at $s=1$.

---

### 14. `WD` — Ward Orientation and Horizontal Collision
- **Route Path & Lean Status:** Two-variable Ward / Cauchy–Riemann phase orientation around critical-line zeros $\to$ absence of horizontal collision singularities $\to$ RH (`riemannHypothesis_of_ward_orientation`).
- **Hard Obstacles & Why We Failed So Far:**
  - On the critical line $\sigma = 1/2$, $\Xi(t)$ is real, so its phase is piecewise constant ($0$ or $\pi$) and its derivative vanishes except as Dirac deltas at real zeros (Wall 4: `WardOrientationDegeneracy`).
  - Moving off the line to $\sigma = 1/2 + \alpha$ ($\alpha > 0$) gives the Cauchy–Riemann identity $\frac{\partial}{\partial t}\arg \xi(1/2+\alpha+it) = -\operatorname{Re}\frac{\xi'}{\xi}(1/2+\alpha+it)$. Proving this is positive as $\alpha \to 0^+$ requires showing no zeros lie to the right of $1/2+\alpha$, which is circular unless controlled from the arithmetic side (where $-\zeta'/\zeta$ diverges for $\sigma \le 1$).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing the local Puiseux/Bendixson index formula for simple vs. multiple zeros of $\Xi(t)$ in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **global boundary monotonicity certificate** for $\arg \xi(1/2+\alpha+it)$ as $\alpha \to 0^+$ derived from prime factorization rather than interior zero-freeness (Walls 4, 6).
- **Dead-End Assessment:** **Local phase-portrait analysis around a putative collision without global arithmetic input is a dead end** because analytic functions with off-line zeros satisfy all local Cauchy–Riemann identities away from the zeros.

---

### 15. `LI` — Paired Li and Prime–Gamma Balances
- **Route Path & Lean Status:** Li coefficients $\lambda_n = \sum_\rho \bigl(1 - (1 - 1/\rho)^n\bigr) = \lambda_{n,\mathrm{arch}} + \lambda_{n,\mathrm{pole}} - \lambda_{n,\mathrm{prime}} \ge 0$ for all $n \ge 1 \iff \text{RH}$ (`riemannHypothesis_iff_li_positivity`, plus `BiScaleUncertainty` factorial-Müntz / Laguerre polynomial modules).
- **Hard Obstacles & Why We Failed So Far:**
  - $\lambda_{n,\mathrm{arch}} + \lambda_{n,\mathrm{pole}} \sim \frac{1}{2}n \log n + c n$, while the prime sum $\lambda_{n,\mathrm{prime}}$ is a sum of Laguerre polynomials $L_{n-1}^{(1)}(k\log p)$ evaluated at prime powers.
  - If RH holds, $\lambda_n \ge 0$ cancels to $O(n \log n)$ because $\lambda_{n,\mathrm{prime}}$ is $O(\sqrt{n}\log n)$ by square-root prime cancellation.
  - If an off-line zero $\rho_0$ with $\operatorname{Re}\rho_0 > 1/2$ exists, $|1 - 1/\rho_0| = 1 + \delta > 1$, so $(1 - 1/\rho_0)^n$ grows **exponentially** as $(1+\delta)^n \cos(n\theta_0)$, making $\lambda_{n,\mathrm{prime}}$ oscillate with amplitude $\pm (1+\delta)^n$!
  - Thus proving $\lambda_n \ge 0$ from the prime side requires proving that the prime Laguerre sum $\sum_{p,k} \frac{\log p}{p^{k/2}} L_{n-1}^{(1)}(k\log p)$ does NOT grow exponentially in $n$—which is equivalent to Wall 1 + Wall 10 (bounding oscillatory prime sums against Laguerre kernels whose stationary phase sits at $k\log p \asymp 4n$).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Completing the explicit finite-$n$ Li-coefficient archimedean-plus-pole closed forms in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Sub-exponential (or polynomial) bounds on the **prime Laguerre sum $\lambda_{n,\mathrm{prime}}$ as $n \to \infty$**, which requires resolving the Oscillation–Transport Dichotomy (Wall 10) and Square-Root Barrier (Wall 1).
- **Dead-End Assessment:** **Asymptotic expansion of the archimedean part $\lambda_{n,\mathrm{arch}} \sim \frac{1}{2}n\log n$ alone is a dead end** because off-line zeros produce exponential $(1+\delta)^n$ oscillations in $\lambda_{n,\mathrm{prime}}$ that swamp $\frac{1}{2}n\log n$.

---

### 16. `SZ` — Suzuki Screw and Shifted-Kernel Limits
- **Route Path & Lean Status:** Screw-function / Lévy–Khintchine representation $g(t) - g(0) = -\int \frac{1-\cos(\gamma t)}{\gamma^2}\,d\mu(\gamma)$ on $[0, 2a]$ $\to$ non-negativity of the second-difference screw kernel $\to$ RH (`riemannHypothesis_iff_suzuki_screw_nonneg`).
- **Hard Obstacles & Why We Failed So Far:**
  - Suzuki's screw function $g(t)$ for $\Xi$ is literally the integrated Weil distribution on $[-t, t]$!
  - Therefore, proving the screw kernel $G(t, s) = g(t-s) - g(t) - g(-s) + g(0)$ is positive-definite on $[0, T]$ for all $T > 0$ is **100% isomorphic** to proving Restricted Weil positivity $E_0(a) \ge 0$ (`RW`) on constant-free test functions (`WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean`).
  - It hits the exact same obstacles as `RW` and `WL`: Wall 11 (`NodeCriticality`), Wall 12 (`ForcedDualMeasure`), and Wall 13 (`ConeMismatch`).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Unifying the `SZ` screw-kernel equivalence with the `RW` and `CHMD` Lévy-jump forms in Lean so all three share one canonical library.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Same as `RW` and `CHMD`: proving positivity of the prime+archimedean-minus-pole form as the horizon $T \to \infty$.
- **Dead-End Assessment:** **Isomorphic to `RW`; not an independent proof mechanism.**

---

### 17. `PM` — Physical-Model Routes (`FZZ-P` Live Route & `PW-B` Candidate Sub-Branch)
- **Route Path & Lean Status:**
  - **Live branch `FZZ-P` (Haar / Báez–Duarte / Selberg-coordinate $L^2$ approximation):** Approximating the constant indicator $\mathbf{1}_{(0,1]}$ in $L^2((0,\infty), dx/x^2)$ by dilates of the sawtooth function $\rho(x) = \{1/x\}$, rewritten in `BezoutValuationIncidence` Selberg/Ramanujan coordinates (`riemannHypothesis_iff_baezDuarte_dist_zero`, `ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean`, `DiscretePrimitiveEnergyAndJordanComparison.lean`, `SharpPrimitiveEnergySuccessorFrontier.lean`).
  - **Candidate sub-branch `PW-B` (Poincaré–Weil / scattering cusp forcing):** Automorphic Eisenstein scattering matrix $\phi(s) = \xi(2s-1)/\xi(2s)$ on $\mathrm{SL}_2(\mathbb{Z})\backslash \mathbb{H}$ $\to$ unitarity/positivity of the truncated Maaß–Selberg inner product on the fundamental domain.
- **Hard Obstacles & Why We Failed So Far:**
  - **In `FZZ-P`:** `BezoutValuationIncidence` diagonalized the finite-period Selberg variance $V(c)$, Bézout successor covariance $C(c)$, and discrete primitive energy $E(c)$ (with Jordan $\varphi_2(q) = q^2\prod(1-p^{-2})$ weights in [DiscretePrimitiveEnergyAndJordanComparison.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/DiscretePrimitiveEnergyAndJordanComparison.lean)), and proved the exact 3-facet universal lower bound $12 E(c) \ge \max(5V+2C, 6V+4C, 6V+12C)$ in [SharpPrimitiveEnergySuccessorFrontier.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SharpPrimitiveEnergySuccessorFrontier.lean).
    - *Why `FZZ-P` is still blocked:* On the periodic cycle $N!$, the discrete primitive energy $E(c)$ grows with $V(c)$, whereas in the Báez–Duarte continuum limit $L^2((0,\infty), dx/x^2)$, one needs the distance from $\mathbf{1}_{(0,1]}$ to the span of $\{\rho(x/k) : 1 \le k \le N\}$ to **converge to $0$** as $N \to \infty$! In the periodic model $N!$, the trans-horizon sawtooth jump discontinuity at multiples of $k > N$ (the inactive sawtooth martingale tail in `ActiveDeletedMartingaleAndShiftedEulerConvergence.lean`) is missing unless $M \to \infty$ is taken *before* $N \to \infty$.
  - **In `PW-B`:** By Lax–Phillips / Colin de Verdière / Zagier Maaß–Selberg relations, the truncated Eisenstein inner product $\langle \Lambda^T E_s, \Lambda^T E_s \rangle \ge 0$ holds on the modular surface $\mathrm{SL}_2(\mathbb{Z})\backslash \mathbb{H}$, **but** the scattering poles of $\phi(s) = \xi(2s-1)/\xi(2s)$ occur at $\rho/2$, so $\operatorname{Re}(\rho/2) = 1/4$ (critical line of $\zeta$) lies **inside the continuous-spectrum strip $\operatorname{Re} s < 1/2$**, where resonant poles of the scattering matrix in $(1/4, 1/2)$ have positive Maaß–Selberg norm only up to an oscillatory $T^{2s-1}$ boundary term at the cusp height $T$!
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing the exact algebraic dictionary between the continuous Báez–Duarte Gram matrix $G_{j,k} = \int_0^\infty \{1/(jx)\}\{1/(kx)\}\,dx/x^2$ and the `BVI` shifted-exponent Ramanujan coordinates (`ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.lean`).
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - For **`FZZ-P`**: Showing that the optimal Báez–Duarte / Selberg-coordinate weights $c_{N,k}$ drive the **full non-periodic $L^2(dx/x^2)$ norm (including the inactive sawtooth tail $x < 1/N$)** to $0$ as $N \to \infty$ (Walls 1, 11).
    - For **`PW-B`**: Eliminating the oscillatory $T^{2s-1}$ cusp-truncation boundary term in the Maaß–Selberg relation at $\operatorname{Re} s \in (1/4, 1/2)$ without assuming zero-freeness (Walls 6, 14).
- **Dead-End Assessment:** **`PW-B` (naive Maaß–Selberg cusp truncation) is a well-known dead end** (Hejhal / Bombieri–Garrett: resonant poles of $\phi(s)$ at $\operatorname{Re} s < 1/2$ do not violate positivity of $\Lambda^T E_s$). **`FZZ-P` via `BVI` remains viable** if the inactive sawtooth tail is coupled to the active shifted-Euler convergence.

---

### 18. `JAS` — Joint Ancestry
- **Route Path & Lean Status:** Common ancestor / joint dilation of the archimedean and prime operators $\to$ joint contractivity/positivity $\to$ RH (`riemannHypothesis_of_joint_ancestry`).
- **Hard Obstacles & Why We Failed So Far:**
  - In `CHMD`, the archimedean jump form $\mathcal{E}_{\mathrm{arch}}$ and prime jump form $\mathcal{E}_{\mathrm{prime}}$ already live on a common Hilbert graph (`CHMDDoobSourceGraph`), and their sum $L = L_{\mathrm{arch}} + L_{\mathrm{prime}}$ is a positive Markov generator.
  - However, by [chmd-revisit.md](file:///Users/michael/Documents/code/hgt/docs/reports/chmd-revisit.md#L444-L445), joint positivity $L \ge 0$ only proves $\mu \le 1$ (the pole is at $s=1$); RH is the **strictly stronger spectral gap $L \ge 1$ on $1^\perp$**, where the negative term $-\operatorname{CoshMass}(v^2)$ must be dominated.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Redirecting `JAS` directly to `CHMDDoobSourceGraph` in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Same as `CHMD`: proving $L \ge 1$ on $1^\perp \cap (\text{signedRadical})^\perp$ (Walls 12, 13).
- **Dead-End Assessment:** **Subsumed by `CHMD`; proving $L \ge 0$ via joint dilation is insufficient because RH requires $L \ge 1$ on $1^\perp$.**

---

### 19. `CTF` — Chronological Tail and Báez–Duarte Approximation
- **Route Path & Lean Status:** Chronological / causal projection in Nyman–Beurling–Báez–Duarte Hilbert space $\mathcal{H} = L^2((0,\infty), dx/x^2)$ $\to$ $d_N^2 = \|\mathbf{1}_{(0,1]} - \sum_{k=1}^N c_k \rho(\cdot/k)\|_{\mathcal{H}}^2 \to 0 \iff \text{RH}$ (`riemannHypothesis_iff_baezDuarte_dist_zero`, `ActiveDeletedMartingaleAndShiftedEulerConvergence.lean`).
- **Hard Obstacles & Why We Failed So Far:**
  - By Báez–Duarte's theorem, for the literal Möbius choice $c_k = \mu(k)$, the indicator cancels on $(1/N, 1]$, leaving only the chronological tail $\int_0^{1/N} \bigl(\sum_{k=1}^N \mu(k)\{1/(kx)\}\bigr)^2 \frac{dx}{x^2}$.
  - Even for literal $c_k = \mu(k)$, the norm does **not** go to $0$ (Burnol proved $\liminf_{N\to\infty} \|\mathbf{1}_{(0,1]} - \sum_{k=1}^N \mu(k)\rho(\cdot/k)\|^2 \ge \sum_\rho \frac{1}{|\rho|^2} > 0$!); one must use **mollified/Selberg-damped weights** $c_{N,k} \approx \mu(k)\bigl(1 - \frac{\log k}{\log N}\bigr)$, and even then $d_N^2$ decays only like $O(1/\log N)$ under RH!
  - In `BezoutValuationIncidence` ([ActiveDeletedMartingaleAndShiftedEulerConvergence.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ActiveDeletedMartingaleAndShiftedEulerConvergence.lean)), we proved that the active martingale jump cancels the active divisor squares 100%, and the active shifted-Euler sum converges at rate $+1/2$, **but** the chronological tail $x \in (0, 1/N)$ (i.e., $M = \lfloor 1/x \rfloor > N$) is governed by the **inactive centered sawtooth martingale drift**, where composite numbers $M > N$ have divisors both $\le N$ and $> N$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing Burnol's lower bound for unmollified $c_k = \mu(k)$ and the Selberg-mollified weight ansatz $c_{N,k} = \mu(k)\frac{\log(N/k)}{\log N}$ in Lean so `CTF` targets the damped weights rather than raw $\mu(k)$.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Proving that for Selberg-damped weights $c_{N,k}$, the **inactive chronological tail integral $\int_0^{1/N} \bigl(\sum_{k=1}^N c_{N,k}\{1/(kx)\}\bigr)^2 \frac{dx}{x^2}$ converges to $0$** as $N \to \infty$ (or even remains bounded, which by weak compactness in Hilbert space already implies $d_N \to 0$!) (Walls 1, 10, 11).
- **Dead-End Assessment:** **Using literal undamped $c_k = \mu(k)$ in Báez–Duarte is a proven dead end (Burnol's theorem: norm stays $\ge \sum 1/|\rho|^2 > 0$).** However, **proving mere uniform $L^2$-boundedness of a point-wise convergent mollified sequence $\sum_{k=1}^N c_{N,k}\rho(\cdot/k)$ on $(0, 1/N)$ is one of the cleanest Hilbert-space formulations of RH** (by Banach–Saks / weak compactness).

---

### 20. `HCF` — Gaussian Heat Trace / Critical Feature Variance
- **Route Path & Lean Status:** Gaussian heat-kernel trace of the explicit formula $\to$ non-negativity / variance bounds across heat scales $\to$ RH (`riemannHypothesis_of_heat_critical_feature_positivity`).
- **Hard Obstacles & Why We Failed So Far:**
  - Evaluated on a single Gaussian $g_\sigma(x) = e^{-x^2/(4\sigma)}$, the Weil explicit formula is trivially positive for small $\sigma$ and dominated by the pole $s=1$ for large $\sigma$.
  - To detect an off-line zero $\gamma_0 = \alpha_0 + i\beta_0$ at height $\alpha_0$, one must modulate the Gaussian by $\cos(\alpha_0 x)$ (or form high-order Hermite/determinantal combinations), which immediately runs into Wall 3 (`ZeroClusteringTuranBarrier`: nearby real zeros around $\alpha_0$ mask the off-line zero unless $\sigma \asymp (\log \alpha_0)^2$, where the prime sum up to $e^{\sigma}$ hits Wall 1) and Wall 13 (`ConeMismatch`).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Connecting `HCF` Gaussian test evaluations to the general `WL` / `CHMD` test-function library in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Overcoming the Gaussian bandwidth vs. prime-horizon trade-off (Walls 1, 3, 13).
- **Dead-End Assessment:** **Single-Gaussian or unmodulated heat-trace inequalities are a dead end**; modulated Gaussian packets are a special case of `WL`.

---

### 21. `XN` — Xi Newton Invariant Discs
- **Route Path & Lean Status:** Newton flow $\dot{z} = -\Xi(z)/\Xi'(z)$ and invariant-disc geometry $\to$ absence of off-real basins $\to$ RH (`riemannHypothesis_of_xi_newton_real_basins`).
- **Hard Obstacles & Why We Failed So Far:**
  - Every simple zero $z_0$ of $\Xi(z)$ (whether real or off-real!) is locally a sink with basin of attraction isomorphic to a disc in $\zeta$-coordinates $\log|\Xi(z)| = \log|\Xi(0)| - t$.
  - Global topological obstructions to off-real basins (via Euler characteristic or separatrices of $\Xi'(z) = 0$) require knowing that critical points $\Xi'(c) = 0$ are real and interlace the zeros—which by Rolle's / Laguerre–Pólya theory is equivalent to real-rootedness of $\Xi$ itself (Wall 4).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing local Newton-basin conformal coordinates in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A global arithmetic constraint on the critical values $\Xi(c)$ at $\Xi'(c) = 0$ that prevents complex saddle connections (Walls 4, 15).
- **Dead-End Assessment:** **High dead-end risk.** Purely complex-dynamical arguments on $\dot{z} = -\Xi/\Xi'$ hold for arbitrary entire functions of order $1$ with complex zeros and cannot see the Euler product of $\zeta(s)$ (Wall 9).

---

### 22. `BAG` — Deterministic Zeta Self-Return (Bagchi Universality)
- **Route Path & Lean Status:** Bagchi's theorem: RH $\iff \zeta(s)$ is strongly recurrent in the strip $1/2 < \operatorname{Re} s < 1$, i.e., $\liminf_{T\to\infty} \frac{1}{T}\int_0^T |\zeta(\sigma+it+i\tau) - \zeta(\sigma+it)|^2\,d\tau = 0$ (`riemannHypothesis_iff_bagchi_self_return`).
- **Hard Obstacles & Why We Failed So Far:**
  - For any finite Dirichlet polynomial $\zeta_N(s) = \sum_{n=1}^N n^{-s}$, self-return $\liminf_{T\to\infty} \frac{1}{T}\int_0^T |\zeta_N(s+i\tau) - \zeta_N(s)|^2\,d\tau = 0$ holds **unconditionally** by Kronecker–Weyl equidistribution of $\{(\tau\log p) \bmod 2\pi\}$ (`Wall 7`).
  - Why doesn't $\zeta_N \to \zeta$ give self-return for $\zeta(s)$? Because for $1/2 < \sigma < 1$, the tail $\zeta(s+i\tau) - \zeta_N(s+i\tau) = \sum_{n > N} n^{-\sigma-it-i\tau}$ converges only conditionally/in $L^2$-mean over *all* $\tau \in [0, T]$ (via Carlson's theorem), **not** when restricted to the thin Kronecker return set $\{\tau : |p^{-i\tau} - 1| < \delta \;\forall p \le P\}$!
  - Conditioning on the small-prime Kronecker phases $p^{-i\tau} \approx 1$ ($p \le P$) biases the distribution of the tail $\sum_{n > N} n^{-s-i\tau}$ unless $N \gg e^P$, where the approximate functional equation requires bounding conditioned short Dirichlet polynomials—the exact Wall 1 / Wall 7 barrier!
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing unconditional Kronecker–Weyl self-return for finite Dirichlet polynomials $\zeta_N(s)$ and unconditional Carlson $L^2$-ergodicity on the unconditioned interval $[0, T]$ in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - **Asymptotic statistical independence between the small-prime Kronecker return set $\{\tau : |p^{-i\tau}-1| < \delta, p \le P\}$ and the high-frequency approximate-functional-equation tail** at $\sigma \in (1/2, 1)$ (Walls 1, 6, 7).
- **Dead-End Assessment:** **Unconditioned $L^2$ mean-value bounds on $[0, T]$ are a dead end** because the Kronecker return set has exponentially small density $\asymp \delta^{\pi(P)}$; any valid proof must control the tail *restricted* to the Kronecker return set.

---

### 23. `EWU` — Even Pole-Weight Uniqueness
- **Route Path & Lean Status:** Even-sector Bochner / Krein / Farkas rigidity $\to$ `WeilPositiveEvenPolar` forces $\lambda = \Lambda$ and RH (`riemannHypothesis_iff_weilPositiveEvenPolar`, `EvenSectorFullPositivity.lean`, `EvenSectorPolarRigidity.lean`, `BiScaleUncertainty` factorial-Müntz and collar modules).
- **Hard Obstacles & Why We Failed So Far:**
  - As reviewed in [ewu-review.md](file:///Users/michael/Documents/code/hgt/docs/reports/ewu-review.md) and [chmd-revisit.md](file:///Users/michael/Documents/code/hgt/docs/reports/chmd-revisit.md#L370-L382), `EWU` proves that *if* the Weil functional is non-negative on even polar-null tests (`WeilPositiveEvenPolar`), *then* Bochner's theorem gives a positive cosine-shift spectral measure $\nu_S \ge 0$, and the twisted-arc null identity kills off-line spectrum $\rho^2 \le 2$.
  - However, **producing** `WeilPositiveEvenPolar` from the prime-blind archimedean side (`ArchimedeanNonnegOnEvenPolarNonnegCone`) hits four proven obstructions in `BiScaleUncertainty`:
    1. `FactorialBiNullObstruction`: Factorial bi-null and causal-tent profiles are differences of two autocorrelations, not single autocorrelations (Wall 13).
    2. `FactorialPolarGramScaleSeparation`: The polar loss $\frac{1}{4}\frac{\log(n+2)}{n+1}$ dominates the off-diagonal Gram coupling $o(1/(n+1))$ by $\log n$.
    3. `FactorialMuntzTailWeilGrowth`: Canonical polar-repaired factorial tails have positive Weil energy $\ge \frac{\log(n+1)}{2048(n+1)} > 0$ **unconditionally**, so they are RH-nonselective!
    4. `EvenSectorBlindGroundShiftInvariance`: Subtracting $m(a)\|Ju\|^2$ cancels constant shifts $C$ identically on the form domain.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Constructing the concrete even-polar de Branges ground operator on finite windows and proving general-grid collar optimizer attainment in Lean (explicitly noted as engineering tasks in `ewu-review.md`).
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **genuine prime-blind single-autocorrelation coercivity bound** on the quotient modulo `signedRadical` that dominates the polar loss $2|\widehat{F}(i/2)|^2$ without relying on difference-of-autocorrelation causal tents or shift-blind ground operators (Walls 11, 12, 13).
- **Dead-End Assessment:** **The Farkas dual-cone and factorial-Müntz / causal-tent producer sub-programmes inside `EWU` are proven dead ends** (`FactorialBiNullObstruction`, `FactorialPolarGramScaleSeparation`, `FactorialMuntzTailWeilGrowth`). Only direct coercivity on the `CHMD` quotient space survives.

---

### 24. `GTA` — Transverse Schur Charge
- **Route Path & Lean Status:** Cayley transform of $-\xi'/\xi$ into a Schur function $\Theta_{\mathrm{Schur}}(s)$ on $\operatorname{Re} s > 1/2$ $\to$ positive de Branges–Rovnyak reproducing kernel $\frac{1 - \Theta(s)\overline{\Theta(w)}}{s + \bar{w} - 1} \ge 0 \iff \text{RH}$ (`riemannHypothesis_iff_schur_pick_positivity`).
- **Hard Obstacles & Why We Failed So Far:**
  - By Pick–Nevanlinna theory, positivity of the de Branges–Rovnyak kernel on $\operatorname{Re} s > 1/2$ is algebraically equivalent to $\operatorname{Re}(-\xi'/\xi(s)) \ge 0$ (`PA`), and after Fourier transform against compactly supported test functions, is equivalent to Weil positivity (`WL` / `RW`).
  - Evaluating the Pick matrix on finite point sets $\{s_1, \dots, s_m\}$ in the strip $\frac{1}{2} < \operatorname{Re} s_j \le 1$ cannot be done from the Euler product alone because the Euler product diverges for $\operatorname{Re} s_j \le 1$ (Wall 6).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Completing the formal Pick-matrix $\leftrightarrow$ Herglotz-passivity (`PA`) $\leftrightarrow$ Weil-positivity (`WL`) equivalence triangle in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Same as `PA` and `WL`: an arithmetic certificate of Pick-kernel positivity inside the critical strip $\frac{1}{2} < \operatorname{Re} s < 1$ (Walls 6, 12, 13).
- **Dead-End Assessment:** **Purely a Cayley-transform coordinate change of `PA` and `WL`; offers no independent escape from Walls 6 and 12.**

---

### 25. `OWU` — Odd Weil-Weight Uniqueness
- **Route Path & Lean Status:** Odd-sector antisymmetric prime-blind tests (`PrimeBlindPositiveOddAt β`) & parity-joint rigidity $\to$ kills off-line zero at imaginary depth $\beta \in (0, 1/2)$ $\to$ RH (`riemannHypothesis_of_primeBlindPositiveOddAt`, `ParitySectorJointRigidity.lean`, `BiScaleUncertainty` Nyquist/polar-escape modules).
- **Hard Obstacles & Why We Failed So Far:**
  - As documented in [owu-review.md](file:///Users/michael/Documents/code/hgt/docs/reports/owu-review.md), `OWU` eliminates the $s=1$ pole linearly on odd functions because $\sinh(x/2)$ vs. $\cosh(x/2)$ parity separates the linear pole functional (`odd_polar_null`), and `ParitySectorJointRigidity` shows that combining even and odd sectors pins $\lambda = \Lambda$.
  - **Why `OWU` is still blocked:**
    1. *Linear vs. Quadratic Pole Confusion (`chmd-revisit.md` Hole 2):* In the quadratic energy form, an odd test $v(-x) = -v(x)$ has **even** square $v(x)^2 \ge 0$, so the negative quadratic pole potential $-\int \Theta(x)\cosh(x/2)v(x)^2\,dx < 0$ **does NOT vanish on the odd sector**!
    2. *Nyquist Polar Escape (`NyquistPolarSourceEscape.lean`, `DistantCopySharpness.lean`):* In `BiScaleUncertainty`, sequences of polar-balanced odd/distant-copy profiles can converge weakly or in correlation to non-polar limits, escaping finite-window collar bounds.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Unifying the `OWU` odd-sector receiver with `CHMDOddSectorCriterion.lean` (`riemannHypothesis_iff_no_odd_bound_state` and `riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare`).
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Proving the **odd-sector Dirichlet–Poincaré inequality $\mathcal{E}_{\mathrm{arch}}(v) + \mathcal{E}_{\mathrm{prime}}(v) \ge \int \Theta(x)\cosh(x/2)v(x)^2\,dx$** on odd tests $v$ orthogonal to `signedRadical`, using the origin-crossing prime-chain variance factorization (`CHMDPrimeChainSourceFactorization.lean`) (Walls 9, 11, 13).
- **Dead-End Assessment:** **Viable when merged with `CHMD`'s odd-sector Poincaré criterion (`CHMDOddSectorCriterion.lean`), where the linear pole $1$ is automatically orthogonal to odd $v$.** However, assuming oddness kills the *quadratic* pole mass $\operatorname{CoshMass}(v^2)$ is a proven mathematical error.

---

### 26. `PBM` — Prime Boundary Monodromy (Regularized $\log\zeta$ Abscissa)
- **Route Path & Lean Status:** Analytic continuation / abscissa of regularity of regularized $\log \zeta(s)$ (or prime Dirichlet series $\sum p^{-s}$) down to $\sigma = 1/2$ $\to$ absence of branch points in $\operatorname{Re} s > 1/2 \iff \text{RH}$ (`riemannHypothesis_iff_log_zeta_regular_abscissa`).
- **Hard Obstacles & Why We Failed So Far:**
  - Every zero $\rho_0$ of $\zeta(s)$ is a logarithmic branch point with monodromy $+2\pi i m_{\rho_0}$ for $\log \zeta(s)$.
  - However, by Wall 1 (`SquareRootBarrier`) and Wall 6 (`ProbabilityCone`), the prime Dirichlet series $P(s) = \sum_p p^{-s}$ has a natural boundary at $\operatorname{Re} s = 0$ and logarithmic singularities at every $\rho/k$ ($k \ge 1$) via $\log \zeta(s) = \sum_{k=1}^\infty \frac{1}{k} P(ks)$. Showing $P(s)$ (after subtracting $\frac{1}{k}\log\frac{1}{ks-1}$) is holomorphic on $\operatorname{Re} s > 1/2$ is equivalent by Landau/Mellin inversion to $\pi(x) - \operatorname{li}(x) = O(x^{1/2+\varepsilon})$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing the Möbius-inversion identity $P(s) = \sum_{k=1}^\infty \frac{\mu(k)}{k}\log \zeta(ks)$ on $\operatorname{Re} s > 1$ and its strip continuation under zero-freeness in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Cancellation in the partial sums $\sum_{p \le x} p^{-s}$ for $\frac{1}{2} < \operatorname{Re} s \le 1$, which is literally Wall 1.
- **Dead-End Assessment:** **Direct restatement of Wall 1 in Dirichlet-series abscissa language; no independent analytic mechanism.**

---

### 27. `RB` — Robin / Nicolas Divisor-Sum Criterion
- **Route Path & Lean Status:** Robin's inequality $\sigma(n) < e^\gamma n \log\log n$ for all $n > 5040$ (or Nicolas's Euler-totient / colossally abundant criterion $N_k / \varphi(N_k) > e^\gamma \log\log N_k$) $\iff \text{RH}$ (`riemannHypothesis_iff_robin_inequality`, `riemannHypothesis_iff_nicolas_criterion`).
- **Hard Obstacles & Why We Failed So Far:**
  - Robin's inequality is proved unconditionally for huge classes of integers (squarefree, odd, $5$-free, $7$-free, non-superabundant, and for all $n$ unless $n$ lies between two consecutive colossally abundant numbers near a massive Chebyshev $\theta(x) - x$ oscillation).
  - However, at colossally abundant / primorial numbers $N_k = \prod_{p \le x} p^{a_p}$, $\log \frac{\sigma(N_k)}{N_k} - \gamma - \log\log N_k$ expands via Mertens' third theorem into $\frac{\theta(x) - x}{x \log x} + O\bigl(\frac{1}{x}\bigr)$.
  - By Littlewood's theorem, $\theta(x) - x$ changes sign infinitely often with amplitude $\Omega_\pm(x^{1/2}\log\log\log x)$. If RH is false with supremum of real parts $\Theta_0 > 1/2$, then $\theta(x) - x = \Omega_\pm(x^{\Theta_0})$, which violates Robin's inequality at infinitely many primorial scales $x$, whereas proving Robin's inequality for **all** colossally abundant $N_k$ requires bounding the positive peaks of $\theta(x) - x$ by $\le c x^{1/2}$—which is Wall 1 + Wall 3!
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Formalizing the reduction of Robin's inequality from all $n > 5040$ to the sparse sequence of colossally abundant numbers in Lean.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - Bounding the one-sided Chebyshev oscillation $\theta(x) - x \le c x^{1/2}$ at primorial scales $x \to \infty$ (Walls 1, 3).
- **Dead-End Assessment:** **Case-by-case divisor checks (odd $n$, $k$-free $n$, bounded $\omega(n)$) are a 100% proven dead end** because the RH equivalence lives exclusively on colossally abundant numbers $N_k$ where $\omega(N_k) \to \infty$.

---

## Part III: The 18 Route Candidates (`docs/reports/rh-current-frontier-map.md`)

In [rh-current-frontier-map.md](file:///Users/michael/Documents/code/hgt/docs/reports/rh-current-frontier-map.md), the 18 Route Candidates are separated from Live Routes because they either (i) still depend on pre-divisor / zero-indexed spectral data before landing on a zero-free arithmetic object, or (ii) have an incomplete Lean bridge to `RiemannHypothesis`. Below we list both their **"Just Work" landing/formalization obstacles** and the **uncharted mathematical obstacles** that remain once landed, along with which candidates are structural dead ends.

---

### 1. `APF` — Arithmetic Paired Fredholm
- **Concept:** Regularized Fredholm determinant $\det_2(I - K_s)$ of a paired prime–archimedean Hilbert–Schmidt operator reproducing $\xi(s)$.
- **Hard Obstacles & Why We Failed So Far:**
  - By Wall 14 (`SizeLawObstruction`), the prime shift operator is not Hilbert–Schmidt or trace-class relative to the archimedean generator on unweighted $L^2(\mathbb{R})$.
  - Even if weighted by $\Theta(x)\cosh(x/2)$ (as in `CHMD`), $\det_2(I - \mu^{-1} R)$ simply reproduces the entire function $\Xi(z)$ via Hadamard's product; proving its zeros lie in $\mu \le 1/2$ still requires proving $\lambda_1(L) \ge 1$ on $1^\perp$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing the Hilbert–Schmidt trace of $R^2 = (1+L)^{-2}$ on `CHMDDoobSourceGraph` (`R` is already proved compact in `CHMDCompactResolvent.lean`).
  - **(B) Requires New Mathematics:** Same as `CHMD` ($\lambda_1(L) \ge 1$ on $1^\perp$).
- **Dead-End Assessment:** **Unweighted Fredholm determinants are a dead end (Wall 14); $\Theta$-weighted Fredholm determinants are redundant with `CHMD`.**

---

### 2. `BSH` — Arithmetic Mate Curvature
- **Concept:** Differential-geometric curvature of the conjugate/mate harmonic function associated with $\Xi(z)$ on the upper half-plane.
- **Hard Obstacles & Why We Failed So Far:**
  - By Wall 4 (`AxisOutsideZeroSet`) and Wall 15 (`SupportVsPositivity`), Gaussian curvature of $\log|\Xi(z)|$ is zero away from zeros and $-\infty$ (Dirac delta) at every zero regardless of whether the zero is real or complex.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing harmonic-mate Cauchy–Riemann identities in Lean.
  - **(B) Requires New Mathematics:** A global boundary-to-interior curvature inequality that distinguishes real zeros from off-real zeros using the Euler product (Walls 4, 9, 15).
- **Dead-End Assessment:** **Likely dead end.** Local differential geometry of $\Xi(z)$ is blind to the Euler product (Wall 9).

---

### 3. `BVI` — Bézout–Valuation Incidence
- **Concept:** The 40-module Lean framework ([BezoutValuationIncidence.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence.lean)) combining Selberg LCM divisibility with Bézout successor coprimality $\gcd(a, b) \mid 1$, valuation visibility clocks $q/\operatorname{rad}(q)$, and active/inactive sawtooth martingales.
- **Hard Obstacles & Why We Failed So Far:**
  - Detailed in the Executive Diagnostic above:
    1. Pronic pairs annihilate prime powers ($\Lambda(d_1 d_2) = 0$ for $\gcd(d_1,d_2)=1, d_i \ge 2$).
    2. Universal inequalities in $(V, C, E)$ are exhausted by modes $\{1,2,3,4,6\}$ (`SharpPrimitiveEnergySuccessorFrontier.lean`).
    3. One-step successor prediction loses $\ge 3/4$ of variance above parity (`SharpSuccessorPhaseLossAndClosureClassification.lean`).
    4. True $h$-lag translation requires consecutive lags up to $N/2$ to see high prime powers $2^k$ (`ArithmeticLagSchedulesAndSharpRecoveryHorizon.lean`).
    5. Renormalized defect non-positivity holds only sub-horizon ($M+1 \le N$), while trans-horizon ($M \gg N$) leaves the **inactive centered sawtooth martingale drift** uncancelled (`ActiveDeletedMartingaleAndShiftedEulerConvergence.lean`).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):**
    1. Syncing `rh-current-frontier-map.md` (which still marks `ShiftedExponentAsymptoticDensityAndActiveMartingaleRate` as `[S]` and omits the 9 newest `[L]` modules already imported in `BezoutValuationIncidence.lean`).
    2. Replacing the `Littlewood_converse` hypothesis parameter in `PowerSavingIncrementCriterion.lean` with the unconditional Mellin–Landau bridge.
  - **(B) Requires New Mathematics Nobody Has Yet:**
    - A **trans-horizon multi-lag incidence identity** that bounds the inactive sawtooth martingale drift across $N < M \le N^2$ by combining Buchstab prime-factorization decomposition with the true-lag Ramanujan visibility schedule (Walls 1, 10, 11).
- **Dead-End Assessment:** **High-value active engine for `MC` and `CTF`, NOT a dead end**—provided we stop looking for universal inequalities in $(V, C, E)$ for arbitrary weights $c$ (which are proven sharp on $\{1,2,3,4,6\}$) and instead exploit the multiplicative Buchstab structure of the specific weight $c = \mu$ in the trans-horizon regime $M > N$.

---

### 4. `CDC` — Constitutive Dagger
- **Concept:** Non-self-adjoint / Krein-space $\dagger$-involution coupling between forward and backward arithmetic shifts.
- **Hard Obstacles & Why We Failed So Far:**
  - Hits Wall 12 (`ForcedDualMeasure`) and Wall 15 (`SupportVsPositivity`): any Krein-space $\dagger$-positivity statement is algebraically equivalent to the Weil quadratic form being positive on the quotient space.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Wiring the Krein $\dagger$-adjoint definitions into `CHMD` and `WL`.
  - **(B) Requires New Mathematics:** Eliminating negative-norm Krein eigenvectors (`imVector` of off-line zeros) via multiplicative structure.
- **Dead-End Assessment:** **Redundant wrapper around `WL` / `CHMD`; dead end as an independent route.**

---

### 5. `DR` — Dyadic Xi Roots
- **Concept:** Dyadic frequency decomposition of $\Xi(t)$ and root-counting in dyadic intervals $[2^k, 2^{k+1}]$.
- **Hard Obstacles & Why We Failed So Far:**
  - Hits Wall 1 (`NyquistBandwidthRigidity`) and Wall 3 (`ZeroClusteringTuranBarrier`): isolating roots in dyadic frequency bands $[2^k, 2^{k+1}]$ requires prime sums up to $e^{2^k}$ and cannot prevent local zero pairs from splitting horizontally by $\pm \delta$ without sub-unit resolution.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing dyadic Littlewood–Paley partition-of-unity bounds for $\Xi(t)$ in Lean.
  - **(B) Requires New Mathematics:** Sub-unit horizontal zero localization at dyadic height $2^k$ (Walls 1, 3).
- **Dead-End Assessment:** **Likely dead end** due to Nyquist exponential prime horizon $e^{2^k}$.

---

### 6. `EGC` — Pole-Safe Contour
- **Concept:** Contour integration of $-\zeta'/\zeta$ or $\Xi'/\Xi$ along pole-avoiding kernels that cancel the $s=1$ residue identically.
- **Hard Obstacles & Why We Failed So Far:**
  - Cancelling the $s=1$ pole linearly (e.g., via $\widehat{F}(i/2) = 0$ or finite differences $\Delta_h$) is easy and already done in `EWU`/`OWU`/`CHMD`.
  - However, by `CompactTestXiDivisibility` (`STATUS.md`) and `chmd-revisit.md` Hole 2, killing the *linear* pole $\widehat{F}(i/2) = 0$ on $f$ does not kill the *quadratic* pole $|\widehat{f}(i/2)|^2$ unless $\widehat{f}(i/2) = 0$ (which happens automatically on odd $f$), and even on odd $f$ in $\Theta$-Doob coordinates, the quadratic pole mass $-\int \Theta\cosh(x/2)v^2\,dx$ remains strictly negative!
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing explicit pole-free contour shift identities in Lean.
  - **(B) Requires New Mathematics:** Bounding the zero-sum residue $\sum_\rho \widehat{F}(\gamma_\rho)$ after pole cancellation, which is Wall 1 / Wall 12.
- **Dead-End Assessment:** **Linear pole cancellation alone is a solved triviality (`odd_polar_null`); `EGC` has no independent producer mechanism beyond `EWU`/`OWU`/`CHMD`.**

---

### 7. `EWJ` — Euler/Wold Jets
- **Concept:** Wold decomposition (innovation / moving-average representation) of arithmetic sequences and finite Taylor/Euler jets.
- **Hard Obstacles & Why We Failed So Far:**
  - In `BezoutValuationIncidence` ([OptimalSuccessorPredictionAndExactPhaseLoss.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/OptimalSuccessorPredictionAndExactPhaseLoss.lean) and [SharpSuccessorPhaseLossAndClosureClassification.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SharpSuccessorPhaseLossAndClosureClassification.lean)), we explicitly computed the one-step Wold innovation of divisor-sieve sequences under $k \mapsto k+1$: the innovation loses between $3/4$ and $100\%$ of all variance above parity at every single step (`successorPhaseLoss_bounds`)!
  - Because one-step compression does not commute with $h$-step translation (`TrueTranslationPredictionAndExactCompression.lean`), a Markovian/Wold 1-step jet forgets prime-power phases exponentially fast ($4^{-m}$).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Connecting `EWJ` Wold-innovation definitions to `OptimalSuccessorPredictionAndExactPhaseLoss.lean` and `TrueTranslationPredictionAndExactCompression.lean`.
  - **(B) Requires New Mathematics:** A **non-Markovian multi-lag Wold memory functional** over full visibility schedules $H$ (`ArithmeticLagSchedulesAndSharpRecoveryHorizon.lean`) that controls trans-horizon residuals.
- **Dead-End Assessment:** **1-step Markovian Wold jets are a 100% proven dead end** (`SharpSuccessorPhaseLossAndClosureClassification.lean`: $\ge 3/4$ variance loss per step above parity).

---

### 8. `FEL` — Theta Likelihood
- **Concept:** Information-theoretic / Fisher-information / log-likelihood convexity of the normalized theta/xi distribution.
- **Hard Obstacles & Why We Failed So Far:**
  - Hits Wall 2 (`JensenGap` / BSY integral) and Wall 6 (`ProbabilityCone`): $\Xi(t)$ oscillates in sign on $\mathbb{R}$, so $|\Xi(t)|^2$ is non-negative, but its log-likelihood $\log|\Xi(t)|^2$ has $-\infty$ singularities at every real zero and concave Jensen inequality in the wrong direction.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing the Fisher-information / Stam-inequality identities for heat-smoothed $\Theta_t$ in Lean.
  - **(B) Requires New Mathematics:** Reverse-Jensen / entropy bound across oscillatory sign changes (Walls 2, 4).
- **Dead-End Assessment:** **High dead-end risk** (Wall 2 + Wall 4: heat-smoothed Fisher information monotonicity is equivalent to de Bruijn–Newman forward flow, which goes in the trivial direction $\Lambda_{\mathrm{dBN}}$ shrinking).

---

### 9. `HJ` — Hurwitz Reflection
- **Concept:** Embedding $\zeta(s) = \zeta(s, 1)$ into the Hurwitz family $\zeta(s, a) = \sum_{n=0}^\infty (n+a)^{-s}$ ($0 < a \le 1$) and using the differential-difference shift $\partial_a \zeta(s, a) = -s\zeta(s+1, a)$ + reflection at $a = 1/2, 1$.
- **Hard Obstacles & Why We Failed So Far:**
  - By Davenport–Heilbronn, $\zeta(s, a)$ has **infinitely many off-line zeros in $\frac{1}{2} < \operatorname{Re} s < 1$** for every rational or transcendental $a \notin \{1/2, 1\}$!
  - Why? Because $\zeta(s, a)$ lacks an Euler product for $a \notin \{1/2, 1\}$. Thus any differential identity in $a \in (0, 1)$ passes continuously through functions that **violate RH**, and at the special endpoints $a = 1$ ($\zeta(s)$) and $a = 1/2$ ($(2^s-1)\zeta(s)$), the $a$-derivative $\partial_a \zeta(s, 1) = -s(\zeta(s+1)-1)$ simply shifts $s \mapsto s+1$ without closing a self-contained equation on $\operatorname{Re} s = 1/2$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing the Hurwitz shift identity $\zeta(s, a) - \zeta(s, a+1) = a^{-s}$ and reflection formula at $a = 1/2, 1$ in Lean.
  - **(B) Requires New Mathematics:** An **Euler-product compatibility filter at $a \in \{1/2, 1\}$** that explains why the Davenport–Heilbronn off-line zeros of $\zeta(s, a)$ must exit the strip as $a \to 1^-$ (or annihilate in the Dirichlet character decomposition at rational $a = r/q$).
- **Dead-End Assessment:** **Purely analytic $a$-transport in $\zeta(s, a)$ without multiplicative projection at $a = 1/2, 1$ is a proven dead end** (Davenport–Heilbronn theorem).

---

### 10. `IRK` — Rotation-Algebra Trace
- **Concept:** Non-commutative torus / irrational rotation $C^*$-algebra $A_\theta$ traces at $\theta = \log p / \log q$.
- **Hard Obstacles & Why We Failed So Far:**
  - The canonical trace $\tau$ on $A_\theta$ only reads the $(0,0)$ Fourier mode, which is linear and commutative on diagonal elements, while coupling all primes $\log p$ simultaneously requires the infinite tensor product $\bigotimes_p A_{\log p}$ (the Bost–Connes algebra), where KMS positivity holds only for $\beta > 1$ (Wall 6) and trace-class perturbations fail at $\beta = 1/2$ (Wall 14).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing two-prime rotation-algebra commutator traces in Lean.
  - **(B) Requires New Mathematics:** A positive trace/state on the critical-line representation ($\beta = 1/2$) that survives Wall 6 and Wall 14.
- **Dead-End Assessment:** **Likely dead end** unless reduced to `CHMD`'s concrete Hilbert graph.

---

### 11. `MSC` — Möbius–Sonin Transport
- **Concept:** Sonin's spaces of functions whose Fourier/Mellin transforms vanish on intervals $[-a, a]$, combined with Möbius inversion to annihilate the pole and low primes.
- **Hard Obstacles & Why We Failed So Far:**
  - Sonin spaces are de Branges spaces (isomorphic to the prime-blind collar spaces in `RW`, `EWU`, and `BiScaleUncertainty`).
  - Transporting Möbius weights through the Sonin Bessel/cosine kernel hits Wall 10 (`OscillationTransportDichotomy`) and `BiScaleUncertainty`'s `InfiniteGridStrictEnergyLoss` (origin-concentration defect).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Connecting `MSC` Sonin-space definitions to `BiScaleUncertainty`'s Krein collar transport modules in Lean.
  - **(B) Requires New Mathematics:** Same as `RW`/`EWU`: overcoming `FactorialPolarGramScaleSeparation` and `InfiniteGridStrictEnergyLoss` (Walls 10, 11, 13).
- **Dead-End Assessment:** **Subsumed by `RW` / `EWU` / `BiScaleUncertainty`.**

---

### 12. `PCS` — Singular Co-Shift
- **Concept:** Adjoint/co-shift operator of the multiplicative-to-additive dilation semigroup on Hardy/Bergman spaces.
- **Hard Obstacles & Why We Failed So Far:**
  - By Beurling–Lax theorem, invariant subspaces of the multiplicative shift $S_n f(x) = f(nx)$ on $H^2$ correspond to inner factors of Dirichlet series (`CTF` / Báez–Duarte in Mellin space).
  - Proving the co-shift $S^*$ is cyclic on the pole-free subspace is equivalent by duality to the Nyman–Beurling–Báez–Duarte density criterion (`CTF`), hitting Wall 1 and Wall 2 (inner Blaschke factors have boundary modulus $1$).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing the Mellin isometry between `PCS` co-shift cyclicity and `CTF` Báez–Duarte density in Lean.
  - **(B) Requires New Mathematics:** Same as `CTF` and Wall 2: ruling out nontrivial inner Blaschke factors in $\operatorname{Re} s > 1/2$.
- **Dead-End Assessment:** **Dual restatement of `CTF` and Wall 2; no independent producer advantage.**

---

### 13. `PTR` — Photonic Source
- **Concept:** Waveguide / Maxwell-type first-order Dirac system for the CHMD Klein–Gordon wave $(\partial_y^2 - \partial_x^2 + 2)u = 0$.
- **Hard Obstacles & Why We Failed So Far:**
  - As proved in [chmd-revisit.md](file:///Users/michael/Documents/code/hgt/docs/reports/chmd-revisit.md#L370-L382) (`Hole 4`), the CHMD Klein–Gordon wave $\cos(y\sqrt{z^2+2})$ has mass-squared $+2$, so critical-line zeros ($z \in \mathbb{R}$) have $\rho^2 = z^2 + 2 \ge 2$, while hypothetical extreme off-line zeros near $s=1$ have $\rho^2 \in (1, 2)$.
  - However, the classical wave energy $\int (|\partial_y u|^2 + |\partial_x u|^2 + 2|u|^2)\,dx$ is conserved and positive for **every** wave solution; to couple it to the primes, one must evaluate the wave against the Weil functional $L_\lambda$, where concluding $\nu_S(\{\rho^2 \le 2\}) = 0$ via `EvenSectorTwistedArcNull.lean` **already requires assuming $L_\lambda \ge 0$ (`WeilPositiveEvenPolar`) first**!
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Unifying `PTR` with `EvenSectorCosineBochner.lean` and `EvenSectorTwistedArcNull.lean`.
  - **(B) Requires New Mathematics:** Proving positivity of the Weil pairing *before* applying `EvenSectorTwistedArcNull` (Walls 12, 13, 15).
- **Dead-End Assessment:** **Proven circular (`chmd-revisit.md` Hole 4) if used without an independent proof of `WeilPositiveEvenPolar`.**

---

### 14. `RFHM` — Support Grade
- **Concept:** Graded filtration of the test-function support by prime-power log-lattice thresholds $\log 2 < \log 3 < \log 4 < \log 5 < \dots$.
- **Hard Obstacles & Why We Failed So Far:**
  - Directly confronts Wall 11 (`PrimeBlindNodeCriticality`): at each threshold $2a = k\log p$, a new prime-power jump enters the quadratic form, and on the critical band (`signedRadical`) the form has zero slack at every grade.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing the finite-grade jump-increment recurrence across consecutive prime-power thresholds $k\log p$ in Lean.
  - **(B) Requires New Mathematics:** Proving by induction or asymptotic coupling across grades that each newly activated prime-power jump $\frac{\log p}{p^{k/2}}(v(x)-v(x+k\log p))^2$ compensates for the incremental growth of $\int_{-a}^a \Theta(x)\cosh(x/2)v(x)^2\,dx$ on the quotient modulo `signedRadical` (Walls 9, 11).
- **Dead-End Assessment:** **Useful structural lens on `RW` and `CHMD`, provided all prime powers $p^k$ (not just primes $p$) are included in the filtration (Wall 11).**

---

### 15. `SC` — Stokes / Witt–Krein
- **Concept:** Witt-vector Ghost/Frobenius/Verschiebung operators $F_p, V_p$ ($F_p V_p = p$) coupled to a Stokes/Krein boundary pairing.
- **Hard Obstacles & Why We Failed So Far:**
  - Over the big Witt ring $W(R)$, $F_n V_n = n$ encodes the exact divisor-sum / ghost-map relation (`selbergMultiplesCoord` in `BVI`!), and $V_p^* F_q = \gcd(p, q)$ on coprime modes.
  - However, turning Witt-vector algebra into a Hilbert-space inequality for $\zeta(s)$ requires choosing a norm on $W(\mathbb{R})$ that couples the discrete multiplicative index $n$ to the continuous archimedean scale $\log n$ (Wall 5: `NoFrobeniusNoF1`).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing the isomorphism between the Witt-vector ghost/Frobenius/Verschiebung algebra on $\{1, \dots, N\}$ and the `BezoutValuationIncidence` Selberg/Ramanujan coordinates (`selbergMultiplesCoord`, `sieveLagMultiplier`).
  - **(B) Requires New Mathematics:** Coupling the Witt/BVI discrete incidence algebra to the continuous archimedean scale (Walls 5, 11).
- **Dead-End Assessment:** **Abstract Witt-ring algebra alone is a dead end (Wall 5), but when identified with `BVI` + `CHMDPrimeChainVariance`, it is part of the core multiplicative engine.**

---

### 16. `SEC` — Adjacent Prime Seam
- **Concept:** Seam/interface boundary conditions between adjacent prime intervals $[p_k, p_{k+1}]$ or adjacent pronic windows $[M(M-1), M(M+1)]$.
- **Hard Obstacles & Why We Failed So Far:**
  - In `BezoutValuationIncidence` ([ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean) and [PowerDampedRenormalizedDefectAndPronicCeiling.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PowerDampedRenormalizedDefectAndPronicCeiling.lean)), the discrete boundary seam term at $M+1$ is $+\frac{1}{2}(g_N(M+1)^2 - 1)$.
  - For $M+1 \le N$, $g_N(M+1) = 0$ so the seam term is $-1/2 < 0$ (favorable!). For $M+1 > N$, $g_N(M+1)$ can be strictly greater than $1$ on composite numbers with multiple prime factors $> N$, making the seam term positive and uncancelled.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Merging `SEC` with `ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean` in Lean.
  - **(B) Requires New Mathematics:** Controlling the trans-horizon boundary seam $g_N(M+1)^2 - 1$ for $M+1 > N$ (Wall 1).
- **Dead-End Assessment:** **Subsumed by `BVI` / `MC`.**

---

### 17. `W1C` — Clifford–Dirac / Centred Lee–Yang
- **Concept:** Rewriting $\Xi(z)$ or its finite Euler/Jensen approximations as a Lee–Yang partition function (or Clifford–Dirac determinant) whose zeros lie on the unit circle / real line by Lee–Yang ferromagnetic circle theorems.
- **Hard Obstacles & Why We Failed So Far:**
  - The classical Lee–Yang theorem requires ferromagnetic pairwise couplings $J_{ij} \ge 0$.
  - For $\Xi(t) = \int_0^\infty \Phi(x)\cos(tx)\,dx$, Newman proved that $\Phi(x)$ is a limit of Lee–Yang measures at $\Lambda_{\mathrm{dBN}} = -\infty$, **not** necessarily at $\Lambda_{\mathrm{dBN}} = 0$ (Wall 4: backward heat flow kills ferromagnetic positivity of couplings).
  - If instead one uses the Euler product $\prod_p (1 - p^{-s})^{-1}$, the prime phases $p^{-it}$ have incommensurate frequencies $\log p$, and for $\operatorname{Re} s < 1$ the pole $s=1$ introduces an antiferromagnetic / negative mode (`CoshMass`) that violates Lee–Yang ferromagnetism (Walls 6, 8, 13).
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Formalizing finite-spin Lee–Yang circle theorem certificates in Lean.
  - **(B) Requires New Mathematics:** A **frustration-free / pole-deflated Lee–Yang theorem** on $1^\perp$ that survives an antiferromagnetic ground-state subtraction (Walls 4, 6, 13).
- **Dead-End Assessment:** **Standard ferromagnetic Lee–Yang circle theorems are a proven dead end for $\zeta(s)$** because the $s=1$ pole introduces a mandatory negative (antiferromagnetic) mode.

---

### 18. `WBF` — Source Certificates
- **Concept:** Finite-level linear-programming / SOS (sum-of-squares) source certificates for prime-blind positivity (`PrimeBlindLevelCertificateSqueeze.lean`, `CHMDCardinalOperatorAction.lean`).
- **Hard Obstacles & Why We Failed So Far:**
  - As exposed in [chmd-revisit.md](file:///Users/michael/Documents/code/hgt/docs/reports/chmd-revisit.md#L356-L366) (`Hole 3`), `exists_level_forall_levelCertificates_abs_sub_lt` in [PrimeBlindLevelCertificateSqueeze.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindLevelCertificateSqueeze.lean) is true unconditionally **only because if RH were false, $\operatorname{levelCertificates}(L)$ would be the empty set $\emptyset$ for all large $L$**, making $\forall \mu \in \emptyset, |\mu(n) - \Lambda(n)| < \varepsilon$ vacuously true!
  - Proving that $\operatorname{levelCertificates}(L) \ne \emptyset$ for all $L$ is literally equivalent to RH (`riemannHypothesis_iff_forall_levelCertificates_nonempty`), and by Wall 8 (`InfinitesimalAdmixture`), any sequence $\mu_L \in \operatorname{levelCertificates}(L)$ is forced to converge pointwise to $\Lambda(n)$.
- **Obstacle Split:**
  - **(A) Solvable ("Just Work"):** Adding explicit non-emptiness certificates for small finite levels $L \le L_0$ where only the first few prime powers enter.
  - **(B) Requires New Mathematics:** Proving $\operatorname{levelCertificates}(L) \ne \emptyset$ for all $L \to \infty$ by explicitly using $\mu_L = \Lambda$ and proving primal positivity on `SourceGraph ⧸ signedRadical` (Walls 8, 11, 12).
- **Dead-End Assessment:** **Trying to construct "easier" smooth certificates $\mu_L \ne \Lambda$ for large $L$ is a 100% proven dead end** (`PrimeBlindLevelCertificateSqueeze.lean`: $\operatorname{levelCertificates}(L)$ squeezes to the singleton $\{\Lambda\}$).

---

## Summary Ledger: Which Routes Are Structural Dead Ends vs. Active Frontiers

| Category | Routes / Sub-Branches | Verdict |
| :--- | :--- | :--- |
| **Proven Dead Ends (Even If Local Engineering Obstacles Are Solved)** | • Tensor-power amplification $\zeta(s)^d$ (Wall 5)<br>• Homotopy / admixture $\lambda_t = t\Lambda + (1-t)\lambda_0$ (Wall 8)<br>• Finite-order differential multipliers $P(D)\Xi$ & forward heat flow (Wall 4, `TT` pointwise, `TH` fixed-$d$)<br>• Reflection-even / 2D Poincaré–Lelong positivity (Wall 15, `LA`, `BSH`, `XN`)<br>• Window $\le 2\log 2$ one-signed odd cone & Beurling–Deny $v \mapsto \|v\|$ alone (`CHMD` window programme, Wall 13)<br>• Difference-of-autocorrelations causal-tent / factorial-Müntz repairs (`BSU` inside `EWU`/`WL`)<br>• Shift-gauge ground operators (`EvenSectorBlindGroundShiftInvariance` inside `RW`/`EWU`)<br>• Vacuum certificate squeeze without non-emptiness (`WBF` Hole 3)<br>• Unmollified $c_k = \mu(k)$ in Báez–Duarte (`CTF` Burnol obstruction)<br>• 1-step Markovian successor prediction (`EWJ` $3/4$ phase-loss obstruction)<br>• Pure Hurwitz $a$-transport without Euler projection (`HJ` Davenport–Heilbronn obstruction)<br>• Naive Maaß–Selberg cusp truncation (`PM (PW-B)`)<br>• Ferromagnetic Lee–Yang without pole deflation (`W1C`) | **Cannot deliver RH.** Each violates one or more formalized no-go theorems (`TwinRigidityZetaPower`, `FactorialBiNullObstruction`, `FactorialMuntzTailWeilGrowth`, `SharpSuccessorPhaseLossAndClosureClassification`, etc.). |
| **Isomorphic / Redundant Coordinates (Valid Receivers, Same Producer Core)** | `WL`, `RW`, `SZ`, `PA`, `GTA`, `JAS`, `RN`, `OWU`, `EWU`, `HF`, `PBM`, `RB`, `APF`, `CDC`, `EGC`, `MSC`, `PCS`, `PTR`, `RFHM`, `SC`, `SEC` | Valid `↔` or `←` bridges, but reduce algebraically to either the **Spectral Gap of the $\Theta$-Doob Operator (`CHMD`)** or **Trans-Horizon Sawtooth / Möbius Cancellation (`MC`/`CTF`/`BVI`)**. |
| **Primary Frontier Engines Where Genuine Multiplicative Leverage Exists** | 1. **`CHMD` (Quotient Spectral Gap & Multiplicative Divisor-Chain / Cardinal-Packet Contradiction)**<br>2. **`MC` + `CTF` + `PM (FZZ-P)` + `BVI` (Trans-Horizon Inactive Sawtooth Martingale & Multi-Lag Visibility Schedule)**<br>3. **`BAG` (Conditioned Kronecker-to-Tail Independence)** | **Only viable paths to RH**, provided the uncharted mathematical obstacles isolated in [hard-obstacles-summary-1810.md](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md) are solved. |
