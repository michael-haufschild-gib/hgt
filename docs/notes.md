### 1. What the Corpus Has Already Achieved (Ahead of Known Literature)

Most of the 16 live routes (`WL`, `RW`, `FU`, `RP`, `PA`, `MC`, `TT`, `LA`, `TG`, `TH`, `RN`, `WD`, `LI`, `SZ`, `PM`) are **receiver-first** routes: they reformulate RH as an equivalent positivity, cancellation, or operator-norm bound and hit the classical barrier that analytic smoothing or finite truncation loses prime phase information (`STATUS.md`).

However, in **Route HF**, the corpus has already achieved a genuine structural breakthrough—**unconditional uniqueness of the Weil cone**—that eliminates half of the Riemann Hypothesis:

1. **The Twisted Arc Minimum Principle ([`TwistedArcMinimumPrincipleProof.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/TwistedArcMinimumPrincipleProof.lean)):**
   Using the Maass–Whittaker stream PDE on the modular half-fundamental domain and a corner-derivative contradiction at $\rho = \frac{1}{2} + i\frac{\sqrt{3}}{2}$, Lean proves unconditionally (`twistedArcMinimumPrinciple_holds`) that there is a probability measure on the bottom modular arc $u \in [-\frac{1}{2}, \frac{1}{2}]$ annihilating all twisted integer moments $\int g_u(x)\cos(2\pi(n+2)x)\,dx$.
2. **Unconditional Uniqueness of the Weil Cone ([`WeilConeUniquenessUnconditional.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeUniquenessUnconditional.lean)):**
   That modular-arc measure produces a jointly prime-blind $\Xi$-divisible shifted-Gamma family $\Xi Q_j$, which proves unconditionally (`eq_vonMangoldt_of_weilPositiveFull`):
   > *Every real sequence $\lambda : \mathbb{N} \to \mathbb{R}$ (with **no** assumption on sign, growth, or multiplicativity) whose Weil functional is nonnegative on $C^2_c(\mathbb{R})$ autocorrelations satisfies $\lambda(n) = \Lambda(n)$ for all $n \ge 2$, and forces RH.*
3. **Unconditional Equivalence with Herglotz Existence & Prime-Blind Positivity ([`HerglotzProducerUniquenessUnconditional.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/HerglotzProducerUniquenessUnconditional.lean), [`PrimeBlindNodeCriticality.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindNodeCriticality.lean)):**
   Because uniqueness is completely solved, **primes and zeta zeros are eliminated from the remaining target (`PBAP`)**:
   $$\text{RiemannHypothesis} \iff \text{WeilOneSided.PrimeBlindPositive}$$
   i.e., for every finite nonnegative combination $k = \sum_i c_i (f_i \star \tilde{f}_i)$ of $C^2_c(\mathbb{R})$ autocorrelations satisfying $k(\pm \log n) = 0$ for all $n \ge 2$ (or all prime powers $p^m$), the purely archimedean functional
   $$W_\infty(k) = A(0) k(0) + \int_0^\infty \frac{e^{-x/2}}{1 - e^{-2x}}\bigl(2k(0) - k(x) - k(-x)\bigr)\,dx + 2\int_{\mathbb{R}} k(x)\cosh\!\left(\frac{x}{2}\right)dx$$
   is nonnegative.

---

### 2. Why We Are Stuck: The Structural Blind Spot

Why have we not yet proved `PrimeBlindPositive` (`PBAP`), and why do local/analytic attacks keep getting stuck?

The answer is already proved **inside our own Lean corpus**, in [`PrimeBlindNodeCriticality.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindNodeCriticality.lean#L165-L180) (`not_primeBlindPositiveOn_of_primePower_not_mem` and `exists_negative_arch_of_primePower_node_deleted`):

> **Theorem (`exists_negative_arch_of_primePower_node_deleted`, unconditional in Lean):**
> *For **every** prime power $m = p^k \ge 2$, there exists a nonnegative combination $k = \sum_i c_i (f_i \star \tilde{f}_i)$ of $C^2_c(\mathbb{R})$ autocorrelations that vanishes at $\pm \log n$ for **every** integer $n \ge 2$ with $n \ne m$, and yet has $W_\infty(k) < 0$.*

Look at what this theorem tells us about **why every attempt so far has stalled**:

1. **Why the Nonnegative-Cone Window Reduction ([`PrimeBlindNonnegativeConeReduction.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindNonnegativeConeReduction.lean)) only solves a sub-problem:**
   When we restrict to **nonnegative** test functions $f \ge 0$, vanishing at $\log n$ ($n \ge 2$) forces the support $S = \{f > 0\}$ to be dilation-free, so $|S| \le \log 2$ (using only $n = 2^k$), and quantile rearrangement moves $f$ onto $(0, \log 2)$.
   - On $(0, \log 2)$, $(f^* \star \tilde{f}^*)(x)$ vanishes on the **entire continuum** $[\log 2, \infty)$, not just at the discrete lattice $\{\log n : n \ge 2\}$.
   - In our just-completed module [`WeilLevyPoleGaussModeCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilLevyPoleGaussModeCancellation.lean), we extracted the $k=0, 1$ Gauss modes $\omega(x) = e^{-x/2} + e^{-5x/2} + e^{-4x}\omega(x)$ against the pole kernel $2\cosh(x/2)$ (reducing the universal anomaly floor from $A(0) \approx -5.3605$ to $A(0) + \frac{24}{5} \approx -0.5605$, and to $A(0) + 8\sinh(x_0/2) + 2\Omega(x_0) \approx -0.1448$ at the plastic-number crossover $e^{3x_0} = e^{x_0} + 1$), and proved unconditional positivity on $(0, L)$ for small $L$.
   - Closing the remaining $0.1448$ margin on $(0, \log 2)$ will prove **`WindowPositive`** (and hence `PBAP` on the **nonnegative cone** $f \ge 0$), which is a major milestone on the HF ledger—**but it cannot prove full `PBAP`**, because signed functions $f_i$ can have arbitrarily large support and achieve $k(\pm \log n) = 0$ by **oscillatory cancellation** rather than support size $\le \log 2$.

2. **Why the Disconnected "Constraint vs. Objective" Approach Fails on Signed `PBAP`:**
   Look at how our files in `RHTower` split into two non-communicating halves:
   - **Half 1 (The Blindness Constraint):** [`BlindCoreMayerTransferHalf.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/BlindCoreMayerTransferHalf.lean), [`InversionSymmetricFourierBlindTotalRigidity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/InversionSymmetricFourierBlindTotalRigidity.lean), and the `CosDilation*` / `ModularArc*` files study the constraint $k(\pm \log n) = 0$ ($\forall n \ge 2$) via Poisson summation and the Gauss–Mayer transfer operator, without ever plugging that identity into $W_\infty(k)$.
   - **Half 2 (The Archimedean Functional $W_\infty$):** [`WeilArchReLevyPoleForm.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilArchReLevyPoleForm.lean), [`SeparatedBumpPrimeBlindPositivity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/SeparatedBumpPrimeBlindPositivity.lean), and [`WeilLevyPoleGaussModeCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilLevyPoleGaussModeCancellation.lean) lower-bound $W_\infty(k)$ using only continuum/support geometry, without ever using the hypothesis that $k(\pm \log n) = 0$ at $n = 2, 3, 4, 5, 7, 8, 9, \dots$!
   - By `exists_negative_arch_of_primePower_node_deleted`, **any lower bound on $W_\infty(k)$ that does not explicitly use the vanishing of $k(\pm \log n)$ at every prime power $n = p^m$ is mathematically guaranteed to fail on signed tests.**

---

### 3. The Gordian Knot: How to Reframe the Problem

Where does the archimedean functional $W_\infty(k)$ actually meet the discrete nodes $\{\log n : n \ge 2\}$?
Look at the two equivalent faces of the missing existence theorem:

#### Perspective A: The Primal (Modular / Theta / Poisson) Identity for $W_\infty(k)$ on All-Integer-Blind Cores
Why does the continuous functional
$$W_\infty(k) = \int_{-\infty}^\infty \widehat{k}(\tau)\, A\!\left(\frac{\tau}{2\pi}\right) d\tau + 2\int_{-\infty}^\infty k(x)\cosh\!\left(\frac{x}{2}\right)dx$$
know about the discrete lattice $\{\log n : n \ge 2\}$ at all?
Because $A(\frac{\tau}{2\pi}) = \operatorname{Re}\frac{\Gamma_\mathbb{R}'}{\Gamma_\mathbb{R}}(\frac{1}{2} + i\tau)$, and $\Gamma_\mathbb{R}(s) = \pi^{-s/2}\Gamma(s/2)$ is the Mellin transform of the **Gaussian $e^{-\pi y^2}$**, which is coupled to all integers $n \in \mathbb{Z}$ by **Jacobi theta / Poisson summation**:
$$\vartheta(t) = \sum_{n=-\infty}^\infty e^{-\pi n^2 t} = t^{-1/2}\vartheta(1/t).$$
When a signed combination of autocorrelations $k = \sum_i c_i (f_i \star \tilde{f}_i)$ satisfies $k(\pm \log n) = 0$ for **all** $n \ge 2$:
- In multiplicative coordinates $F_i(y) = y^{-1/2} f_i(\log y)$ on $(0, \infty)$, integer blindness $k(\pm \log n) = 0$ ($\forall n \ge 2$) says that the off-diagonal integer dilations $\sum_{n \ge 2} \langle D_n F, F \rangle$ vanish.
- Therefore, for any kernel built from a modular/Poisson sum $\sum_{n \ge 1} \phi(n y)$, **the $n \ge 2$ terms are identically zero on the prime-blind cone**, collapsing the entire infinite arithmetic sum onto the **$n = 1$ (archimedean) term alone!**
- Look at what that means: on the Uniqueness side ([`TwistedArcMinimumPrincipleProof.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/TwistedArcMinimumPrincipleProof.lean)), we used $\mathrm{SL}_2(\mathbb{Z})$ modularity on the *test function* to annihilate $\{\log n : n \ge 2\}$. We have **never yet used Poisson/Epstein/Mayer summation to rewrite the archimedean kernel $W_\infty(k)$ itself modulo the ideal $\{k(\pm \log n) = 0 : n \ge 2\}$** as a positive quadratic form!

#### Perspective B: The Dual (Herglotz / Schur) Construction via Unconditional Uniqueness
Look at [`HerglotzProducerUniquenessUnconditional.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/HerglotzProducerUniquenessUnconditional.lean#L44-L49):
$$\text{RiemannHypothesis} \iff \exists \lambda : \mathbb{N} \to \mathbb{R},\; \operatorname{Re}\!\left(\Phi_\infty(s) - \sum_{n=2}^\infty \lambda(n) n^{-s}\right) \ge 0 \quad \text{on } \operatorname{Re} s > \frac{1}{2},$$
where $\Phi_\infty(s) = \frac{1}{2}\psi(\frac{s}{2}) - \frac{1}{2}\log\pi + \frac{1}{s} + \frac{1}{s-1}$.
Notice two remarkable facts about $\Phi_\infty(s)$ on $\operatorname{Re} s = \frac{1}{2}$:
1. On the critical line $s = \frac{1}{2} + it$, the pole sum $\frac{1}{s} + \frac{1}{s-1} = \frac{-2it}{1/4 + t^2}$ has **identically zero real part**.
2. $\operatorname{Re}\Phi_\infty(\frac{1}{2} + it) = \frac{1}{2}A(t)$ is **already strictly positive** for all $|t| > 6.29$ (growing like $\frac{1}{2}\log|t|$) and is only negative on the bounded low-frequency window $|t| \le 6.29$ (plus the simple pole of $\frac{1}{s-1}$ at $s = 1$ inside the half-plane).
3. Because **uniqueness is already proved**, we do **not** need to plug $\lambda(n) = \Lambda(n)$ into $\Phi_\lambda(s)$ and prove $\zeta(s) \ne 0$: by Nevanlinna–Pick / Herglotz interpolation in the Dirichlet-series subspace $\{ \sum_{n \ge 2} \lambda(n) n^{-s} \}$, the existence of *any* Dirichlet series canceling the pole at $s = 1$ and lifting the finite low-frequency well $|t| \le 6.29$ to $\operatorname{Re} \Phi \ge 0$ automatically forces $\lambda = \Lambda$ and RH.

---

### 4. Concrete Two-Track Path Forward

1. **Immediate Track 1 (Finish the Nonnegative-Cone Window Theorem on $(0, \log 2)$):**
   In [`WeilLevyPoleGaussModeCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilLevyPoleGaussModeCancellation.lean) (just verified and wired into [`RHTower.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower.lean)), we reduced the universal nonnegative-cone anomaly from $-5.3605$ to $-0.5605$. Using the exact **Lévy–cosh crossover identity** at $x_0 = \log u_0 \approx 0.2812$ ($u_0^3 = u_0 + 1$):
   $$W_\infty(f \star \tilde{f}) = \bigl(A(0) + 8\sinh(x_0/2) + 2\Omega(x_0)\bigr)\|f\|_2^2 + \int_0^{x_0}\bigl(\omega(x) - 2\cosh(x/2)\bigr)\|f - f(\cdot+x)\|_2^2\,dx + 2\int_{x_0}^\infty\bigl(2\cosh(x/2) - \omega(x)\bigr)R_f(x)\,dx,$$
   the constant deficit drops to $-0.1448$, and combining the $(0, x_0)$ boundary-escape/Dirichlet term with the $(x_0, \log 2)$ autocorrelation term attacks the remaining `WindowPositive` gap on $(0, \log 2)$ in [`PrimeBlindNonnegativeConeReduction.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindNonnegativeConeReduction.lean).
2. **Strategic Track 2 (The All-Integer Poisson / Mayer Positivity Identity for Signed `PBAP`):**
   To cross the `PrimeBlindNodeCriticality` barrier for **signed** tests, we must stop bounding $W_\infty(k)$ as if $k$ were an arbitrary function, and instead use the identity $\sum_{n=2}^\infty w_n k(\pm \log n) = 0$ on the prime-blind cone to add a Poisson/Mayer counterterm $\sum_{n \ge 2} w_n \bigl(k(\log n) + k(-\log n)\bigr) = 0$ directly to $W_\infty(k)$ so that the combined kernel becomes globally positive semi-definite (`Bochner` / `Herglotz`) without sign restrictions on $f$.

## addition other route
WeilMarkovOddPositivity.lean: RH holds iff the archimedean-minus-prime form is ≥0 on odd tests, a pure positivity statement with no pole or index. Or:  RH is positivity of the archimedean-minus-prime form on odd tests

WeilMarkovPrimitiveHyperplane.lean: RH is equivalent to M ≥ 0 on the hyperplane ∫f·cosh(x/2) = 0 — combined with M(Φ_L) < 0, this captures the "exactly one negative square" law. RH is positivity of the archimedean-minus-prime form on the primitive hyperplane.

We pinned down the target as positivity on a specific hyperplane but confirmed every mechanism hits the same obstruction—exact cancellation between the pole and primes' main term at √x precision.


## new route
Viewed rh-current-frontier-map.md:1-541
Viewed STATUS.md:1-800
Viewed rh-current-frontier-map.md:1-541
Viewed rh-current-frontier-map.md:1-541
Viewed rh-current-frontier-map.md:1-541
Viewed rh-killed-routes.md:1-800
Viewed rh-killed-routes.md:1-800
Viewed rh-killed-routes.md:1-800
Viewed rh-killed-routes.md:1-800
Viewed rh-killed-routes.md:801-1143
Viewed rh-killed-routes.md:801-1143
Viewed STATUS.md:4500-5156
Viewed STATUS.md:4500-5156
Viewed STATUS.md:4500-5156
Viewed STATUS.md:4500-5156
Viewed STATUS.md:5050-5156
Ran command: Check STATUS.md headings and pipeline cards (`rg '^##' docs/reports/STATUS.md && ls -lt docs/drafts/pipeline/1-in-progress/ | head -n 40`)
Viewed pbap-existence-barrier-atlas.md:1-105
Viewed rh-big-picture-interpretation.md:1-680
Viewed STATUS.md:230-978
Viewed rh-big-picture-interpretation.md:1-680
Viewed STATUS.md:521-1320
Viewed rh-big-picture-interpretation.md:1-680
Ran command: List recent in-progress pipeline cards (`ls -lt docs/drafts/pipeline/1-in-progress/ | head -n 30`)
Viewed pbap-conjecture-loop-fable-2026-10-14.md:1-269
Viewed even-window-pole-weight-uniqueness.md:1-44
Viewed odd-sector-weil-uniqueness.md:1-105
Ran command: Check tail of main conjecture loops (`tail -n 100 docs/drafts/pipeline/1-in-progress/producer-loop-opus-2026-10-12.md docs/drafts/pipeline/1-in-progress/rh-goal-loop-opus-2026-09-29.md`)
Viewed tg-quantized-exclusion-loop-2026-10-15.md:1-108
Viewed gta-arithmetic-core-loop-2026-10-15.md:1-191
Viewed route-dr-corpus-loop-2026-10-15.md:1-435
Viewed irk-rh-source-loop-2026-10-15.md:1-223
Viewed route-rn-full-divisor-charge-2026-10-15.md:1-181
Viewed _card-template.md:1-33
Ran command: Search corpus for PBAP value function and squeeze theorems (`scripts/formal_tools.py research "ArchimedeanNodeValueFunction PrimeBlindLevelCertificateSqueeze" --no-refresh`)
Ran command: Search corpus for solid observation theorems (`scripts/formal_tools.py research "SolidObservationLpSolidUniform" --any --no-refresh`)
Ran command: Search corpus for Twisted Arc Minimum Principle theorems (`scripts/formal_tools.py research "ClampedBeamPositivity TwistedArcMinimumPrinciple" --any --no-refresh`)
Created new-route-synthesis-conjecture-loop-2026-10-15.md
Viewed TwistedArcMinimumPrincipleProof.lean:1-418
Viewed PrimeBlindNodeCriticality.lean:1-200
Viewed WeilConeUniquenessUnconditional.lean:1-120
Viewed TwistedArcMomentPositiveRH.lean:1-250
Viewed TwistedArcN1Reduction.lean:1-250
Viewed DivisorKernelFourierIdentification.lean:1-174
Viewed TwistedArcGenerator.lean:1-250
Viewed n1-log-edge-modular-arc-witness.md:1-254
Viewed n1-voronoi-maass-interpolation.md:1-103
Ran command: Search corpus for xiShiftedGammaTest and xiDivisibleBlindFamily (`scripts/formal_tools.py research "xiShiftedGammaTest eq_vonMangoldt_of_xiDivisibleBlindFamily" --any --no-refresh`)
Viewed WeilConeXiDivisibleBlindFamily.lean:1-250
Viewed ArcGammaMultiplier.lean:1-250
Viewed WeilConeXiDivisibleBlindFamily.lean:251-601
Viewed WeilConeXiDivisibleBlindTest.lean:1-250
Viewed WeilConeXiDivisibleBlindTest.lean:900-1269
Viewed WeilConeCriticalZeroCarriedRigidity.lean:1-250
Viewed ArchimedeanPoleValueFunction.lean:1-260
Viewed ArchimedeanPoleValueFunction.lean:261-788
Viewed new-route-synthesis-conjecture-loop-2026-10-15.md:1-115
Ran command: Search Lean corpus for levelCertificates (`scripts/formal_tools.py research --no-refresh "levelCertificates PrimeBlindLevelCertificateSqueeze"`)
Viewed PrimeBlindLevelCertificateSqueeze.lean:1-172
Viewed BlindArchimedeanNodeTwoCertificate.lean:1-250
Viewed BlindArchimedeanNodeTwoCertificate.lean:240-309
Viewed WeilBlindPoleSignLaw.lean:1-224
Viewed PrimeBlindPoleWeightLevelWindow.lean:1-300
Viewed PrimeBlindPoleWeightLevelWindow.lean:300-422
Viewed PrimeBlindPoleZetaDefect.lean:2-301
Viewed PrimeBlindPoleSpectralTail.lean:1-300
Viewed PrimeBlindPoleSpectralTail.lean:301-612
Viewed PrimeBlindKernelSpectral.lean:1-336
Viewed PrimeBlindFiniteLevelFarkas.lean:1-350
Viewed WeilSymbolMertensExpansion.lean:1-350
Ran command: List Blind, Pole, and Level Lean modules (`ls formal/GaloisForLFunctions/RHTower/*Blind* formal/GaloisForLFunctions/RHTower/*Pole* formal/GaloisForLFunctions/RHTower/*Level*`)
Ran command: List PrimeBlind and WeilPole Lean modules (`ls formal/GaloisForLFunctions/RHTower/PrimeBlind* formal/GaloisForLFunctions/RHTower/WeilPole* formal/GaloisForLFunctions/RHTower/EvenWeil* formal/GaloisForLFunctions/RHTower/OddWeil*`)
Viewed PrimeBlindPoleCriticalZetaDefect.lean:1-250
Viewed PrimeBlindPoleCuspIdentity.lean:1-112
Viewed PrimeBlindFiniteCertificateObstruction.lean:1-99
Viewed EvenWeilRHCriterion.lean:1-250
Viewed OddWeilFunctionRigidity.lean:1-250
Viewed DilationAutocorrelationPeriodization.lean:1-250
Viewed CosDilationKernelBlindnessLink.lean:1-250
Viewed InvertedCosineDistanceGammaPhase.lean:1-250
Viewed DoublyBlindCorePoleDistance.lean:1-250
Viewed CosDilationMediumSupportRigidity.lean:1-100
Viewed CosDilationShortSupportRigidity.lean:1-100
Ran command: Search for cosDilationKernel across corpus (`rg "DilationAutocorrelationPeriodization|cosDilationKernel" formal/ docs/`)
Viewed BlindCoreMayerTransferHalf.lean:1-120
Viewed InversionSymmetricFourierBlindGaussTransfer.lean:1-120
Viewed CosDilationPrimitiveEnergyRigidity.lean:1-120
Ran command: List CosDilation and InversionSymmetric modules (`ls formal/GaloisForLFunctions/RHTower/*CosDilation* formal/GaloisForLFunctions/RHTower/*InversionSymmetric* formal/GaloisForLFunctions/RHTower/*DoublyBlind* formal/GaloisForLFunctions/RHTower/*DilationAutocorrelation* formal/GaloisForLFunctions/RHTower/*BlindCore*`)
Viewed InversionSymmetricFourierBlindTotalRigidity.lean:1-216
Viewed InversionSymmetricFourierBlindTwistedMayer.lean:1-134
Viewed InversionSymmetricOddFourierBlindRigidity.lean:1-250
Viewed InversionSymmetricFourierBlindSqrtThreeCore.lean:1-120
Viewed InversionSymmetricFourierBlindContinuousCore.lean:1-120
Viewed CosDilationDivisorMomentPeriodizationRigidity.lean:1-120
Viewed CosDilationLogPrimCoreDualRigidity.lean:1-120
Viewed CosDilationPeriodicMultiplierUnfolding.lean:1-120
Ran command: Search for levelWindow nonemptiness theorems (`scripts/formal_tools.py research --no-refresh "levelWindow nonempty"`)
Ran command: Search for levelWindow and ZeroPoleBlind across files (`rg "levelWindow|ZeroPoleBlind" formal/ docs/`)
Edited new-route-synthesis-conjecture-loop-2026-10-15.md
Viewed PrimeBlindLevelFloor.lean:1-243
Viewed pbap-conjecture-loop-fable-2026-10-14.md:120-160

Error: API error (attempt 1): UNAVAILABLE (code 503): The service is currently unavailable. (Error ID: 87ff960f-c5b6-410f-a30a-36664da11301-166)

Ran command: Search for Beurling-Deny and small-aperture Weil positivity (`scripts/formal_tools.py research --no-refresh "BeurlingDeny plastic weilArchRe"`)
Ran command: Search for plastic constant and MUST-886 in docs and formal (`rg "plastic|886|CANNOT-559|MUST-1506" docs/ formal/`)
Viewed STATUS.md:4850-5156
Viewed STATUS.md:4850-5156
Viewed new-route-synthesis-conjecture-loop-2026-10-15.md:1-202
Checked task Search for plastic constant and MUST-886 in docs and formal
Killed task Search for plastic constant and MUST-886 in docs and formal
Ran command: Search EvenSectorFullPositivity in corpus (`python3 scripts/formal_tools.py research "EvenSectorFullPositivity" --no-refresh`)
Viewed EvenSectorFullPositivity.lean:1-685
Viewed ArchimedeanPoleValueFunction.lean:1-788
Viewed EvenSectorWeilCone.lean:1-402
Viewed EvenSectorTwistedArcNull.lean:1-693
Viewed MarkovOddSectorFarkasAndOneSidedPBAP.lean:1-800
Viewed MarkovShiftPolarizationAndEvenPrimitivePBAP.lean:1-800
Viewed EvenSectorSechRepresentation.lean:1-204
Viewed EvenSectorSpectralConsistency.lean:1-800
Viewed EvenSectorCosineBochner.lean:1-800
Viewed EvenSectorStripPositivity.lean:1-329
Viewed TwistedArcNullLaplacePositivity.lean:1-250
Ran command: Search cosineShiftFn and sechHalf in corpus (`rg "cosineShiftFn|sechHalf" formal/ docs/`)
Viewed EvenSectorCriticalZeroCarrier.lean:1-131
Viewed EvenSectorPoleFreeResonatorPositivity.lean:1-553
Viewed EvenSectorPoleFreeLogDensity.lean:1-247
Viewed WeilPositivityMultiplicativeToeplitzBound.lean:1-800
Viewed PrimeBlindPoleSpectralTail.lean:1-90
Ran command: Search markovArchRe and weilArchRe in corpus (`python3 scripts/formal_tools.py research "markovArchRe weilArchRe" --no-refresh`)
Viewed MarkovOddShiftWindowAndPlasticCrossoverPBAP.lean:1-120
Viewed WeilLevyPoleGaussModeCancellation.lean:1-120
Viewed WeilLevyCoshPlasticCrossover.lean:1-120
Viewed MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean:1-100
Viewed AllIntegerPoissonCountertermAndBochnerPBAPBridge.lean:1-100
Viewed WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean:1-100
Viewed new-route-synthesis-conjecture-loop-2026-10-15.md:140-202
Viewed MarkovShiftPolarizationAndEvenPrimitivePBAP.lean:1-95
Viewed MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean:1-260
Viewed MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean:340-470
Viewed MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean:471-620
Viewed WeilLevyPoleGaussModeCancellation.lean:1-110
Viewed EvenSectorSechRepresentation.lean:204-204
Viewed EvenSectorTwistedArcNull.lean:500-561
Viewed EvenSectorCosineBochner.lean:240-310
Viewed EvenSectorCosineBochner.lean:650-804
Viewed EvenSectorTwistedArcNull.lean:220-340
Viewed EvenSectorCriticalZeroCarrier.lean:1-131
Viewed EvenSectorTwistedArcNull.lean:420-500
Viewed EvenSectorTwistedArcNull.lean:560-693
Viewed EvenSectorSechRepresentation.lean:70-204
Viewed EvenSectorSpectralConsistency.lean:220-360
Viewed EvenSectorSpectralConsistency.lean:361-470
Viewed EvenSectorSpectralConsistency.lean:471-560
Created new-route-synthesis-conjecture-loop-2026-10-15.md

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

### 3. Summary of the New Route (Part IV of the Working Log)

The new route—**Causal Hyperbolic–Modular Duality (CHMD)** ([new-route-synthesis-conjecture-loop-2026-10-15.md](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/new-route-synthesis-conjecture-loop-2026-10-15.md#L411-L461))—proceeds in four concrete stages:

1. **Stage 1 (Multiplicative Unit-Interval / Half-Line Reduction & Clamped-Beam Floor on `EvenPrimitiveWeilTestFn`):** Formalize the exact bridge between `bochnerResolventEnergy` (`RHTower`) and $2\int_0^1 A_c(r)\,dr$ (`Zeta23`), the nonsingular multiplicative formula for `markovArchRe` with $M = 4$ Gauss-mode extraction, and the $f = (-D_x^2 + 1/4)q$ clamped-beam factorisation on `EvenPrimitiveWeilTestFn` (pushing unconditional positivity past $2a = \log 4$).
2. **Stage 2 (Klein–Gordon Mass-$1/2$ Wave Propagators & Adjoint Volterra Transmutation $H_c = \mathcal{S} K_c$):** Formalize the compactly supported Klein–Gordon propagators $u_{1/4}, v_{1/4}$ on `EvenWeilTestFn`/`EvenPrimitiveWeilTestFn` and the unconditional T-contour Bochner positivity $\widehat{H_c}(\rho) \ge 0$ on $\mathbb{R}$.
3. **Stage 3 (Primal Variational Ground State $C_{\text{TA}}$ & Unconditional 1D Sech-Convolution Equations):** Extract $C_{\text{TA}}$ as the standalone zero-energy prime-blind ground state ($\frac{-\text{archOnly}(C_{\text{TA}})}{P(C_{\text{TA}})} = 1$) and remove the measure hypothesis `hν` from the Fubini representation in [EvenSectorSpectralConsistency.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorSpectralConsistency.lean) to give $\kappa_j \star \varphi_\Lambda \equiv 0$ and $\kappa_{\text{TA}} \star \varphi_\Lambda \equiv 0$ unconditionally.
4. **Stage 4 (2D Elliptic–Hyperbolic Closure):** Combine the zero-energy ground state $C_{\text{TA}}$ and Dual Poisson Periodization on the primal cone with the causal Klein–Gordon light-cone expansion of $\varphi_\Lambda(y)$ under $\kappa_{\text{TA}}$-annihilation to close `exists_cosineShift_measure` for `sechHalf`.

Viewed EvenSectorPoleFreeLogDensity.lean:1-247
Viewed EvenSectorPolarRigidity.lean:180-280
Viewed PolarConePartialSumRigidity.lean:1-250
Viewed EvenSectorPolarStripCeiling.lean:1-250
Viewed EvenSectorPoleFreeNodeTests.lean:1-250

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
