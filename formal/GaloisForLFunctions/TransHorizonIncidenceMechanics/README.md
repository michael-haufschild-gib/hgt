# Trans-Horizon Incidence Mechanics (`GaloisForLFunctions.TransHorizonIncidenceMechanics`)

**Trans-Horizon Incidence Mechanics (`THIM`)** — also referred to in the programme blueprint ([`docs/reports/hard-obstacles-summary-1810.md`](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md)) as **Multiplicative Valuation-Clock Spectral Theory** — is the unified mathematical framework that fuses our two foundational Lean formalizations into a single joint operator calculus on $\mathbb{R} \times \mathbb{N}_+$:
1. **Continuous / Archimedean Side (`BiScaleUncertainty` & `RHTower`):** Bi-scale Krein collars, folded interpolation, Riesz–Herglotz resolvents, and secondary odd theta profiles on the logarithmic scale $x \in \mathbb{R}$.
2. **Discrete / Arithmetic Side (`BezoutValuationIncidence`):** Multiplicative Selberg LCM divisibility coupled with additive Bézout successor shifts ($k \mapsto k + 1$), Ramanujan lag diagonalization, valuation visibility clocks $\tau_{\mathrm{vis}}(q) = q / \operatorname{rad}(q)$, and active/inactive sawtooth martingales on $\mathbb{N}_+$.

Rather than serving a single route, `THIM` provides the shared algebraic, combinatorial, and functional-analytic machinery needed to break the **6 Irreducible Uncharted Obstacles** across all **15 Structural Walls**, **27 Live Routes**, and **18 Route Candidates** (`MC`, `CTF`, `PM (FZZ-P)`, `BVI`, `RP`, `SEC`, `CHMD`, `OWU`, `EWU`, `RW`, `WL`, `SZ`, `PA`, `GTA`, `HF`, `LI`, `RB`, `PBM`, `DR`, `TG`, `BAG`, `TH`, `TT`, `WD`, `XN`, `FEL`, `HJ`, `W1C`).

---

## 1. Motivation: Why the Two Existing Halves Stalled & the 6 Uncharted Obstacles

### 1.1 Why Each Half Stalled in Isolation at a Horizon Boundary
- **Why `BiScaleUncertainty` Stalled (Continuous/Archimedean Side):**
  It treated the prime-power log-grid $\{k \log p\}$ as an *external exclusion set* for 1D continuum test functions. Consequently, it hit four structural obstructions:
  - `FactorialBiNullObstruction`: Bi-null repaired profiles generate *differences* of autocorrelations rather than a single Bochner autocorrelation $F = f \star \tilde{f}$ with $\widehat{F} \ge 0$.
  - `FactorialPolarGramScaleSeparation`: The $s = 1$ polar mode dominates the Gram matrix by a factor of $\log n$.
  - `FactorialMuntzTailWeilGrowth`: Repaired factorial Müntz-ramp tails have strictly positive Weil energy unconditionally and are therefore RH-nonselective.
  - `InfiniteGridStrictEnergyLoss`: As the prime grid grows, Lévy diffusion energy escapes into the origin collar $t \to 0^+$.
- **Why `BezoutValuationIncidence` Stalled (Discrete/Arithmetic Side):**
  It established unconditional non-positivity of the renormalized correlation defect (`PowerDampedRenormalizedDefectAndPronicCeiling`) **sub-horizon ($M + 1 \le N$)** inside the periodic factorial cycle $L_N = \operatorname{lcm}(1, \dots, N) = e^{\psi(N)}$, where $s_{N,\mu}(k) = 0$ for all $2 \le k \le N$. However, RH lives in the **trans-horizon regime ($N < M \le N^2$ and $M \to \infty$)**, where 1-step successor prediction loses $\ge 3/4$ of the variance (`SharpSuccessorPhaseLossAndClosureClassification`), incomplete-period Ramanujan remainders explode as $O((\sum_{d \le N} |c(d)|)^2)$, and inactive sawtooth martingale drift escapes.

### 1.2 The 6 Uncharted Obstacles Across the RH Programme
Every viable route in our corpus reduces to one (or a coupled pair) of six irreducible mathematical problems ([`docs/reports/hard-obstacles-summary-1810.md`](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md)):

| Obstacle | Routes Blocked & Walls Confronted | Core Mathematical Bottleneck |
| :--- | :--- | :--- |
| **1. Trans-Horizon Sawtooth Martingale & Tail Cancellation** | `MC`, `CTF`, `PM (FZZ-P)`, `BVI`, `RP`, `SEC` (Wall 1) | Bounding inactive centered sawtooth martingale drift across $N < M \le N^2$ against active shifted-Euler drift, or proving uniform $L^2((0, 1/N), dx/x^2)$ tail boundedness so weak compactness / Mazur's lemma forces Báez–Duarte distance $d_N \to 0$. |
| **2. Odd-Sector / Primitive Quotient Spectral Gap ($\lambda_1 \ge 1$) & Off-Line Packet Exclusion** | `CHMD`, `OWU`, `EWU`, `RW`, `WL`, `SZ`, `PA`, `GTA`, `HF`, `JAS`, `RN` (Walls 6, 9, 11, 12, 13, 14) | Proving the divisor-chain Poincaré inequality on $\mathcal{H}_{\mathrm{odd}} / \operatorname{signedRadical}$ (using $\Lambda(p^r) = \log p$ to beat `Zeta23Countermodel` / Wall 9, radical deflation to beat zero-slack Wall 11, and sign-preserving nodal mechanics to beat Beurling–Deny $v \mapsto |v|$ loss / Wall 13), or excluding off-line cardinal packets $(A - 1)u = m_a \cos(\bar{a}x)/\cosh(x/2)$. |
| **3. Single-Autocorrelation Prime-Blind Synthesis Without Polar or Origin Escape** | `BiScaleUncertainty`, `EWU`, `WL`, `RW`, `FU`, `MSC` (Walls 8, 11, 12, 13) | Constructing genuine single Bochner autocorrelations $F_n = f_n \star \tilde{f}_n$ tuned to a putative off-line zero with uniform origin-collar tightness ($t \to 0^+$) and $s = 1$ pole annihilation. |
| **4. Non-Stationary / Pole-Neutral Additive-to-Multiplicative Phase Transport** | `LI`, `RB`, `PBM`, `DR`, `TG` (Walls 1, 3, 10) | Executing additive-to-multiplicative phase cancellation inside $\mathbb{N}$ via multi-lag Bézout/Ramanujan visibility schedules $\tau_{\mathrm{vis}}(q) \mid h$ *before* Mellin/Laguerre transformation (avoiding Wall 10's stationary-phase pole crossing), and breaking critical-line symmetry $\gamma \leftrightarrow \bar{\gamma}$ against Turán zero clustering (Wall 3). |
| **5. Conditioned Kronecker-to-Tail Independence in Vertical Shifts** | `BAG` (Wall 7) | Decoupling small-prime Kronecker return sets $\mathcal{K}_{P,\delta}$ from high-prime Dirichlet tails via a conditioned Montgomery–Vaughan mean-value theorem with polynomial cutoff $N = P^{O(1)}$. |
| **6. Pole-Deflated / Antiferromagnetic Lee–Yang & Reverse-Jensen Rigidity** | `TH`, `TT`, `WD`, `XN`, `FEL`, `HJ`, `W1C` (Walls 2, 4, 15) | Projecting out the rank-1 antiferromagnetic polar mode ($s = 1$ pole / `CoshMass`) on $1^\perp$ and enforcing exact prime-power multiplicativity $\Lambda(p^r) = \log p$ to defeat Davenport–Heilbronn Hurwitz counterexamples. |

---

## 2. Core Objects and Unified Language (What)

`THIM` operates through a precise dictionary linking discrete multiplicative-additive observation states on $\mathbb{N}_+$, $p$-adic valuation chains, and continuous archimedean/resolvent functionals on $\mathbb{R}$:

| Domain | Object / Lean Symbol | Mathematical Definition & Cross-Route Role |
| :--- | :--- | :--- |
| **Discrete Observation Fibers** (`BVI`, `MC`, `CTF`, `LI`, `RB`, `BAG`) | `sieveSeq N c k` | Truncated divisor sum $s_{N,c}(k) = \sum_{d \mid k,\, d \le N} c(d)$ for horizon $N$ and weight $c : \mathbb{N} \to \mathbb{R}$. |
| | `horizonObservationState N k` | $\sigma_N(k) = \operatorname{lcm}\{d \le N : d \mid k\} = \gcd(k, L_N)$ ($L_N = \operatorname{lcm}(1,\dots,N)$), the universal $L_N$-even state determining $s_{N,c}(k)$ for all $c$. |
| | `horizonRadicalState N k` | $\operatorname{rad}_N(k) = \gcd(k, N\#)$ ($N\# = \prod_{p \le N} p$), the squarefree observation state determining $s_{N,c}(k)$ for all squarefree-supported $c$. |
| | `lagVisibilityClock q` | Valuation visibility clock $\tau_{\mathrm{vis}}(q) = q / \operatorname{rad}(q)$ ($\tau_{\mathrm{vis}}(p^a) = p^{a-1}$), satisfying $\Lambda(d) = \log(d / \tau_{\mathrm{vis}}(d))$. |
| **Trans-Horizon Sieve, Sawtooth & Fermi Dynamics** (`MC`, `CTF`, `PM`, `RP`, `SEC`) | `shortWindowRenormalizedDefect N M₀ M c` | $\widetilde{\mathcal{D}}_N(M_0, M; c) = \sum_{k=M_0+1}^{M_0+M} \bigl(s_{N,c}(k) s_{N,c}(k+1) - s_{N,c}(k)^2\bigr)$, measuring unit-shift correlation minus $L^2$ energy on $[M_0+1, M_0+M]$. |
| | `sieveL2PrefixEnergy N M c` | Prefix $L^2$ sieve energy $\mathcal{E}_N(M; c) = \sum_{k=1}^M s_{N,c}(k)^2$, evolved downward in $N$ from $\mathcal{E}_M(M; \mu) = 1$. |
| | `fermiCellResponse N c m` | Dyadic Fermi–Nyman cell jump $s_{N,c}(2m+1) - s_{N,c}(2m)$ coupling discrete Buchstab steps to the $L^2((0, 1/N), dx/x^2)$ Báez–Duarte tail. |
| **Prime-Power Chains & Hyperbolic Lifts** (`CHMD`, `SZ`, `PA`, `GTA`, `TH`, `W1C`) | `varianceEnergy L R f` / `chainVariance N u f` | Discrete bipartite cut energy $\sum_{n \in L}\sum_{m \in R} (f(n) - f(m))^2$ on $p$-adic prime chains `(chainLeft N p b u, chainRight N p b u)` ($N = m p^r n$, $p \nmid m n$) and its $\log p$-weighted sum. |
| | `chainIntegral v q` | Continuous `CHMDPrimeChainSource` divisor-chain variance integral $\int_{\mathbb{R}} \operatorname{density}(N, p, b, v, u)\,du \ge 0$ for `q : ChainIndex`. |
| **Quotient Resolvent & Nodal Lobes** (`CHMD`, `OWU`, `EWU`, `RW`, `WL`, `HF`, `TG`) | `oddPrimitivePart b hb q` | Quotient projection onto $\mathcal{H}_{\mathrm{odd}} \cap (\operatorname{signedRadical})^\perp$, where `sourceEnergy (oddPrimitivePart b hb q) = weilForm q`. |
| | `absGraph q`, `posGraph q`, `negGraph q` | Modulus and positive/negative nodal lobes of a `SourceGraph` vector $q$, with bilateral cross-pairing `sourcePair (posGraph q) (negGraph q)`. |
| | `oddPrimeDriftOperator` | Odd chiral prime-shift drift operator on `HalfLineL2`, anticommuting with `reflectMass` so its expectation vanishes on every odd vector. |
| **Bi-Scale Collars & Dual Doob Gauges** (`BiScaleUncertainty`, `CHMD`, `EWU`, `WL`) | `oddProfile a x` ($m_a(x)$) / `oddPolarFunction a x` ($f_a(x)$) | Secondary odd theta profile $m_a(x) = \frac{\Theta(x - a) - \Theta(x + a)}{2\sinh(a/2)}$ ($> 0$ on $(0, \infty)$) and polar ratio $f_a(x) = m_a(x)/\Theta(x)$. |
| | `oddPolarWeight a w x` / `oddProfileTest a w x` | Weighted Doob profile $v(x) = f_a(x) w(x)$ and secondary test $\Theta(x) v(x) = m_a(x) w(x)$ linking the $\Theta$-Doob and $m_a$-Doob gauges. |
| | `oddProfileShiftJump a w t x` / `oddProfileCollarDiffSq a w t x` | Half-line shift jump $m_a(x) m_a(x + t) (w(x) - w(x + t))^2$ vs. origin-crossing collar difference square $m_a(x) m_a(t - x) (w(x) - w(t - x))^2$ on $x \in (0, t)$. |
| | `oddProfileCollarMixed a w t x` | Mixed collar kernel $\Theta(x)\Theta(t-x)(v(x)+v(t-x))^2 + m_a(x)m_a(t-x)(w(x)-w(t-x))^2$, whose cross term $w(x)w(t-x)$ cancels under midpoint reflection. |

---

## 3. The Five Foundational Pillars & Mechanisms (How)

Following [`docs/reports/hard-obstacles-summary-1810.md` §3](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md), the results in `TransHorizonIncidenceMechanics` are organized into **five foundational pillars**:

### Pillar 1: Quotient State-Space & Non-Leaky Observation-Fiber Geometry
*Defeats Walls 11 & 12; underpins `BVI`, `CTF`, `MC`, `CHMD`, `OWU`, `EWU`, `WL`, `RW`.*

- **Shift-Invariant Polar Radical Deflation (`PolarRadicalInvarianceNodalDriftAndFermiGradientBridge`):**
  For any admissible polar shifts $a, b > 0$, the difference of Riesz polar vectors $\Psi_a - \Psi_b$ lies in `signedRadical`. Consequently, the polar pairing $\operatorname{sourcePair}(\Psi_a, q) = \langle q.\text{fst}, \operatorname{tanhL}\rangle_{\mathbb{R}}$ is independent of $a$ and vanishes identically on the quotient projection `oddPrimitivePart b hb q`, where `sourceEnergy (oddPrimitivePart b hb q) = weilForm q` with zero polar leakage.
- **Finite Multiplicative Observation Fibers & Iso-State Windows (`FiniteMultiplicativeObservationState`, `ShortWindowCorrelationDefectAndIsoStateClassification`):**
  On the discrete side, $s_{N,c}(k)$ factors through the finite lattice state $\sigma_N(k) = \gcd(k, L_N)$ (and through $\operatorname{rad}_N(k) = \gcd(k, N\#)$ for squarefree weights). By Dirichlet polarization,
  $$2\widetilde{\mathcal{D}}_N(M_0, M; c) = -E_{N,c}(M_0, M) + s_{N,c}(M_0+M+1)^2 - s_{N,c}(M_0+1)^2.$$
  Thus $\widetilde{\mathcal{D}}_N(M_0, M; c) \le 0$ holds for **all** weights $c$ iff the window endpoints share the same observation fiber $\sigma_N(M_0+M+1) = \sigma_N(M_0+1)$ (which recurs at scale $O(\log N)$–$O(N)$ rather than the full period $L_N = e^{\psi(N)}$), and holds unconditionally for $c = \mu$ for **every** starting phase $M_0$ whenever $M_0 + M + 1$ lands in the zero cone $s_{N,\mu}(M_0+M+1) = 0$.

### Pillar 2: Dual Arithmetic Invariants: Valuation Clocks $\tau_{\mathrm{vis}}(q) \leftrightarrow$ Prime-Power Chains $\Lambda(p^r) = \log p$
*Defeats Walls 1, 5, 7, 9, & 10; underpins `BVI`, `LI`, `RB`, `PBM`, `DR`, `BAG`, `CHMD`, `SZ`, `PA`, `GTA`, `TH`, `W1C`.*

Any operator using only the linear explicit formula is blind to the two arithmetic invariants that separate $\zeta(s)$ from general Dirichlet polynomials, Beurling countermodels (`Zeta23Countermodel`), and Davenport–Heilbronn Hurwitz functions:
1. **Multiplicative Valuation Constantness ($\Lambda(p^r) = \log p$ for all $r \ge 1$):** Encoded in the bipartite $p$-adic prime-chain variance `CHMDPrimeChain.varianceEnergy` on $N = m p^r n$ ($p \nmid m n$) and its continuous density `chainIntegral`.
2. **Additive Successor Visibility Clocks ($\tau_{\mathrm{vis}}(q) = q / \operatorname{rad}(q)$):** Under additive translation $k \mapsto k + h$, a prime-power divisor $p^r$ changes its valuation state iff $\tau_{\mathrm{vis}}(p^r) = p^{a-1} \mid h$, linked to von Mangoldt by $\Lambda(d) = \log(d / \tau_{\mathrm{vis}}(d))$ (`ValuationClockChainBridge`).

`THIM` locks these two invariants together:
- **Sharp Totient Observability Threshold (`TotientObservabilityThresholdAndValuationFiberCollision`, `ClockScheduleSynthesisAndPrimePowerPhaseRecovery`):**
  $W$ consecutive additive observations $t \mapsto \gcd(k + t, p^a)$ uniquely determine the phase $k \bmod p^a$ **iff** $W \ge \varphi(p^a) = p^a - \tau_{\mathrm{vis}}(p^a)$, yielding the global horizon observability threshold $\Phi_{\max}(N) = \max_{p^a \le N} \varphi(p^a) < N$ (and $\Phi_{\mathrm{rad}}(N) = \max_{p \le N}(p - 1)$ for squarefree weights) —performing phase recovery inside $\mathbb{N}$ *before* any Mellin/Laguerre transform (bypassing Wall 10).
- **Prime-Chain Spectral Cutoff (`PrimeChainSieveBridgeAndSpectralCutoff`):**
  When discrete sieve observables $s_{H,c}$ with squarefree-supported $c$ are inserted into `CHMDPrimeChain.varianceEnergy`, radical invariance $s_{H,c}(p^r b) = s_{H,c}(p b)$ ($r \ge 1, p \nmid b$) annihilates all higher-shell ($r \ge 2$) scatter, collapsing every active prime chain $p \le H$ to a rank-1 ground-state jump $s_{H/p, c(p\cdot)}(b)^2$ and vanishing identically for $p > H$.

### Pillar 3: Trans-Horizon Buchstab–Sawtooth Filtration & All-Octave Fermi–Nyman Renormalization
*Defeats Walls 1 & 10; underpins `MC`, `CTF`, `PM (FZZ-P)`, `BVI`, `RP`, `SEC`.*

Instead of expanding $\mathcal{E}_N(M; \mu) = \sum_{k=1}^M s_{N,\mu}(k)^2$ in characters modulo $L_N$, `THIM` evolves the horizon $N$ **downward** from the trivial top identity $\mathcal{E}_M(M; \mu) = 1$ across squarefree steps $n + 1 \in [N+1, M]$ (`BuchstabHorizonFiltrationAndSawtoothEvolution`, `DownwardBuchstabL2TelescopeAndSawtoothCoupling`):
- **Composite Steps via Dirichlet Hyperbola Involution (`ComplementaryQuotientAndSecondOctaveLaw`, `CompositeSquarefreeStepAndMultiOctaveL2Energy`, `ThirdBandCompositeStepAndLinearL2EnergyBounds`):**
  The complementary-quotient involution $d \leftrightarrow k/d$ evaluates every step $\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu)$ in bands $B = \lfloor M/(n+1) \rfloor \in \{1, 2, 3\}$ by $(2, 3)$-adic divisibility of $n + 1$ without requiring $n + 1$ to be prime.
- **Centered $(B - 2)$ Square Completion (`CenteredSquareCompletionAndMultiBandResidueCancellation`):**
  In band $B \ge 3$, completing the square with weight $B - 2$ gives
  $$(B - 2)\bigl(\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+1}(M; \mu)\bigr) = \bigl(\mu(n+1) S_2\bigr)^2 - \bigl((B - 2)\mu(n+1)^2 + \mu(n+1) S_2\bigr)^2 \le \mu(n+1)^2 S_2^2,$$
  removing the linear ground-term penalty and proving that consecutive parity pairs $(2m, 2m+1)$ cancel the $+1$ third-band excursion whenever $\gcd(2m+1, 3) = 1$.
- **Second-Octave Fermi Curvature–Gradient Reciprocity (`BuchstabFermiCovarianceAndQuotientChainBridge`, `PolarRadicalInvarianceNodalDriftAndFermiGradientBridge`):**
  Across the second trans-horizon octave $m \in [N, 2N-1]$, the second-order Fermi cell difference $\Delta^2 F(2m)$ centered at $2m+1$ plus the forward gradient $\operatorname{addDiff}(s_{N,\mu})(2m+1)$ equals $-2\mu(m+1)$, enforcing the unconditional lower bound $\sum_{m=N}^{2N-1} \bigl((\Delta^2 F(2m))^2 + \operatorname{addDiff}(s_{N,\mu})(2m+1)^2\bigr) \ge 2\,\#(\operatorname{oddSquarefreeWindow} N)$.
- **Calibrated Active Sawtooth Sampling (`ActiveSawtoothPowerSamplingAndCalibratedRecovery`, `ActiveSawtoothInterpolationAndSharpConditioning`):**
  Reconstructs active divisor sawtooth defects from finite power-sampling nodes with explicit Vandermonde/Lagrange conditioning, isolating the trans-horizon sawtooth drift that governs the $L^2((0, 1/N), dx/x^2)$ Báez–Duarte tail.

### Pillar 4: Sign-Preserving Odd-Sector Coercivity, Two-Regime Origin-Collar Duality, & Off-Line Packet Exclusion
*Defeats Walls 2, 3, 4, 6, 8, 13, & 15; underpins `CHMD`, `BiScaleUncertainty`, `OWU`, `EWU`, `RW`, `WL`, `SZ`, `PA`, `GTA`, `HF`, `TG`, `TH`, `TT`, `WD`, `XN`, `FEL`, `HJ`, `W1C`.*

- **Sign-Preserving Nodal-Modulus Balance & Chiral-Drift Tightening (`OddEigenvectorNodalModulusBalanceAndFourthBandStepLaw`, `OddEigenvectorHalfMassLobeAndStrictPrimeShiftClosure`, `PolarRadicalInvarianceNodalDriftAndFermiGradientBridge`):**
  Replacing naive modulus contraction $v \mapsto |v|$ (which loses sign opposition on odd states, Wall 13), reflection anti-symmetry of any odd `SourceGraph` vector $q$ forces automatic half-mass lobe balance $\int q^+ = \int q^-$, so `absGraph q` is orthogonal to both $q$ and `signedRadical`. If $\operatorname{resolvent} v = \nu\,v$ ($\nu > 0$, $v \in \text{oddSector}$, $q = \operatorname{rieszLift} v$), then:
  $$\operatorname{sourceEnergy}(\operatorname{absGraph} q) - 4\operatorname{sourcePair}(q^+, q^-) = \frac{1 - 2\nu}{\nu}\|q.\text{fst}\|^2, \qquad \operatorname{sourceEnergy}(\operatorname{absGraph} q) - 4\operatorname{sourceEnergy}(q^+) = \frac{2\nu - 1}{\nu}\|q.\text{fst}\|^2,$$
  and the primitive modulus `primGraph (absGraph q)` has exact cross-lobe Rayleigh excess $4\bigl(\langle \operatorname{resolvent} q^+.\text{fst}, q^-.\text{fst}\rangle_{\mathbb{R}} - 2(1-\nu)\langle q^+.\text{fst}, \text{oneL}\rangle_{\mathbb{R}}\langle q^-.\text{fst}, \text{oneL}\rangle_{\mathbb{R}}\bigr)$ with $0 < -\nu^2\operatorname{sourcePair}(q^+, q^-) \le \langle \operatorname{resolvent} q^+.\text{fst}, q^-.\text{fst}\rangle_{\mathbb{R}}$. Because `oddPrimeDriftOperator` anticommutes with `reflectMass`, $\langle \operatorname{oddPrimeDriftOperator} q.\text{fst}, q.\text{fst}\rangle_{\mathbb{R}} = 0$, tightening the prime-shift energy bound on **both** nodal lobes by $+\frac{1}{4}\langle \operatorname{oddPrimeDriftOperator} q.\text{fst}, (\operatorname{absGraph} q).\text{fst}\rangle_{\mathbb{R}}^2$.
- **Symmetrized $(+\beta, -\beta)$ Off-Line Hyperbolic Coercivity (`OffLineHyperbolicPrimeChainExcessAndCardinalRecurrence`, `AllCutPrimeChainCoercivityAndContinuousDensityBridge`, `CompactWindowedOfflineChainIntegralAndOriginCollarDuality`):**
  Functional-equation pairing $(+\beta, -\beta)$ breaks critical-line conjugation symmetry $\gamma \leftrightarrow \bar{\gamma}$ (defeating Turán clustering, Wall 3): on both discrete prime chains and continuous `chainIntegral` densities, the symmetrized off-line energy exceeds the $\beta = 0$ baseline by non-negative radial hyperbolic jumps $(e^{\beta \Delta} - 1)^2 + (e^{-\beta \Delta} - 1)^2 \ge (\beta \Delta)^2$ plus phase amplification, yielding a $\frac{1}{2}\beta^2 \sum_{p \mid N} (\log p)^3$ ground-cut floor.
- **Two-Regime Origin-Collar Duality, Collective Chebyshev Transport, & Unit-Coefficient `sinh` Absorption (`OddProfileCollarToContinuumArchimedeanBridge`, `SupportRadiusCollarCutoffAndAllScaleObstacleBBridge`, `CollectiveLowPrimeChebyshevTransportAndSinhAbsorption`):**
  For even $w \in C^2_c((-R, R))$ and $a > 0$, the origin-crossing prime collar is controlled across all scales without prime-by-prime Schur blowup:
  1. **High Primes ($2R \le \log d \le a - R$):** Outside $\operatorname{supp}(w)$, $(w(x) - w(\log d - x))^2 = w(x)^2 = (w(x) - w(x + \log d))^2$ and $m_a(\log d - x) < m_a(x + \log d)$, so high-prime collars are dominated **1-for-1 by half-line prime shift jumps with zero archimedean cost**.
  2. **Low Primes ($\log d < 2R$) via Midpoint-Reflection Diagonalization & Collective Chebyshev Transport:** Adding the $\Theta$-Doob sum-square to `oddProfileCollarDiffSq` forms `oddProfileCollarMixed`, cancelling the 2-point cross term $w(x)w(t-x)$ under midpoint reflection $x \mapsto t - x$ and collapsing the integral to twice a **1-point diagonal potential** $G(t)$ that feeds directly into collective Stieltjes integration by parts against the Chebyshev discrepancy $\Delta(s) = \psi_0(e^s) - (e^s - \log 2 - 2)$.
  3. **Global $x \to 0^+$ `sinh` Dominance & Convex Gauge Interpolation ($\theta \le 1$):** Because $m_a(0) = 0$ and $s \le \sinh s$, $f_a(x)\cosh(x/2) \le \operatorname{coshSinhPolarRatio}(a, M, R)\sinh(x/2)$ holds globally on $[0, R]$ **all the way down to $x = 0$ without any origin cutoff $\delta > 0$**. Via `convex_doob_chain_sinh_interpolation`, whenever $\operatorname{coshSinhPolarRatio}(a, M, R) \le \theta \le 1$, the $+2\theta\int_0^\infty m_a(x)\sinh(x/2)w(x)^2\,dx$ potential absorbs `phiDoobCoshMass` while $\sum_q \operatorname{chainIntegral}(\operatorname{oddPolarWeight}\,a\,w, q) \ge 0$ absorbs all prime collars with **net coefficient $\theta \le 1$ uniformly in $R$**.

### Pillar 5: Weak-Compactness & Topological Sub-Unit Gate Closure
*Defeats Walls 3 & 14; underpins `CTF`, `BVI`, `PM`, `CHMD`, `TG`, `RW`, `OWU`, `EWU`, `SZ`, `PA`, `GTA`.*

- **Arithmetic / Hilbert Closure (`CTF`, `BVI`, `PM`):**
  To close the Báez–Duarte / Nyman–Beurling distance $d_N \to 0$, one does not need explicit inverse Gram matrix entries: by weak compactness in Hilbert space and Mazur's lemma, proving uniform boundedness of the trans-horizon sawtooth remainder in $L^2((0, 1/N), dx/x^2)$ suffices to force strong $L^2$ closure.
- **Spectral / Integer-Multiplicity Closure (`CHMD`, `TG`, `RW`, `OWU`, `EWU`, `SZ`):**
  Because the dimension of any above-threshold bound-state eigenspace ($\mu \in (1/2, 1)$) is a non-negative integer, any strict operator-norm contraction $\le 1/2$ on $\mathcal{H}_{\mathrm{odd}} / \operatorname{signedRadical}$ or trace bound $< 1$ on the bound-state projection forces the multiplicity to be strictly $0$.

---

## 4. Traps, Sharp Boundaries, and Permanent Dead Ends

### 4.1 Cross-Programme Permanent Dead Ends (from `hard-obstacles-summary-1810.md`)

| Permanent Dead End | Why It Is Mathematically Impossible & What `THIM` Uses Instead |
| :--- | :--- |
| **1. Using sub-horizon ($M < N$) or full-period ($L_N = e^{\psi(N)}$) Ramanujan identities in trans-horizon regimes ($N < M \le N^2$)** | Sub-horizon identities hold before the sawtooth wakes up; incomplete-period character expansions leave $O((\sum_{d \le N}|c(d)|)^2)$ remainders (Wall 1). Use **downward Buchstab $L^2$ telescoping**, **iso-state window polarization**, and **$(B-2)$ centered square completions** (Pillars 1 & 3). |
| **2. Applying $v \mapsto |v|$ modulus contraction on odd/antisymmetric states** | Modulus folding destroys sign opposition between positive and negative nodal lobes, losing the factor of $2$ between $\mu = 1/2$ and $\mu = 1$ (Wall 13). Use **half-mass nodal-modulus balance**, **cross-lobe primitive modulus Rayleigh excess**, and **chiral-drift tightening** (Pillar 4). |
| **3. Using differences of autocorrelations or unprojected Müntz-ramp tails** | Differences of autocorrelations lack Bochner positivity ($\widehat{F} \ge 0$), and unprojected Müntz-ramp tails have positive Weil energy regardless of RH (Walls 8 & 11). Always work on **`oddPrimitivePart`** ($\perp \operatorname{signedRadical}$) with genuine single-autocorrelation or convex Doob–`sinh` gauges (Pillars 1 & 4). |
| **4. Pushing stationary-phase Mellin/Laguerre transforms across the $s = 1$ pole before discrete cancellation** | Stationary-phase saddle continuation hits the $s = 1$ pole and exponential Gram conditioning blowup (Wall 10). Perform additive-to-multiplicative cancellation **inside $\mathbb{N}$ first** via valuation visibility clocks $\tau_{\mathrm{vis}}(q) = q/\operatorname{rad}(q)$ and totient thresholds $\Phi_{\max}(N) < N$ (Pillar 2). |
| **5. Using linear explicit-formula trace bounds against off-line zero clusters** | Linear trace sums suffer Turán power-sum dilution $c_1^K$ under zero clustering and cannot distinguish critical-line pairs from off-line quadruplets (Walls 3 & 5). Use **symmetrized $(+\beta, -\beta)$ hyperbolic prime-chain variance** or **integer-multiplicity bound-state projections** (Pillars 2, 4, & 5). |
| **6. Using individual-prime Schur bounds on low-prime collars ($\log d < 2R$) as $R \to \infty$** | Bounding each low prime separately against the 2D absorbed archimedean integral inflates the cumulative multiplier to $\operatorname{supportArchBudget}(R, \delta, L) \sim e^{8.5 R} \gg 1$. Use **midpoint-reflection 1-point diagonalization + collective Chebyshev Stieltjes transport** or **unit-coefficient convex Doob–`sinh` interpolation** (Pillar 4). |

### 4.2 Sharp Formal Boundaries & Technical Traps in `TransHorizonIncidenceMechanics`

| Formal Trap | Exact Counterexample / Theorem & Correct Mechanism |
| :--- | :--- |
| **Assuming $+1$ descends to observation states $\sigma_N(k)$ for $N \ge 3$** | Fails for every $N \ge 3$: $\sigma_N(1) = \sigma_N(5) = 1$, but $\sigma_N(2) = 2 \ne 6 = \sigma_N(6)$ (`horizonObservationState_successor_congr_iff`). Use consecutive traces of length $\Phi_{\max}(N) = \max_{p^a \le N}\varphi(p^a) < N$. |
| **Using fewer than $\varphi(p^a)$ steps to recover $k \bmod p^a$ from $\gcd(k+t, p^a)$** | At $W = \varphi(p^a) - 1$, $k = 1$ and $\ell = 1 + p^{a-1}$ produce identical $\gcd(\cdot, p^a)$ traces on $0 \le t < \varphi(p^a) - 1$ (`gcd_prime_pow_collision_below_totient`). |
| **Assuming $|s_{N,\mu}(k)| \le 1$ holds beyond $k = 5N$** | Holds for all $2 \le k \le 5N$ (`FourthBandEnvelopeAndSharpFiveHorizonBoundary`), but fails at $k = 5N + 5 = 30p$, $N = 6p - 1$ for every prime $p > 5$, where $s_{N,\mu}(30p) = +2$. |
| **Assuming step-by-step monotonicity $\mathcal{E}_{n+1}(M; \mu) \le \mathcal{E}_n(M; \mu)$ in the third band** | When $3(n+1) \le M < 4(n+1)$, $\gcd(n+1, 6) = 1$, and $n+1$ is squarefree, $\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) = +1 > 0$. Pair consecutive parity steps $(2m, 2m+1)$ (`CenteredSquareCompletionAndMultiBandResidueCancellation`). |
| **Splitting $[0, R]$ at an origin cutoff $\delta > 0$ to bound `phiDoobCoshMass` by the `sinh` potential** | In `phiDoobCoshMass (oddPolarWeight a w ^ 2)`, both factors of $m_a(x)$ are evaluated at the **same** point $x$. Since $m_a(0) = 0$ and $x \le 2\sinh(x/2)$, $f_a(x)\cosh(x/2)/\sinh(x/2)$ is bounded globally on $[0, R]$ down to $x = 0$ with no $\delta > 0$ cutoff (`oddPolarFunction_mul_cosh_le_sinh_of_deriv_bound`). |
| **Trying to cancel `sourcePair (oddPolarVectorAt a ha) q` for a fixed `q` by varying `a`** | Since $\Psi_a - \Psi_b \in \operatorname{signedRadical}$, $\operatorname{sourcePair}(\Psi_a, q) = \langle q.\text{fst}, \operatorname{tanhL}\rangle_{\mathbb{R}}$ is independent of $a$ (`sourcePair_oddPolarVectorAt_eq_of_admissible`). Project to `oddPrimitivePart b hb q` instead. |
| **Importing unbuilt heavy modules into leaf files** | Always verify `.lake/build/lib/lean/` before adding external imports. Compile every new leaf module with `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/TransHorizonIncidenceMechanics/<Module>.olean GaloisForLFunctions/TransHorizonIncidenceMechanics/<Module>.lean`. |

---

## 5. Active Research Frontier Across All Five Pillars

1. **Collective Chebyshev Transport on the 1-Point Diagonal Collar Kernel (Pillars 2 & 4 — Obstacles 2, 3, 6):**
   Apply `sum_vonMangoldtAtom_lt_eq_pole_add_chebyshevDiscrepancy_transport` directly to a smoothed 1-point diagonal collar-mixed potential $G(t) = 2\int_0^t m_a(x)\,\operatorname{collarMixedDiagKernel}(a, t, x)\,w(x)^2\,dx$ on $[0, 2R]$ so that the PNT main term $2 G(0) + \int_0^{2R} e^{s/2} G(s)\,ds$ and Chebyshev discrepancy derivative transport $-\int_0^{2R} \Delta(s) G'(s)\,ds$ are absorbed directly against the 2D archimedean jump and `sinh` potentials.
2. **Coupling Primitive Modulus Rayleigh Excess to Nodal Chiral Drift on Quotient Eigenvectors (Pillars 1, 4, & 5 — Obstacles 2 & 3):**
   Combine the cross-lobe Rayleigh excess of `primGraph (absGraph q)` (`odd_eigenvector_primGraph_absGraph_rayleigh_excess_and_cross_pos`) and the single-lobe `stationaryResolvent (absGraph q)` Cauchy–Schwarz bound (`odd_eigenvector_stationaryResolvent_absGraph_via_posGraph_snd`) with the nodal chiral-drift tightening $+\frac{1}{4}\langle \operatorname{oddPrimeDriftOperator} q.\text{fst}, (\operatorname{absGraph} q).\text{fst}\rangle_{\mathbb{R}}^2$ to force a strict sub-unit contraction on above-threshold odd eigenvectors ($\mu \in (1/2, 1)$).
3. **Multi-Band $(B - 2)$ Square Completion, Higher-Octave Fermi Reciprocity, & $L^2((0, 1/N), dx/x^2)$ Tail Boundedness (Pillars 1, 3, & 5 — Obstacles 1 & 4):**
   Combine the $(B - 2)$ centered square completion (`CenteredSquareCompletionAndMultiBandResidueCancellation`), zero-cone iso-state checkpoints $s_{N,\mu}(k) = 0$, and multi-octave Fermi curvature–gradient reciprocity to bound the trans-horizon sawtooth tail uniformly in $L^2((0, 1/N), dx/x^2)$ for `CTF`, `MC`, `PM`, `BVI`, and `RP`.
4. **Multi-Lag Visibility-Clock Conditioning for Dirichlet Tails & Non-Stationary Transport (Pillars 1 & 2 — Obstacles 4 & 5):**
   Use the totient observability threshold $\Phi_{\max}(N) < N$, composite clock wavelet tensors (`CompositeClockWaveletTensorAndPhaseRecovery`), and prime-chain spectral cutoff (`PrimeChainSieveBridgeAndSpectralCutoff`) to decouple small-prime observation fibers $\sigma_N(k)$ from high-prime Dirichlet/Mellin tails in `LI`, `RB`, `PBM`, `DR`, and `BAG`.
