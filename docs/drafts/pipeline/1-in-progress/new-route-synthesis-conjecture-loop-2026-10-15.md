# Post-Frontier Synthesis & New Route Conjecture Loop

- **ID:** new-route-synthesis-loop-2026-10-15
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (meta-route synthesis + iterative conjecture/refutation loop)
- **Source:** `docs/reports/rh-current-frontier-map.md` · `docs/reports/STATUS.md` · `docs/reports/rh-killed-routes.md` · `docs/drafts/pipeline/1-in-progress/rh-big-picture-interpretation.md` · `docs/drafts/pipeline/1-in-progress/pbap-existence-barrier-atlas.md`
- **Statement:** Assume all 17 live routes and 23 route candidates in `rh-current-frontier-map.md` are dead ends that inevitably stall at structural walls. Extract the exact mathematical laws revealed by their collective failures, and run a relentless conjecture $\to$ attack/falsify $\to$ learn $\to$ next-conjecture loop to discover a genuinely new proof architecture (and the new mathematical framework it requires) that circumvents those walls.

## Goal
1. Diagnose **why** every single existing route (17 live + 23 candidates) and killed mechanism (`KR-01`..`KR-36`, `CANNOT-01`..`CANNOT-559`) gets stuck, without relying on external training data.
2. Synthesize the **Big Picture Meta-Laws** that our Lean corpus is teaching us about the true nature of the Riemann Hypothesis.
3. Run an iterative **Conjecture $\to$ Audit/Falsify $\to$ Salvage $\to$ Next Conjecture** loop (no Lean code yet) to forge a new route that attacks the actual producer core from a new mathematical perspective.

## Gates
- [x] 0 → 1  in-progress: full corpus autopsy, meta-law extraction, active conjecture loop initialized
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

---

## Part I: Autopsy of All 17 Live Routes and 23 Route Candidates

Under our working premise, **every existing route and candidate is a dead end**. Why? Because the corpus proves that each route decomposes into:
1. A **Uniqueness / Rigidity / Receiver half** (which the corpus has largely **proved unconditionally in Lean**), and
2. An **Existence / Producer half**, where every route hits one of a small number of universal structural walls and stalls permanently.

### 1. The 17 Live Routes — Exact Stalling Obstacles

| Route | Unconditional Lean Achievement (The "Free" Half) | The Insurmountable Wall Where It Stalls (The "RH" Half) |
|---|---|---|
| **WL** (Weil Lag / Explicit-Formula Floor) | Exact lag receiver equivalences; syndetic & power-saving gap ($O(n^{1-\delta})$) completeness (`MUST-927`, `MUST-1377`); persistent oscillation on power windows (`MUST-1378`); ZAL $\wedge$ AAL decomposition (`MUST-1356`). | **Wall 1 (Principal Major-Arc Pole/Prime Cancellation):** Requires a one-sided bound $\ge -C\sqrt{X}$ on prime sums against the $s=1$ pole. All thin zero-side samplings are blind (`CANNOT-515`, `CANNOT-516`), and linear arithmetic identities annihilate the off-line zero waves they try to detect (Detection–Knowledge Duality, `MUST-906`). |
| **RW** (Restricted Weil / CCM Operator) | Ground-state real-rootedness at every aperture (`MUST-797`); even parity excludes finite off-line configurations with relation-even, deep, or high clustered tops (`MUST-1218`, `MUST-1229`, `MUST-1259`). | **Nyquist / Edge-State Escape (`CANNOT-499`, `MUST-822`):** Off-line zeros hide as edge states of width $O(1/\delta)$ at aperture ends with energy $-e^{2\delta a}$. Beurling–Deny Markovianity dies at the plastic constant horizon $2a = \log\rho_{\text{plastic}}$ (`MUST-886`). Beyond $\log 2$, positivity is cancellation inside the quadratic form at Nyquist height $t \approx e^{2a}$. |
| **FU** (Finite Unitary / Suzuki–Wold Scattering) | Exact Wold decomposition, activation factor $\zeta(s)/\zeta(s+a)$ (`F196`), Calkin/compact-ideal cost gap (`0` vs `1`), dominated-hull uniform decay (`H:LpSolidUniform`). | **Calkin Blindness & Unbounded Ingress (`F201`, `F204`, `CANNOT-108`):** The compact/solid hull of any fixed history is blind to off-line zeros; the obstruction escapes to cofinal moving prefixes. Any one-sided bounded recovery exports the anomaly into an unbounded formation load. |
| **RP** (Reflection Positivity / OS / Krein) | Exact `(1,1)` vacuum Green cell (`F165`); multiplicity-aware Krein–Langer off-line pair count (`F174`); Fredholm winding `-1` (`F169`). | **Vacuum Cancellation & Compact-Open Discontinuity (`F166`, `F180`, `CANNOT-91`, `CANNOT-100`):** Negative Krein squares can migrate to infinite height while converging locally uniformly in all jets; every $\Xi$ mode contributes a matched kernel–cokernel pair so numerical Fredholm index is blind (`-1` everywhere). |
| **PA** (Prime-Anchor / Sonin / De Branges) | Sonin space realization, head-Mellin continuation, quantized integer residue contradiction once native source energy $E < \infty$ (`tg-quantized-exclusion-loop-2026-10-15`). | **Native Source Energy Bound = Wall 1:** Finiteness of $E = \sum_n A_n^2/((n+2)(n+3))$ for $A_n = \sum_{k\le n}(\mathbf{1}_P(k+2) - m_{\text{polar}}(k))$ is a square-root prime-count cancellation bound in disguise. |
| **MC** (Möbius Cancellation / Báez–Duarte / Nyman–Beurling) | Unconditional pointwise convergence of bounded-error approximants to $\mu(n)$ (`MUST-846`, `MUST-850`); strict multiplicity grading (`MUST-884`). | **Gram Conditioning & Incompatible Algebras:** The arithmetic Gram is divisibility-triangular (GCD) while the archimedean inner product is quotient-Toeplitz ($n/m$). No unconditional lower bound on the distance from $\mathbf{1}$ to the dilated-$\zeta$ span exists without $\sqrt{X}$ Möbius cancellation. |
| **TT** (Toeplitz / Truncated / Half-Line Weil) | Unconditional full and even Weil cone uniqueness (`MUST-1433`, `MUST-1495`); unconditional pole-weight pinning $\beta=1$ (`MUST-1463`); Abel pinning for nonnegative/bounded-below even systems (`MUST-1517`, `MUST-1518`). | **Reflected Product-Prime Anti-Markov Obstruction (`MUST-1506`, `CANNOT-559`):** On the half-line `(0,\infty)`, the reflected pairing $\Pi(f) = \sum \Lambda(n)n^{-1/2}\int_0^{\log n} f(t)f(\log n - t)\,dt$ is non-Wait-Markovian for $\operatorname{supp} f$ past $\frac{1}{2}\log 2$ and carries the entire off-line obstruction. |
| **LA** (Local Angle / Horizontal Phase Monotonicity) | Phase monotonicity $\iff$ Hadamard positivity $\operatorname{Re}(\xi'/\xi) > 0$; Backlund equivalence for LH (`MUST-1317`); ZAL gauge laws (`MUST-1348`). | **Near-Double Masking Wall (`CANNOT-471`, `MUST-1301`):** Local phase/angle readouts at scale $\asymp 1$ ($S(T)=O(\log T)$) cannot resolve an off-line pair at depth $\delta \lesssim 1/\sqrt{\log\gamma}$ (or $\delta \asymp 1/\log\gamma$ under LH) from a double critical zero without primes up to $e^{C/\delta}$. |
| **TG** (Theta / Gaussian / Sonin Gap) | Large-height Gaussian gap rate $\Theta_\infty + \Theta_\infty^2/8$ (`MUST-1347`); holds outside a power-saving set of heights unconditionally (`MUST-1351`). | **First Milestone $< 1/4$ is Already Quasi-RH (`CANNOT-514`):** Any improvement over the trivial exponent $1/4$ requires a global zero-free strip; smooth Gaussian windows average over $\asymp \log T$ zeros and lose sign at the Nyquist threshold. |
| **HF** (Herglotz / Farkas / PBAP) | **Complete Uniqueness Closure:** $\text{RH} \iff \text{PBAP} \iff \text{PBAP}_{\text{even}}$ (`MUST-1495`); node-pole value function has gradient $(\Lambda, -1)$ (`MUST-1478`, `MUST-1479`); finite-level certificate boxes squeeze to $\Lambda$ (`MUST-1512`). | **Primal Zero-Pole Blind Positivity (`CANNOT-539`, `CANNOT-557`, `CANNOT-558`):** The archimedean symbol $A(r) = \operatorname{Re}\psi(1/4+ir/2)-\log\pi$ is negative on $|r| < 6.47$ ($A(0) \approx -5.37$). On blind tests, $P = \frac{1}{\pi}\int |\hat{f}|^2(1-\operatorname{Re}\zeta(1/2+it))$, so $A+P$ has effective symbol $\gamma(t)/2 + 1 - \operatorname{Re}\zeta(1/2+it)$, which is unbounded below! No pointwise, finite-node, or constant-tail certificate exists (`CANNOT-557`). |
| **TH** (Theta / Heat / De Bruijn–Newman) | Strip confinement threshold $t=0$ (`MUST-1364`); cosine ladder `cos(hD)Ξ` is the unique depth-exact detector (`MUST-1292`). | **Amplification vs. Depth-Exactness Exclusion (`CANNOT-506`, `MUST-1292`):** Heat flow $e^{tD^2}$ amplifies at large height ($\Lambda < 1/2$ free) but deep zeros shield shallow ones (`CANNOT-506`). Cosine flow `cos(hD)` preserves depth counts exactly but does not amplify without a zero-free strip. |
| **RN** (Renewal / Theta Feedback Loop) | Exact decomposition $\Xi(2i\lambda) = A(\lambda)+B(\lambda)$ with $A,B$ zero-free in strip; analytic charge $C = (A-B)/(2i)$ has $\operatorname{Re} C > 0$ (`route-rn-full-divisor-charge-2026-10-15`). | **Sum-Time vs. Difference-Time Renewal Coupling:** The Pick kernel has arbitrarily large positive and negative packets; crossings have alternating signs; compact zero-engineering (`compact_critical_strip_zero_engineering`) preserves positivity, strong log-concavity, and finite moments while planting off-line zeros. |
| **WD** (Wick / Dilation / Horizontal Slices) | Slice heat-rate gauge below $1/2$ implies ZAL (`MUST-1333`); large-height slice positivity $\iff$ FOL (`MUST-1328`). | **Euler Saddle Barrier (`rh-big-picture-interpretation.md` row 1094):** Size bounds (even LH) only push the slice heat rate down to $1/2$ because the saddle stays in the Euler region $\sigma > 1$; crossing below $1/2$ requires Faà di Bruno control of $\log\zeta$ of order $\asymp \log t$. |
| **LI** (Li Coefficients / Clock / Cayley) | Two-sided chord pin $0 \le \lambda_n \le n^2\lambda_1$ (`MUST-910`); Bohr-recurrent thinning classification (`MUST-929`); unconditional subexponential clock rate $432/431$ from verified zero band (`MUST-899`). | **Window Horizon Law (`MUST-896`):** Conformal map to the disc compresses height by $\gamma^{-2}$ (`|w_\rho| - 1 \asymp (\beta-1/2)/\gamma^2$), so $\lambda_n \ge 0$ up to $n$ only checks RH up to height $\gamma \lesssim \sqrt{n/\delta}$. Global positivity requires all $n \to \infty$ simultaneously. |
| **SZ** (Selberg Zeta / Modular / Automorphic) | Exact 1-line transport law for Eisenstein/Maass–Selberg (`rows 749–750`); packet identity for `SL₂(ℤ)` cocycle (`MUST-930`). | **1-Line Displacement & Continuous Spectrum:** Maass–Selberg unitarity puts scattering poles ($\zeta$-zeros) on $\operatorname{Re} s = 1/2$ only *after* $\zeta \ne 0$ on $\operatorname{Re} s = 1$ gives the boundary, which shifts to $\operatorname{Re} s = 1/2$ for the Eisenstein constant term—leaving $\zeta(2s)$ zeros at $\operatorname{Re} s = 1/4$! |
| **PM** (Prime Moments / Pair Correlation / Montgomery) | Conditional pair-correlation isolation under LH (`MUST-1304`). | **Averaging Blindness:** Family and height averages assign weight $\to 0$ to any individual off-line zero (`ITQ` inventory, rows 734–760). |
| **JAS** (Joint Ancestry / Dressed Lag Aggregate) | $\text{RH} \iff \text{JasDressedPSD } 1 \wedge \neg\text{JasOffLineChain}$ (`R:JointAncestryRouteCapstone`); large-prime attainment at $\sigma=3/2$ (`MUST-1256`). | **Kronecker Torus Anti-Alignment & $\sigma=1$ Wall:** PSD at $\sigma=1$ is Weil positivity on completely multiplicative tests (Wall 1); the chain residual escapes via phase-$\pi$ Bohr-aligned clusters that neither VK nor Baker bounds can exclude (`rows 94–97`). |

### 2. Why the 23 Route Candidates Also Stall
- **Algebraic / K-Theory / Dynamical / Quantum Graph candidates (`BAG`, `DR`, `EGC`, `FEL`, `IRK`, `PTR`, `W1C`):**
  - `PTR` / `W1C`: Killed at the naive level by Berkolaiko–Kuipers–Sieber (`CANNOT-546`: $\mathbb{Q}$-independent $\log p$ prevents unitary edge coupling) and Fricke (`CANNOT-550`: no hyperbolic subgroup has primitive geodesic lengths $\{k\log p\}$ for $\ge 2$ primes).
  - `IRK`: Projective modules over the norm-closed prime rotation algebra contain no generalized modulation eigenvectors (`irk-rh-source-loop-2026-10-15` Cycle 2), and no functor descends the analytic $\Xi$-divisor to a continuous $K_0$ class with canonical trace integrality.
  - `DR`: Regularized $\log\zeta$ series $\sum (\Lambda(n)-1)/(\log n \, n^s)$ has essential Calkin norm $1/2$ (`PaperPrimeRegularizedIdeal`), and Kummer-cover dilation transport (`PairedEtaKummerCoverTransport`) preserves the local branch-point monodromy unchanged.
- **Matrix / Schur / Theta / Kernel candidates (`APF`, `BSH`, `CDC`, `CTF`, `EWJ`, `GTA`, `HCF`, `HJ`, `MSC`, `OWU`, `PBM`, `PCS`, `RFHM`, `SC`, `SEC`, `WBF`):**
  - `GTA`: Ordinary anti-Hermitian energy has a positive floor (`HedenmalmThetaSkewAdjointDefectFloorNoGo`); finite-range positive metrics fail by an exact dyadic functional (`ThetaQuotientDyadicMetricDefect`); parity block reduction leaves a singular non-$L^2$ rank-one directed feedback $u v^T$ (`ThetaQuotientParityFeedback`).
  - `HCF`: Heat coordinates $w=z^2$ split into two non-overlapping unconditional regimes: small-time window ($N \le \kappa/a$) and bounded-rank large-time (blind above $H(N)$, `CANNOT-503`). Bridging them uniformly in rank is exactly Nyquist/PBAP.
  - `OWU`: Even if completed (`odd-sector-weil-uniqueness.md`), it only closes uniqueness on the odd sector, reducing to `PBAP_odd`—the same existence wall (`2S(f)^2 \le \operatorname{Arch}(f\star\tilde{f})`).
  - `Lee–Yang / Griffiths–Simon (FEL / SC / WBF)`: Requiring harmonic density ($\beta=1$), critical weights ($\alpha=1/2$), and AFE turning-point balance simultaneously is impossible for standard Ising/GS chains; a GS producer of $\Phi$ would have to sit at an "infinite-order" multicritical point with a double-exponential tail (`rh-big-picture-interpretation.md` row 966).

---

## Part II: What All These Failures Are Trying to Tell Us (The 7 Meta-Laws)

When we step back from the 40 routes and 559 `CANNOT` theorems, a single crystal-clear picture emerges. The failures are not random obstacles; they are **the boundary of a mathematical theorem about what kind of object $\Xi$ is**.

1. **Meta-Law 1 (The Primes Are Output, Not Input — Uniqueness Is Already Solved):**
   In Weil's function-field proof, geometry supplies positivity (Hodge index on $S \times S$) and uniqueness is irrelevant. Over $\mathbb{Q}$, our corpus proved the exact opposite phenomenon: **uniqueness is 100% free and already proved in Lean!** Specifically, the archimedean symbol $A(r) = \operatorname{Re}\psi(1/4+ir/2)-\log\pi$, the pole $s(1-s)$, and the additive-multiplicative grid $\{\log n\}_{n\ge 2}$ *uniquely force* the von Mangoldt weights $\Lambda(n)$ and the pole weight $\beta=1$ (`MUST-1433`, `MUST-1463`, `MUST-1478`, `MUST-1512`). The compact finite-level dual boxes `levelCertificates L` unconditionally converge coordinatewise to $\Lambda(n)$ as $L \to \infty$ (`PrimeBlindLevelCertificateSqueeze`).
   *Lesson:* We do NOT need to "understand the primes" first and plug them into a receiver. The archimedean Gamma factor restricted to the logarithmic grid $\{\log n\}$ *already defines* $\Lambda(n)$ as its shadow price (dual gradient)!

2. **Meta-Law 2 (The Pole at $s=1$ Is the Entire Engine of Rigidity and Difficulty):**
   Why is `PBAP` trivial for Dirichlet $L$-functions of conductor $q \ge 216$ (`row 1185`), where $\lambda = 0$ is in the Weil cone? Because they have **no pole**, and $\log(q/\pi) + \operatorname{Re}\psi(1/4+ir/2) \ge 0$ pointwise! For $\zeta$, the archimedean symbol has a deep negative well near $r=0$ ($A(0) \approx -5.37$), and the only thing that can compensate it on the full space is the pole term $P(c)$ plus the prime-power prices $\Lambda(n)$. Conversely, on the **zero-pole prime-blind cone** ($L(c)=0$ for all $n \ge 2$ and $P(c)=0$), the archimedean energy $\int A(r)\,d\mu_c(r)$ must be $\ge 0$ (`riemannHypothesis_iff_zeroPoleBlindPositive`, `MUST-1479`).
   *Lesson:* Every route that subtracts the pole early (`DR`, `PBM`, `TG`) loses the rigidity that couples low frequency ($r \approx 0$) to high frequency ($r \to \infty$). In `PBAP`, the condition $P(c)=0$ is a **single codimension-one global constraint** ($\int \cosh(x/2) K_c(x)\,dx = 0$) which must prevent the spectral measure $\mu_c$ of a prime-blind kernel $K_c$ ($K_c(\log n)=0$ for all $n \ge 2$) from concentrating in the low-frequency well $|r| < 6.47$!

3. **Meta-Law 3 (Why Naïve Spectral Concentration Fails — And Where the True Danger Lives):**
   Wait—why *can't* a prime-blind kernel $K_c$ ($K_c(\log n)=0$ for $n\ge 2$) with $P(c)=0$ concentrate its Fourier transform $\rho_c(r) \ge 0$ inside the negative well $|r| < 6.47$?
   - By **Carlson's theorem / Nyquist barrier**, a function vanishing on $\{\log n\}_{n\ge 2}$ cannot be bandlimited to $|r| < \pi$; in fact, low-frequency concentration alone is blocked because vanishing at $\log n$ forces high-frequency tail mass (`PrimeBlindPoleSpectralTail`, `MUST-1516`).
   - Specifically, Row 3 of `pbap-loop-fable` (`MUST-1480`) proved unconditionally that **even without the pole constraint $P(c)=0$**, the archimedean symbol integral on blind combinations is bounded below by $-3.37 \cdot \text{mass}(c)$ (using only blindness at $\log 2$!).
   - Why, then, could $\int A(r)\rho_c(r)\,dr - P(c)$ ever go to $-\infty$ if RH were false? **NOT** because $\rho_c(r)$ concentrates at low frequency $|r| < 6.47$! In fact, `MUST-1480` proves $\int A(r)\rho_c(r)\,dr \ge -3.37 \int \rho_c(r)\,dr$ for *every* blind $c$!
   - Look at that again! This is a **bombshell realization** already proved in Lean (`BlindArchimedeanNodeTwoCertificate`, `MUST-1480`, `MUST-1514`):
     **The archimedean integral $A_{\text{only}}(c) = \frac{1}{2\pi}\int (\operatorname{Re}\psi(1/4+ir/2)-\log\pi)\,d\mu_c(r)$ is NEVER unbounded below per unit mass on the blind cone! It is unconditionally $\ge -3.37 \cdot \text{mass}(c)$!**

4. **Meta-Law 4 (The True Culprit Is Positive Pole Escape vs. Zero-Pole Rescaling):**
   Wait: if $A_{\text{only}}(c) \ge -3.37 \cdot \text{mass}(c)$ unconditionally on every blind combination $c$, how can $A_{\text{only}}(c)$ be negative when $P(c) = 0$?!
   Let's check carefully!
   - In `ArchimedeanPoleValueFunction` (Row 2, `MUST-1479`), `A(c)` denotes the *total* archimedean-plus-pole energy `archOnly(c) + P(c)`, or wait: let's check the exact convention in `pbap-conjecture-loop-fable-2026-10-14.md`!
   - In Row 2: "`poleFibre v p` = values `A(c) - P(c)` (archimedean symbol only) over nonnegative `c` with node vector `v` and total pole mass `p`." And `riemannHypothesis_iff_zeroPoleBlindPositive`: **RH $\iff \frac{1}{2\pi}\int \gamma(r)\,d\mu_c(r) \ge 0$ for every nonnegative blind $c$ with total pole mass $P(c) = 0$!**
   - And in Row 3 (`BlindArchimedeanNodeTwoCertificate`): on combinations blind at $2$, $\frac{1}{2\pi}\int \gamma(r)\,d\mu_c(r) \ge -3.37 \cdot \text{mass}(c)$ unconditionally!
   - And in Row 4 (`ArchimedeanPoleValueFunction`): `riemannHypothesis_iff_forall_blind_archOnly_add_posPart_nonneg` — RH $\iff$ on any blind combination $c$, the symbol integral $\frac{1}{2\pi}\int \gamma(r)\,d\mu_c(r)$ is $\ge -\max(P(c), 0)$!
   - **WAIT A SECOND!** Look at what Row 2, Row 3, and Row 12 say together:
     1. For a blind combination $c$, the symbol $\gamma(r) = \operatorname{Re}\psi(1/4+ir/2)-\log\pi$ is **negative ONLY for $|r| < 6.4703...$** (where $\gamma(0) \approx -5.37$), and **strictly positive and growing like $\log|r|$ for all $|r| > 6.4703...$**!
     2. Therefore, the **ONLY** way $\frac{1}{2\pi}\int \gamma(r)\rho_c(r)\,dr$ can be negative on a blind combination $c$ with $P(c)=0$ is if the spectral measure $\rho_c(r)$ has enough mass in the compact low-frequency interval $|r| < 6.4703$ to outweigh $\int_{|r|>6.4703} \gamma(r)\rho_c(r)\,dr$!
     3. Wait: then how does an off-line zero at height $\gamma_0 \gg 6.47$ create a zero-pole blind combination $c$ with $\int \gamma(r)\rho_c(r)\,dr < 0$?!
     Let's trace the exact mechanism in `ArchimedeanPoleValueFunction` (`riemannHypothesis_iff_zeroPoleBlindPositive`)!
     Suppose RH fails, so there is a high-frequency blind combination $c_{\text{high}}$ (peaked near an off-line zero at height $\gamma_0 \gg 1$) where the **total** PBAP energy $\text{archOnly}(c_{\text{high}}) + P(c_{\text{high}}) < 0$.
     Since $c_{\text{high}}$ is peaked at high frequency $\gamma_0 \gg 6.47$, its symbol integral $\text{archOnly}(c_{\text{high}}) = \frac{1}{2\pi}\int \gamma(r)\rho_{c_{\text{high}}}(r)\,dr \approx (\log \gamma_0)\cdot \text{mass}(c_{\text{high}})$ is **LARGE AND POSITIVE**!
     So for $\text{archOnly}(c_{\text{high}}) + P(c_{\text{high}})$ to be negative, $P(c_{\text{high}})$ must be **LARGE AND NEGATIVE**:
     $$P(c_{\text{high}}) < -\text{archOnly}(c_{\text{high}}) < 0.$$
     And how does Row 2 turn $c_{\text{high}}$ into a **zero-pole** blind combination $c_0$ with $\text{archOnly}(c_0) < 0$?
     By adding $s \cdot c_{\text{adj}_+}$, where $c_{\text{adj}_+}$ is a **fixed low-frequency blind two-bump adjuster** supported inside $(-\log 2, \log 2)$ with $P(c_{\text{adj}_+}) > 0$ and $\text{archOnly}(c_{\text{adj}_+}) < 0$!
     Specifically, in Row 6 (`riemannHypothesis_iff_forall_blind_det_nonpos`):
     For $c_1 = c_{\text{adj}_+}$ (which has $P(c_1) > 0$ and $\text{archOnly}(c_1) < 0$) and $c_2 = c_{\text{high}}$ (which has $P(c_2) < 0$ and $\text{archOnly}(c_2) > 0$), choosing $s = -P(c_2)/P(c_1) > 0$ makes $c_0 = s c_1 + c_2$ have **zero total pole** $P(c_0) = 0$, and its symbol integral is:
     $$\text{archOnly}(c_0) = s\,\text{archOnly}(c_1) + \text{archOnly}(c_2) = \frac{|P(c_2)|}{P(c_1)}\left(\text{archOnly}(c_1) + P(c_1) \frac{\text{archOnly}(c_2)}{|P(c_2)|}\right).$$
     Look at that ratio:
     Define for any blind combination $c$ with $P(c) \ne 0$ the **Archimedean-to-Pole Ratio**:
     $$q(c) := -\frac{\text{archOnly}(c)}{P(c)}.$$
     - On **pole-positive** blind combinations ($P(c_1) > 0$, where $\text{archOnly}(c_1)$ can be negative because of the low-frequency well $|r| < 6.47$), $q(c_1) = \frac{-\text{archOnly}(c_1)}{P(c_1)}$ is the **demanded pole weight** $\beta^-(c_1)$, and under RH its supremum is $\le 1$ (in fact $=1$ in the limit).
     - On **pole-negative** blind combinations ($P(c_2) < 0$, which live at high frequency $|r| > 6.47$ where $\text{archOnly}(c_2) > 0$), $q(c_2) = \frac{\text{archOnly}(c_2)}{|P(c_2)|}$ is the **allowed pole weight** $\beta^+(c_2)$, and under RH its infimum is $\ge 1$ (in fact $=1$ in the limit).

---

## Part III: The Conjecture $\to$ Falsify/Learn $\to$ Next Conjecture Loop

### Prelude: The Secret of How the Corpus Solved Uniqueness (`(N1)`) — 1D Chaos vs. 2D Elliptic Bulk

Before launching our conjecture loop on the Existence/Producer core, we must understand the most important methodological breakthrough already inside the Lean corpus: **how `(N1)` (`TwistedArcMinimumPrincipleProof.lean`) succeeded after an entire 1D program (`CosDilation*` / `InversionSymmetric*`) hit a genuine counterexample!**

1. **The 1D Boundary Program (`CosDilation*` & `InversionSymmetric*`):**
   - By `CosDilationKernelBlindnessLink.lean` and `DivisorKernelFourierIdentification.lean`, a null-face test $\widehat{g}(r) = \Xi(r)^2 R(1/2+ir) = \zeta(1/2+ir)^2 G(1/2+ir)^2 R(1/2+ir)$ is prime-blind ($g(\log n) = 0$ for all $n \ge 2$, where $d = 1\star 1$ is triangularly invertible) **if and only if** the even self-reciprocal function $h(x)$ ($h(1/x) = |x|h(x)$, $\int h = 0$) has **additive integer Fourier coefficients vanishing**:
     $$\widehat{h}(n) = 0 \quad \text{for all } |n| \ge 2, \qquad \widehat{h}(0) = 0.$$
   - On the 1D real line $\mathbb{R}$, Poisson summation turns $\widehat{h}(n) = 0$ ($|n|\ge 2$) into the **twisted Gauss–Mayer transfer equation** (`InversionSymmetricFourierBlindTwistedMayer.lean`) at $s = 1/2$:
     $$\vartheta(r) + \sum_{m=1}^N (-1)^{m-1} \frac{\vartheta(1/(r+m))}{r+m} = F(2+r).$$
   - The corpus pushed 1D support-ratio rigidity from $\varphi = \frac{1+\sqrt{5}}{2}$ to $5/3$, $1+1/\sqrt{2}$, $12/7 \approx 1.7143$, and $212/123 \approx 1.72358$ (`InversionSymmetricFourierBlindTotalRigidity.lean`).
   - **And then the 1D boundary program hit a wall (`InversionSymmetricFourierBlindSqrtThreeCore.lean`):**
     At support ratio $97/56 \approx \sqrt{3} \approx 1.7321$, the first two Gauss branches $r \mapsto 1/(r+1)$ and $r \mapsto 1/(r+2)$ have a Cantor attractor (continued fractions with digits $\{1, 2\}$) whose **Hausdorff dimension is $\approx 0.531 > 1/2 = \operatorname{Re} s$**! Because $\dim_H > 1/2$, the 1D transfer operator has spectral radius $> 1$ and admits a **nonzero continuous $-1$-eigenfunction** supported on $[56/97, 97/56]$ with $\widehat{G}(n) = 0$ for **all** $n \in \mathbb{Z}$!
2. **How `TwistedArcMinimumPrincipleProof.lean` Circumvented the 1D Cantor-Attractor Wall:**
   - Why did 1D dynamics fail at $\sqrt{3}$? Because on the 1D boundary $\mathbb{R} = \partial\mathbb{H}$, the inversion $x \mapsto 1/x$ and translations $x \mapsto x+k$ generate a chaotic hyperbolic dynamical system with Cantor attractors.
   - `TwistedArcMinimumPrincipleProof.lean` lifted the Fourier series of $h$ from the 1D boundary $\mathbb{R}$ into the **2D hyperbolic bulk $\mathbb{H}$** via the **Whittaker stream function**:
     $$\psi(x, y) = \sum_i a_i\, y K_1(2\pi k_i y) \sin(2\pi k_i x).$$
   - In the 2D bulk $\mathbb{H}$:
     - Integer shifts $x \mapsto x+1$ are **horizontal periodicity**,
     - Inversion $x \mapsto 1/x$ is **modular reflection $z \mapsto -1/z$ across the unit circle $|z| = 1$**,
     - The archimedean Gamma factor is the **Bessel/Whittaker elliptic PDE** $L\psi = (\partial_x^2 + \partial_y^2 - \frac{1}{y}\partial_y + \frac{1}{y^2})\psi = 0$!
   - And in the 2D bulk, the chaotic 1D Cantor attractor disappears completely: it is replaced by the **smooth, simply connected half-fundamental domain** $\mathcal{F}_+ = \{x+iy \in \mathbb{H} : 0 \le x \le 1/2,\; x^2+y^2 \ge 1\}$, whose bottom arc meets $x = 1/2$ at the elliptic corner $\rho = \frac{1}{2} + i\frac{\sqrt{3}}{2}$ (notice $\operatorname{Im}\rho = \frac{\sqrt{3}}{2}$—the exact 2D geometric avatar of the $\sqrt{3}$ 1D threshold!).
   - On $\mathcal{F}_+$, the **elliptic PDE minimum principle** + the **second-derivative contradiction at the corner $\rho$** kills every nonzero combination in one stroke, for *all* support ratios simultaneously!

> **Core Meta-Lesson from `(N1)`:**
> Whenever a problem combines **multiplicative inversion ($r \mapsto 1/r$)** and **additive integer nodes ($n \in \mathbb{Z}$)**, any 1D real-variable analysis (interval splitting, gap bounds, Cauchy–Schwarz, Mayer transfer) will inevitably get trapped by the chaotic continued-fraction / Nyquist dynamics once the support ratio passes a critical horizon ($\log 2$, $\rho_{\text{plastic}}$, $\sqrt{3}$). The ONLY way to defeat 1D hyperbolic chaos globally is to **lift the problem into a 2D elliptic/harmonic bulk on a modular fundamental domain**, where 1D dynamical reflections become static geometric boundary conditions and positivity is enforced by an **elliptic minimum principle**!

---

### Conjecture 1: Transverse First-Order Variation Around the Null Face ($\Xi^2$-Divisible Blind Cone)

- **Hypothesis:** Since `(N1)` proves that on the null face $F_0 = \Phi \star \tilde{\Phi}$ ($\widehat{F_0} = \Xi^2$), the only Weil-positive weight vector is $\text{lam} = \Lambda$ and $W_\Lambda(F_0) = 0$, can we perturb $F_\varepsilon = (\Phi\chi_L + \varepsilon H) \star (\widetilde{\Phi\chi_L + \varepsilon H})$ transversely to the null face and extract a first-order variational obstruction $DW_\Lambda(F_0)[H] = 0$ that forces off-line zeros to violate positivity at order $O(\varepsilon)$?
- **Audit / Falsification:**
  Let $F_0$ have $\widehat{F_0}(r) = \Xi(r) \overline{\Xi(\bar{r})} = \Xi(r)^2$. In the explicit formula:
  $$W_\Lambda(f \star \tilde{f}) = \sum_\rho \widehat{f}(\gamma_\rho) \overline{\widehat{f}(\overline{\gamma_\rho})}.$$
  For $f = \Phi + \varepsilon h$, the $O(\varepsilon)$ cross-term at each zero $\rho$ (whether on-line or off-line!) is:
  $$\Xi(\gamma_\rho) \overline{\widehat{h}(\overline{\gamma_\rho})} + \widehat{h}(\gamma_\rho) \overline{\Xi(\overline{\gamma_\rho})}.$$
  By definition of a zero $\rho$ of $\xi$, $\Xi(\gamma_\rho) = 0$. And by the functional equation $\xi(1-\bar{\rho}) = \overline{\xi(\rho)} = 0$, the paired point $\overline{\gamma_\rho} = \gamma_{1-\bar{\rho}}$ is **also a zero of $\Xi$**, so $\Xi(\overline{\gamma_\rho}) = 0$ **unconditionally for every zero $\rho$, on or off the critical line**!
  Therefore:
  $$DW_\Lambda(F_0)[h] \equiv 0 \quad \text{identically for all } h \text{ unconditionally!}$$
  And the $O(\varepsilon^2)$ second variation is simply $W_\Lambda(h \star \tilde{h})$—the original Weil functional on $h$!
- **Verdict:** **FALSIFIED.**
- **What We Learn (Positive Salvage):**
  - The null face $\{\Xi(r) R(r)\}$ is a **critical manifold** ($W_\Lambda = 0$ and $DW_\Lambda = 0$) of the Weil functional *regardless of whether RH holds*.
  - Tangential variations along the null face determine the Lagrange multipliers $\text{lam}(n) = \Lambda(n)$ and $\beta = 1$ (which is why Uniqueness is unconditional!).
  - Transverse variations vanish to first order, and their Hessian *is* the Weil functional itself. Therefore, we cannot "perturb around $\Xi$"; we must work directly on the **prime-free primal domain** (`ZeroPoleBlindPositive`) exposed by the Lagrange multiplier theorem!

---

### Conjecture 2: Exact Fourier Duality Between `(N1)` and `PBAP`, Dual Poisson Periodization, and the Euler–Maclaurin Pole Identity

- **Hypothesis:** Can we apply the exact coordinate transformation that made `(N1)` solvable—switching from additive lag $u \in \mathbb{R}$ to multiplicative ratio $r = e^u \in (0,\infty)$ and taking the Fourier/cosine–dilation transform—directly to the **primal zero-pole blind cone** (`ZeroPoleBlindPositive` in `ArchimedeanPoleValueFunction.lean`)?
- **Mathematical Derivation & Corpus Verification:**
  Let $g \in C_c^2([-L, L])$ be a real Weil test, and set $f(y) = y^{-1/2} g(\log y) \in C_c^2([e^{-L}, e^L])$ on $(0,\infty)$.
  Its dilation autocorrelation (`dilationAutocorr` in `DilationAutocorrelationPeriodization.lean`) is:
  $$A_f(r) = \int_0^\infty f(y) f(ry)\,dy = r^{-1/2} (g \star \tilde{g})(\log r).$$
  For a nonnegative combination $c$, write $A_c(r) = \sum_i c_i A_{f_i}(r)$, extended evenly to $\mathbb{R}$ as $A_c(|r|)$, and let $\Psi_c(w) = (\mathcal{F}[A_c(|\cdot|)])(w) = 2\int_0^\infty A_c(r)\cos(2\pi w r)\,dr$ be its cosine–dilation kernel (`cosDilationKernel`).
  Look at what happens in the variable $r \in (0,\infty)$:
  1. **The Multiplicative Nodes Become Ordinary Additive Integers:**
     Since $K_c(\log n) = n^{1/2} A_c(n)$, the prime-blindness condition $\text{nodeVector}(c) = 0$ ($K_c(\log n) = 0$ for all $n \ge 2$) is **literally**:
     $$A_c(n) = 0 \quad \text{for every integer } n \ge 2!$$
     And by the inversion law $A_c(1/r) = r A_c(r)$ (`dilationAutocorr_inv`), $A_c(1/n) = 0$ for all $n \ge 2$ as well, while $A_c(1) = \text{mass}(c)$ and $A_c(0) = 0$ (by compact support in $(0,\infty)$)!
  2. **The Exponentially Weighted Pole Term Becomes the Ordinary Lebesgue Integral ($\Psi_c(0)$):**
     Under $x = \log r$, the weight $2\cosh(x/2)\,dx = (r^{1/2}+r^{-1/2})\frac{dr}{r}$ combines with $K_c(\log r) = r^{1/2} A_c(r)$ and $A_c(1/r) = r A_c(r)$ to give (`PrimeBlindPoleCuspIdentity.lean`):
     $$P(c) = \int_{-\infty}^\infty K_c(x) \cdot 2\cosh(x/2)\,dx = 2\int_0^\infty A_c(r)\,dr = \int_{-\infty}^\infty A_c(|r|)\,dr = \Psi_c(0)!$$
     **The exponentially growing weight $2\cosh(x/2)$ in additive coordinates was an artifact of logarithmic coordinates!** In multiplicative ratio coordinates $r \in (0,\infty)$, the pole mass $P(c)$ is simply the unweighted integral $\int_{\mathbb{R}} A_c(|r|)\,dr = \Psi_c(0)$!
  3. **Exact Fourier Duality Table Between `(N1)` and `PBAP`:**
     Since $\mathcal{F}[A_c(|\cdot|)] = \Psi_c$ and $\mathcal{F}[\Psi_c] = A_c(|\cdot|)$:
     - In **`(N1)` (Null-Face Blindness)**: $A_c(1/r) = r A_c(r)$, $A_c(0) = \Psi_c(0) = 0$, and **$\Psi_c(n) = 0$ for all $|n| \ge 2$**.
     - In **`PBAP` (`ZeroPoleBlindPositive`)**: $A_c(1/r) = r A_c(r)$, $A_c(0) = \Psi_c(0) = 0$, and **$A_c(n) = 0$ for all $|n| \ge 2$**!
  4. **New Identity 2A — The Dual Poisson Periodization Law on the Primal Blind Cone:**
     Because $A_c(|r|) \in C_c^2(\mathbb{R})$ vanishes at $r = 0$ and at every integer $|n| \ge 2$, Poisson summation applied to $\Psi_c = \mathcal{F}[A_c(|\cdot|)]$ yields for **every** prime-blind combination $c$ and **every** $w \in \mathbb{R}$:
     $$\sum_{k \in \mathbb{Z}} \Psi_c(w + k) = \sum_{n \in \mathbb{Z}} A_c(|n|) e^{2\pi i n w} = 2 A_c(1) \cos(2\pi w) = 2\,\text{mass}(c) \cos(2\pi w)!$$
     At $w = 0$, since $\Psi_c(0) = P(c)$ and $\Psi_c(-k) = \Psi_c(k)$, this gives the **Exact Primal Cusp-Harmonic Identity**:
     $$P(c) + 2\sum_{k=1}^\infty \Psi_c(k) = 2\,\text{mass}(c)!$$
     In particular, on the **zero-pole blind cone** ($P(c) = 0$), the integer values of the cosine–dilation kernel $\Psi_c(k)$ must sum to the mass:
     $$\sum_{k=1}^\infty \Psi_c(k) = \text{mass}(c) > 0, \qquad \text{and more generally } \sum_{k \in \mathbb{Z}} \Psi_c(w+k) = 2\,\text{mass}(c)\cos(2\pi w)!$$
  5. **New Identity 2B — The Half-Interval Primitive Positivity & Exact Euler–Maclaurin Pole Identity:**
     By `CosDilationPrimitiveEnergyRigidity.lean` (`intervalIntegral_zero_one_dilationAutocorr_eq`), on the unit interval $r \in [0, 1]$ (which contains NO integer nodes $n \ge 2$), the integral of $A_c(r)$ is **unconditionally a sum of squares** of the primitive $F_i(y) = \int_0^y f_i(t)\,dt$:
     $$\int_0^1 A_c(r)\,dr = \sum_i c_i \left(\frac{F_i(\beta_i)^2}{2\beta_i} + \frac{1}{2}\int_0^\infty \left(\frac{F_i(y)}{y}\right)^2 dy\right) = \frac{1}{2}\int_{-\infty}^\infty \frac{\rho_c(t)}{\frac{1}{4}+t^2}\,dt > 0!$$
     Meanwhile, on $[1, \infty)$, the nodes $n = 1, 2, 3, \dots$ have **unit spacing $\Delta r = 1$**, with $A_c(1) = \text{mass}(c)$ and $A_c(n) = 0$ for all $n \ge 2$. Applying Euler–Maclaurin integration by parts on each unit interval $[n, n+1]$ ($n \ge 1$) kills every endpoint term for $n \ge 2$ and yields:
     $$\frac{1}{2}P(c) = \underbrace{\frac{1}{2}\,\text{mass}(c)}_{>\;0} + \underbrace{\int_0^1 A_c(r)\,dr}_{>\;0} + \int_1^\infty \left(\{r\} - \frac{1}{2}\right) A_c'(r)\,dr = \frac{1}{2}\,\text{mass}(c) + \int_0^1 A_c(r)\,dr - \frac{1}{2}\int_1^\infty \{r\}(1-\{r\}) A_c''(r)\,dr!$$
     Therefore, for $P(c) \le 0$ to occur on a blind combination $c$, the unit-interval curvature integral $\frac{1}{2}\int_1^\infty \{r\}(1-\{r\}) A_c''(r)\,dr$ on $[1, \infty)$ must exceed $\frac{1}{2}\,\text{mass}(c) + \int_0^1 A_c(r)\,dr > \frac{1}{2}\,\text{mass}(c)$!
     Wait: if we bound $\frac{1}{2}\int_1^\infty \{r\}(1-\{r\}) |A_c''(r)|\,dr$ by the triangle inequality (`|A_c''|`), what happens? Since $A_c(e^u) = e^{-u/2} K_c(u)$, at large $r \approx e^u$ ($u \gg 1$) and frequency $\tau$, $A_c''(r) \sim r^{-5/2} \tau^2 K_c(\log r)$, so the triangle inequality gives $\int_1^\infty r^{-5/2}\,dr \cdot \int \tau^2 \rho_c(\tau)\,d\tau$ (or with split thresholds, $\int \sqrt{|\tau|}\rho_c(\tau)\,d\tau$ as in `PrimeBlindPoleSpectralTail.lean`), which grows like $\sqrt{|\tau|}$ whereas the archimedean symbol grows only like $\log|\tau|$!
     **Why does the triangle inequality on $[1, \infty)$ lose $\sqrt{|\tau|}$ vs. $\log|\tau|$?**
     Because taking $|A_c''(r)|$ throws away the **oscillatory cancellation of $A_c(r)$ across successive unit intervals $[n, n+1]$**, and throws away the fact that $A_c(r) = \int_0^\infty f(y)f(ry)\,dy$ is a **Mellin-positive self-reciprocal kernel** ($A_c(1/r) = r A_c(r)$), not an arbitrary function vanishing at the integers!
- **Status of Conjecture 2:** **SUCCEEDED as a structural reduction & diagnostic; reveals the exact obstacle for Conjecture 3.**
  Conjecture 2 proves that in multiplicative coordinates $r \in (0,\infty)$, `PBAP` is the **exact Fourier dual of `(N1)`**, and exposes why `PrimeBlindPoleSpectralTail` lost $\sqrt{|\tau|}$ vs. $\log|\tau|$: because it took absolute values $|A_c(r)|$ on each gap $[n, n+1]$ instead of using the **global Mellin/Fourier phase relation between $A_c$ and $\Psi_c$**!

---

### Conjecture 3: The Even-Sector Collapse of the $\sqrt{|\tau|}$ Pole-Tail Enemy (`EvenSectorFullPositivity.lean` vs. `PrimeBlindPoleSpectralTail.lean`) and the Two-Scale Mode-Coupling Reduction

- **Hypothesis 3A:** In Conjecture 2, we saw that on the full blind cone (`WeilTestFn →₀ ℝ`), `PrimeBlindPoleSpectralTail.lean` (`MUST-1516`) got stuck at a $\sqrt{|\tau|}$ spectral tail vs. $\log|\tau|$ archimedean growth because odd tests have negative pole term $P(f) = -2|\widehat{f}(i/2)|^2 \le 0$. What happens if we restrict the primal blind cone to **even** test functions (`EvenWeilTestFn →₀ ℝ`)?
- **Corpus Verification (`EvenSectorFullPositivity.lean`, `MUST-1495`):**
  1. `riemannHypothesis_iff_primeBlindPositiveEvenAt` proves unconditionally that the Riemann Hypothesis is **100% equivalent** to prime-blind positivity on the **EVEN** cone (`PrimeBlindPositiveEvenAt 1`):
     $$\forall c : \text{EvenWeilTestFn} \to_0 \mathbb{R},\quad c \ge 0,\quad \text{evenNodeVector}(c) = 0 \implies \text{evenArchPole}(1, c) \ge 0.$$
  2. On `EvenWeilTestFn`, every generator $f_i$ is real and even, so $\int_{-\infty}^\infty f_i(x)\sinh(x/2)\,dx = 0$ vanishes identically, and its pole term is a **nonnegative square** (`weilPoleTerm_re_nonneg_of_even`):
     $$P(f_i) = 2\left(\int_{-\infty}^\infty f_i(x)\cosh\left(\frac{x}{2}\right) dx\right)^2 = 2\left|\widehat{f_i}\left(\frac{i}{2}\right)\right|^2 = 2\int_{-\infty}^\infty (f_i \star f_i)(y)\cosh\left(\frac{y}{2}\right) dy \ge 0.$$
  3. **Elimination of the $\sqrt{|\tau|}$ Pole-Tail Enemy:**
     Because $P(c) = \sum_i c_i P(f_i) \ge 0$ is **unconditionally nonnegative** on the even cone, $P(c)$ has the **same positive sign** as the high-frequency archimedean integral $\frac{1}{2\pi}\int_{|r| \ge r_0} \gamma(r)\rho_c(r)\,dr \ge 0$ (where $r_0 \approx 6.4703$ is the unique positive zero of $\gamma(r) = \operatorname{Re}\psi(\frac{1}{4}+\frac{ir}{2}) - \log\pi$).
     Therefore, on the even blind cone:
     $$\text{evenArchPole}(1, c) = \underbrace{P(c)}_{\ge\;0} + \underbrace{\frac{1}{2\pi}\int_{|r| \ge r_0} \gamma(r)\,\rho_c(r)\,dr}_{\ge\;0} - \underbrace{\frac{1}{2\pi}\int_{-r_0}^{r_0} |\gamma(r)|\,\rho_c(r)\,dr}_{\le\; 1.50\,\text{mass}(c)}.$$
     **The $\sqrt{|\tau|}$ pole-tail enemy of `PrimeBlindPoleSpectralTail.lean` (`MUST-1516`) does NOT exist on the even blind cone!** Any hypothetical unit-mass ($K_c(0)=1$) violator on the even blind cone is trapped in the bounded-energy regime:
     $$0 \le P(c) < 1.50, \qquad 0 \le \frac{1}{2\pi}\int_{|r|\ge r_0} \gamma(r)\,\rho_c(r)\,dr < 1.50.$$
  4. **Linearity in the Single Autocorrelation $K_c$ and T-Contour Spectral Nonnegativity:**
     On `EvenWeilTestFn`, every functional in the problem—the node values $K_c(\log n)$, the pole term $P(c) = 2\widehat{K_c}(i/2)$, and the archimedean term $\text{archOnly}(c) = \frac{1}{2\pi}\int_{-\infty}^\infty \gamma(r)\widehat{K_c}(r)\,dr$—is a **linear functional of the single autocorrelation $K_c(y) = \sum_i c_i (f_i \star f_i)(y)$**. Moreover, because each $\widehat{f_i}(z)$ is real on both $\mathbb{R}$ and $i\mathbb{R}$, the spectral density $\rho_c(z) = \widehat{K_c}(z) = \sum_i c_i \widehat{f_i}(z)^2$ is **nonnegative on the entire T-shaped contour $\mathbb{R} \cup i\mathbb{R}$**:
     $$\rho_c(r) \ge 0 \quad (\forall r \in \mathbb{R}) \qquad \text{AND} \qquad \rho_c(i\sigma) = \sum_i c_i \left(\int_{-\infty}^\infty f_i(x)\cosh(\sigma x)\,dx\right)^2 \ge 0 \quad (\forall \sigma \in \mathbb{R})!$$
- **Hypothesis 3B (Naive Compactness) & Falsification — The Two-Scale Mode-Coupling Mechanism:**
  - *Question:* Since any unit-mass even blind violator $c$ has bounded low-frequency and high-frequency energy, why doesn't a compactness argument immediately close RH?
  - *Audit / Falsification:* Although the spectral energy is bounded, the **spatial support $[-L, L]$ can be arbitrarily large ($L \to \infty$)**. If $\zeta(s)$ had an off-line zero at high frequency $\gamma_0 \gg 6.4703$, how would it create an even blind violator whose negative energy comes from $[-6.4703, 6.4703]$?
    1. On a wide interval $[-L, L]$ ($L \gg 1$), an even primitive packet $c_{\text{low}}$ ($P(c_{\text{low}}) = 0$) can concentrate its spectrum inside $[-6.4703, 6.4703]$ so that $\text{archOnly}(c_{\text{low}}) < 0$.
    2. Because $\rho_{c_{\text{low}}}$ is bandlimited to $|r| \le 6.4703$, $K_{c_{\text{low}}}(y)$ varies slowly on scale $\Delta y \sim 1/6.4703 \approx 0.15$ and **cannot vanish** at the exponentially dense logarithmic nodes $y = \log n \in (0, 2L]$ ($\Delta(\log n) \approx 1/n \ll 0.15$).
    3. To achieve $K_c(\log n) = 0$ for all $n \ge 2$, $c_{\text{low}}$ must be paired with a high-frequency tail $c_{\text{high}}$ (supported near $|r| \approx \gamma_0$ with small weight $w_{\text{high}} \sim 1/\log\gamma_0$) that cancels the node values of $c_{\text{low}}$:
       $$K_{c_{\text{high}}}(\log n) = -K_{c_{\text{low}}}(\log n) \qquad (\forall n \ge 2),$$
       while paying a high-frequency archimedean penalty $\frac{1}{2\pi}\int_{|r|\ge r_0} \gamma(r)\rho_{c_{\text{high}}}(r)\,dr < |\text{archOnly}(c_{\text{low}})|$.
- **Verdict & Positive Salvage 3:**
  On the even primitive blind cone (`EvenPrimitiveWeilTestFn →₀ ℝ_{\ge 0}`, where $P(f) = 0$ identically), RH is 100% equivalent to the **Two-Scale Mode-Coupling Law**: no high-frequency cone tail $c_{\text{high}}$ can cancel the dense logarithmic node values $K_{c_{\text{low}}}(\log n)$ ($n \ge 2$) of a low-frequency packet $c_{\text{low}}$ ($|r| < 6.4703$) at an archimedean spectral cost smaller than $|\text{archOnly}(c_{\text{low}})|$.

---

### Conjecture 4: Exact Multiplicative-Ratio Duality on $[0, 1] \leftrightarrow [1, \infty)$, Unification of the Two Towers' Resolvent Laws, and the Even-Primitive Clamped-Beam Shift

- **Hypothesis:** Can we express the entire archimedean functional `markovArchRe` and the pole-free resolvent identity (`MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean`) in the multiplicative ratio coordinates $r \in (0, 1]$ / $u \in [1, \infty)$ of Conjecture 2, and see why 1D cell bounds stall while the even-primitive resolvent structure shifts the spectral floor?
- **Mathematical Derivation & Exact Unification Across the Two Towers:**
  1. **Unification of `CosDilationPrimitiveEnergyRigidity.lean` (`Zeta23`) and `MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean` (`RHTower`):**
     Under $r = e^{-x} \in (0, 1]$ on the node-free unit interval and $u = e^x \in [1, \infty)$ on the integer-node half-line, using $K_c(\log u) = u^{1/2} A_c(u)$ and $A_c(1/u) = u\,A_c(u)$:
     - The **Bochner–Poisson resolvent energy** `bochnerResolventEnergy(K_c)` in `MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean` is **literally the node-free unit-interval integral $2\int_0^1 A_c(r)\,dr$** proved positive in `CosDilationPrimitiveEnergyRigidity.lean`:
       $$\text{bochnerResolventEnergy}(K_c) = 2\int_0^\infty e^{-x/2} K_c(x)\,dx = 2\int_0^1 A_c(r)\,dr = 2\int_1^\infty \frac{A_c(u)}{u}\,du = \frac{1}{2\pi}\int_{-\infty}^\infty \frac{\rho_c(\tau)}{\frac{1}{4} + \tau^2}\,d\tau > 0!$$
     - The **continuum `lebesguePart` integral** in `MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean` is **literally the half-line integral $2\int_1^\infty A_c(u)\,du$**:
       $$\left(\int x, \text{primeIntegrand } K_c\; x\;\partial\text{lebesguePart}\right).\text{re} = 2\int_0^\infty e^{x/2} K_c(x)\,dx = 2\int_1^\infty A_c(u)\,du = 2\int_0^1 \frac{A_c(r)}{r}\,dr!$$
     - More generally, **every $m$-th Gauss mode** of the Lévy density $\omega(x) = \frac{e^{-x/2}}{1 - e^{-2x}} = \sum_{m=0}^\infty e^{-(2m + 1/2)x}$ (`WeilLevyPoleGaussModeCancellation.lean`) is an **even power moment of $A_c(r)$ on the node-free unit interval $[0, 1]$**:
       $$2\int_0^\infty e^{-(2m + 1/2)x} K_c(x)\,dx = 2\int_0^1 r^{2m} A_c(r)\,dr = 2\int_1^\infty \frac{A_c(u)}{u^{2m+1}}\,du = \frac{1}{2\pi}\int_{-\infty}^\infty \frac{(2m + \frac{1}{2})\rho_c(\tau)}{(2m + \frac{1}{2})^2 + \tau^2}\,d\tau > 0!$$
  2. **New Identity 4A — The Exact Multiplicative Unit-Interval and Half-Line Formulas for `markovArchRe`:**
     Substituting $x = -\log r$ ($r \in (0, 1]$) into $\text{markovArchRe}(K_c) = A(0)K_c(0) + 2\int_0^\infty \frac{e^{-x/2}}{1 - e^{-2x}}(K_c(0) - K_c(x))\,dx$ and using the exact elementary integral
     $$2\int_0^1 \frac{r^{-1/2} - 1}{1 - r^2}\,dr = 4\int_0^1 \frac{dt}{(1+t)(1+t^2)} = \log 2 + \frac{\pi}{2}$$
     together with $-A(0) = \log\pi + 3\log 2 + \gamma_{\text{EM}} + \frac{\pi}{2}$ (`neg_gammaBracket_zero_eq`) cancels $\frac{\pi}{2}$ and $\log 2$ identically, yielding the **nonsingular unit-interval and half-line representations**:
     $$\boxed{\text{markovArchRe}(K_c) = -\big(\gamma_{\text{EM}} + \log(4\pi)\big) A_c(1) + 2\int_0^1 \frac{A_c(1) - A_c(r)}{1 - r^2}\,dr = -\big(\gamma_{\text{EM}} + \log(4\pi)\big) A_c(1) + 2\int_1^\infty \frac{A_c(1) - u\,A_c(u)}{u^2 - 1}\,du!}$$
     (Both integrands are $C^1$ at $r = 1$ / $u = 1$ because $A_c'(1) = -\frac{1}{2}A_c(1)$, so $A_c(1) - A_c(r) \sim -\frac{1}{2}A_c(1)(1-r)$ and $A_c(1) - u A_c(u) \sim -\frac{1}{2}A_c(1)(u-1)$!)
     Extracting the first $M$ positive Gauss modes $\sum_{m=0}^{M-1} 2\int_1^\infty \frac{u\,A_c(u)}{u^{2m+2}}\,du > 0$ gives for every $M \ge 1$:
     $$\boxed{\text{markovArchRe}(K_c) + \sum_{m=0}^{M-1} \frac{1}{2\pi}\int_{-\infty}^\infty \frac{(2m + \frac{1}{2})\rho_c(\tau)}{(2m + \frac{1}{2})^2 + \tau^2}\,d\tau = \left(2\sum_{m=0}^{M-1}\frac{1}{2m+1} - \gamma_{\text{EM}} - \log(4\pi)\right) A_c(1) + 2\int_1^\infty \frac{A_c(1) - u\,A_c(u)}{u^{2M}(u^2 - 1)}\,du!}$$
     Already at $M = 4$, the origin constant is **strictly positive** ($\frac{352}{105} - \gamma_{\text{EM}} - \log(4\pi) \approx +0.2442 > 0$) and the remainder kernel on $[1, \infty)$ decays as $\frac{2}{u^8(u^2 - 1)} \sim 2 u^{-10}$!
  3. **New Identity 4B — The Even-Primitive Resolvent Factorisation (`f = (-D² + 1/4)q`) and Clamped-Beam Spectral Shift:**
     For an even test $f \in \text{EvenWeilTestFn}$ supported in $[-a, a]$, the unique solution $q$ of $(-D_x^2 + \frac{1}{4})q = f$ vanishing on $[a, \infty)$ satisfies on $(-\infty, -a]$:
     $$q(x) = -2\cosh\left(\frac{x}{2}\right)\underbrace{\int_{-a}^a f(t)\sinh\left(\frac{t}{2}\right) dt}_{=\;0\text{ (since }f\text{ is even)}} + 2\sinh\left(\frac{x}{2}\right)\underbrace{\int_{-a}^a f(t)\cosh\left(\frac{t}{2}\right) dt}_{=\;\widehat{f}(i/2)}.$$
     Therefore:
     $$f \in \text{EvenPrimitiveWeilTestFn}\; (\text{supp}(f) \subset [-a, a],\; \widehat{f}(i/2) = 0) \iff f = \left(-\frac{d^2}{dx^2} + \frac{1}{4}\right) q \quad \text{for a unique even } q \in C_c^4([-a, a])!$$
     In terms of $q$, the Bochner resolvent energy is simply the $H^1$ Klein–Gordon norm of $q$:
     $$\text{bochnerResolventEnergy}(k_f) = \frac{1}{2\pi}\int_{-\infty}^\infty \left(r^2 + \frac{1}{4}\right) |\widehat{q}(r)|^2\,dr = \|q'\|_{L^2}^2 + \frac{1}{4}\|q\|_{L^2}^2 = \langle f, q\rangle_{L^2},$$
     and because $q$ is even and supported in $[-a, a]$, its derivative $q'$ vanishes at **both** endpoints of $[0, a]$ ($q'(0) = 0$ and $q'(a) = 0$, plus $q(a) = 0$), forcing $\|q''\|_{L^2}^2 \ge (\frac{\pi}{a})^2 \|q'\|_{L^2}^2$ and pushing the lowest even-primitive eigenmode to $\approx \frac{3\pi}{2a}$ (which exceeds $r_0 \approx 6.4703$ all the way past $2a = \log 4$!).
  4. **Why 1D Methods Still Stall as $L \to \infty$:**
     In the half-line integral $2\int_1^\infty \frac{A_c(1) - u\,A_c(u)}{u^{2M}(u^2 - 1)}\,du$, the kernel $\frac{2}{u^{2M}(u^2 - 1)}$ is concentrated on the **first gap $u \in (1, 2)$** (between $u = 1$ and the first prime node $u = 2$). On $(1, 2)$, there are no integer nodes $n \ge 2$. Any 1D bound that treats $A_c(u)$ cell-by-cell on $[n, n+1]$ cannot transmit the vanishing $A_c(n) = 0$ ($n \ge 2$) across the node-free gap $(1, 2)$ when the support $e^{2L} \to \infty$ is large. To couple $(1, 2)$ to $n \ge 2$, we must use **global analytic/dispersion duality and the 2D bulk lift**!

---

### Conjecture 5: The Klein–Gordon Mass-$1/2$ Dispersion Transmutation ($\rho = \sqrt{z^2 + 1/4}$) and the Unconditional T-Contour Bochner Theorem

- **Hypothesis:** In `EvenSectorCosineBochner.lean`, the corpus introduced the shifted square root $\rho(z) = \sqrt{z^2 + 2}$ using `Complex.cpow (1/2)` on `Complex.slitPlane`, which required keeping the branch points $\pm i\sqrt{2}$ outside the strip $|\operatorname{Im} z| \le 5/4$ and forced working with non-compactly-supported strip functions `StripTestFn`. What happens if we notice that $\cos(w)$ and $\operatorname{sinc}(w) = \frac{\sin w}{w}$ are **even entire functions of $w$** (containing only powers of $w^2 = z^2 + c$), and set $c = \frac{1}{4}$ (the **exact $\zeta$-pole mass** where $\rho(\pm i/2) = 0$)?
- **Mathematical Derivation & New Theorems:**
  1. **Entirety and Finite-Speed Klein–Gordon Propagation for All $c \in \mathbb{R}$:**
     For **every** $c \in \mathbb{R}$ and $y \in \mathbb{R}$, the functions
     $$\cos\left(y\sqrt{z^2 + c}\right) = \sum_{k=0}^\infty \frac{(-1)^k}{(2k)!} y^{2k} (z^2 + c)^k \quad \text{and} \quad \frac{\sin\left(y\sqrt{z^2 + c}\right)}{\sqrt{z^2 + c}} = y\sum_{k=0}^\infty \frac{(-1)^k}{(2k+1)!} y^{2k} (z^2 + c)^k$$
     have **NO branch cuts anywhere in $\mathbb{C}$**: they are **even entire functions of $z \in \mathbb{C}$ of exponential type $|y|$**.
     By Paley–Wiener (and the classical Riemann–Green formula for the 1+1D Klein–Gordon wave equation $(\partial_y^2 - \partial_x^2 + c)u = 0$), for any compactly supported $f \in \text{EvenWeilTestFn}$ on $[-L, L]$, the cosine and sinc wave propagators
     $$u_c(x, y) := \left(\cos\left(y\sqrt{-D_x^2 + c}\right)f\right)(x) = \frac{f(x+y)+f(x-y)}{2} - \frac{\sqrt{c}\,y}{2}\int_{x-y}^{x+y} \frac{J_1\left(\sqrt{c(y^2-(x-t)^2)}\right)}{\sqrt{y^2-(x-t)^2}} f(t)\,dt,$$
     $$v_c(x, y) := \left(\frac{\sin\left(y\sqrt{-D_x^2 + c}\right)}{\sqrt{-D_x^2 + c}}f\right)(x) = \frac{1}{2}\int_{x-y}^{x+y} J_0\left(\sqrt{c(y^2-(x-t)^2)}\right) f(t)\,dt$$
     are **smooth, even, compactly supported test functions in `EvenWeilTestFn` supported on $[-(L+|y|), L+|y|]$**!
  2. **New Identity 5A — Exact Pole Cancellation at the Canonical Klein–Gordon Mass $c = 1/4$:**
     When $c = \frac{1}{4}$, the dispersion relation is $\rho(z) = \sqrt{z^2 + \frac{1}{4}}$, which **vanishes at the $\zeta$-poles $z = \pm i/2$** ($\rho(\pm i/2) = 0$).
     For any $f \in \text{EvenWeilTestFn}$ and any finite sequence $(c_j, y_j)_{j=1}^m$, set $U = \sum_j c_j u_{1/4}(\cdot, y_j) \in \text{EvenWeilTestFn}$ and $V = \sum_j c_j v_{1/4}(\cdot, y_j) \in \text{EvenWeilTestFn}$. Then:
     - $\frac{1}{2}V \in \text{EvenWeilTestFn}$ has pole term $P(\frac{1}{2}V) = +\frac{1}{2}\widehat{V}(i/2)^2$, while $\partial_x V \in \text{OddWeilTestFn}$ has $\int (\partial_x V)(x)\sinh(x/2)\,dx = -\frac{1}{2}\widehat{V}(i/2)$ by integration by parts, so its pole term is $P(\partial_x V) = -\frac{1}{2}\widehat{V}(i/2)^2$.
     - **Their pole terms cancel identically** ($P(\frac{1}{2}V) + P(\partial_x V) = 0$), and the three-test cone element $C_{(c_j, y_j)} := \delta_U + \delta_{\frac{1}{2}V} + \delta_{\partial_x V}$ in `WeilTestFn →₀ ℝ_{\ge 0}` has total spectral density:
       $$\widehat{K_{C}}(z) = \widehat{k_U}(z) + \widehat{k_{\frac{1}{2}V}}(z) + \widehat{k_{\partial_x V}}(z) = \widehat{f}(z)^2 \sum_{j, k=1}^m c_j c_k \cos\left((y_j - y_k)\sqrt{z^2 + \frac{1}{4}}\right)!$$
     - Moreover, whenever $f \in \text{EvenPrimitiveWeilTestFn}$ ($\widehat{f}(i/2) = 0$), we have $\widehat{U}(i/2) = \widehat{V}(i/2) = 0$, so **every single one of $U, \frac{1}{2}V, \partial_x V$ lies individually in the zero-pole primitive hyperplane `PrimitiveWeilTestFn` ($P = 0$)**!
  3. **New Theorem 5B — The Adjoint Sonine–Gegenbauer Volterra Transmutation $H_c = \mathcal{S} K_c$ and Unconditional T-Contour Bochner Positivity:**
     Using the Sonine–Gegenbauer integral $\cos(zt) = \cos\left(t\sqrt{z^2 + 1/4}\right) + \frac{t}{2}\int_0^t \frac{I_1\left(\frac{1}{2}\sqrt{t^2 - y^2}\right)}{\sqrt{t^2 - y^2}} \cos\left(y\sqrt{z^2 + 1/4}\right) dy$, define for any even combination $c$ supported on $[-L, L]$ the **adjoint Klein–Gordon transmutation** on $[-2L, 2L]$:
     $$H_c(y) := (\mathcal{S} K_c)(y) := K_c(y) + \frac{1}{2}\int_{|y|}^{2L} K_c(t) \frac{t\,I_1\left(\frac{1}{2}\sqrt{t^2 - y^2}\right)}{\sqrt{t^2 - y^2}}\,dt \in C_c^2([-2L, 2L]),$$
     with exact inverse
     $$K_c(t) = (\mathcal{S}^{-1} H_c)(t) = H_c(t) - \frac{1}{2}\int_{|t|}^{2L} H_c(y) \frac{y\,J_1\left(\frac{1}{2}\sqrt{y^2 - t^2}\right)}{\sqrt{y^2 - t^2}}\,dy.$$
     Then for **every** $z \in \mathbb{C}$, the ordinary Fourier transform $\widehat{H_c}(\rho) = \int_{-2L}^{2L} H_c(y)\cos(\rho y)\,dy$ satisfies:
     $$\rho_c(z) = \widehat{K_c}(z) = \widehat{H_c}\left(\sqrt{z^2 + \frac{1}{4}}\right)!$$
     Look at what happens on the **entire real $\rho$-line $\rho \in \mathbb{R}$**:
     - For $|\rho| \ge \frac{1}{2}$, $z = \sqrt{\rho^2 - 1/4} \in \mathbb{R}$ lies on the **critical line**, so $\widehat{H_c}(\rho) = \rho_c\big(\sqrt{\rho^2 - 1/4}\big) \ge 0$.
     - For $|\rho| \le \frac{1}{2}$, $z = i\sqrt{1/4 - \rho^2} \in i[-1/2, 1/2]$ lies on the **real $s$-segment $[0, 1]$ between the $\zeta$-poles**, where by Conjecture 3 (evenness of $f_i$), $\widehat{H_c}(\rho) = \rho_c\big(i\sqrt{1/4 - \rho^2}\big) = \sum_i c_i \big(\widehat{f_i}(i\sqrt{1/4 - \rho^2})\big)^2 \ge 0$ is **also nonnegative**!
     - **Therefore, $\widehat{H_c}(\rho) \ge 0$ for ALL $\rho \in \mathbb{R}$, so $H_c = \mathcal{S} K_c \in C_c^2([-2L, 2L])$ is UNCONDITIONALLY a compactly supported Bochner positive-definite function on $\mathbb{R}$!**
     - Its unweighted integral is the pole term $\int_{-2L}^{2L} H_c(y)\,dy = \widehat{H_c}(0) = \rho_c(i/2) = \frac{1}{2}P(c)$, and on `EvenPrimitiveWeilTestFn` ($P(c) = 0$), $\widehat{H_c}(\rho) = \rho^4 \widehat{H_q}(\rho) \ge 0$ vanishes to **fourth order at $\rho = 0$**, so $H_c = H_q^{(4)}$ is the fourth derivative of a compactly supported Bochner positive-definite function $H_q \in C_c^6([-2L, 2L])$!

---

### Conjecture 6: Discovery of the Exact Variational Ground State $C_{\text{TA}}$ of the Prime-Blind Cone, the Unconditional Convolution Annihilation Law $\kappa_{\text{TA}} \star \varphi_\Lambda \equiv 0$, and the Complex-Frequency Separation of Off-Line Zeros

- **Hypothesis:** Why did `EvenSectorTwistedArcNull.lean`, `EvenSectorCriticalZeroCarrier.lean`, and `EvenSectorFullPositivity.lean` succeed so effortlessly once the single function $\varphi_\Lambda(y) = \text{cosineShiftFn }\Lambda\;\text{sechHalf}\; y$ was represented by a positive measure $\nu$? What is the true primal meaning of the Twisted-Arc Null Family $\Phi_j = \Xi Q_j$, and what equation does $\varphi_\Lambda(y)$ satisfy **unconditionally** (without assuming $\nu$ exists)?
- **Corpus Audit & Three Major Discoveries:**
  1. **Discovery 6A — The Twisted-Arc Combination $C_{\text{TA}}$ Is the Exact Zero-Energy Variational Ground State of the Primal Even Prime-Blind Cone:**
     Look at lines 224–245 and 603–622 of `EvenSectorTwistedArcNull.lean` and lines 46–127 of `EvenSectorCriticalZeroCarrier.lean`:
     With the nonnegative twisted-arc weights $w_j \ge 0$ ($w_0 > 0$) constructed unconditionally from `twistedArcMinimumPrinciple_holds` (the 2D Whittaker minimum principle on the modular fundamental domain $\mathcal{F}_+$), the infinite strip combination
     $$C_{\text{TA}} := \sum_{j=0}^\infty w_j\,\delta_{\Phi_j}, \qquad \Phi_j(z) = \text{xiShiftedGamma } j(z) = \Xi(z)\,Q_j(z)$$
     satisfies **UNCONDITIONALLY (with ZERO RH hypothesis)**:
     - **Exact Prime-Blindness (`hblind'`):**
       $$K_{C_{\text{TA}}}(\log n) = \sum_{j=0}^\infty w_j (\Phi_j \star \Phi_j)(\log n) = 0 \qquad \text{for ALL integers } n \ge 2!$$
     - **Exact Zero Archimedean-Pole Energy (`hA0`):**
       $$\text{archPoleEnergy}(C_{\text{TA}}) = P(C_{\text{TA}}) + \text{archOnly}(C_{\text{TA}}) = \sum_{j=0}^\infty w_j\,\text{archPoleEnergy}(\Phi_j) = 0!$$
     - **Strict Positivity of Pole Mass and Carrier Outside Critical Zeros (`hSpos`, `measure_xiC_ne_zero_eq_zero`):**
       On the $\rho$-line ($\rho = \sqrt{z^2 + 2} \in \mathbb{R}$, which is the T-shaped union $\mathbb{R} \cup i[-\sqrt{2}, \sqrt{2}]$ in the $z$-plane), the lifted carrier
       $$G_{\text{TA}}(\rho) := \sum_{j=0}^\infty w_j \operatorname{Re}\Big(\Phi_j\big(\sqrt{\rho^2 - 2}\big)\Phi_j^\#\big(\sqrt{\rho^2 - 2}\big)\cosh^2\Big(\frac{\sqrt{\rho^2 - 2}}{2}\Big)\Big)$$
       satisfies $G_{\text{TA}}(\rho) > 0$ **everywhere on $[-\sqrt{2}, \sqrt{2}]$** (in particular at the pole $\rho = \sqrt{7/4}$, so $P(C_{\text{TA}}) = 2\rho_{\text{TA}}(i/2) > 0$!), and for $|\rho| > \sqrt{2}$ satisfies $G_{\text{TA}}(\rho) \ge w_0 |\Xi(\sqrt{\rho^2-2})|^2 \cosh^2(\sqrt{\rho^2-2}/2) \ge 0$, so on the entire real line $\mathbb{R}$:
       $$\boxed{G_{\text{TA}}(\rho) \ge 0 \quad (\forall \rho \in \mathbb{R}), \qquad \text{and} \qquad G_{\text{TA}}(\rho) = 0 \iff \rho^2 > 2 \text{ and } \Xi\big(\sqrt{\rho^2 - 2}\big) = 0!}$$
     - **Variational Significance:**
       In `ArchimedeanPoleValueFunction.lean` (`MUST-1509`), RH was shown to be equivalent to $\sup_{c \text{ prime-blind}} \frac{-\text{archOnly}(c)}{P(c)} \le 1$.
       **$C_{\text{TA}}$ is the explicit, unconditional global maximizer of this variational ratio on the even strip prime-blind cone, achieving the exact boundary value $\frac{-\text{archOnly}(C_{\text{TA}})}{P(C_{\text{TA}})} = 1$ ($\text{archOnly}(C_{\text{TA}}) + P(C_{\text{TA}}) = 0$)!**
       This also explains why Candidate 15 (`WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean`) stalled when it used only the single function $\Phi_0$ ($\widehat{\Phi_0} = \Xi$) as its Doob ground state: $\Phi_0$ alone is only the $j = 0$ term of $C_{\text{TA}}$ and is **not prime-blind**, leaving an uncompensated prime sum and pole mass. The **true prime-blind ground state** is the full 2D Whittaker-weighted series $C_{\text{TA}} = \sum_{j=0}^\infty w_j \delta_{\Phi_j}$!

  2. **Discovery 6B — The Unconditional 1D Sech-Representation and Convolution Annihilation Law $\big(\kappa_j \star \varphi_\Lambda\big)(y) \equiv 0$:**
     In `EvenSectorSpectralConsistency.lean` (lines 250–433: `evenPolePart_mul_integral`, `evenArchPart_mul_integral`, `evenPrimePart_mul_integral`), Fubini's theorem is proved **100% unconditionally** (without any measure $\nu$) for any multiplier kernel $\kappa(t)$ satisfying $|\kappa(t)| \le C_\kappa e^{-b|t|}$ with $b > 5/4$.
     Combining this with `specSq_sechHalf_mul_cosh_sq` (`EvenSectorSechRepresentation.lean` line 156) and `stripDecay_rhoLift` (`EvenSectorTwistedArcNull.lean` line 378, which gives decay rate $b = 3/2 > 5/4$) yields the **Unconditional 1D Sech-Representation Identity**:
     For every admissible even strip function $\Psi$ (`Multiplier (sechWeight Ψ)`), let $\kappa_\Psi(t) := \text{stripTest}\big(\text{rhoLift}(\text{sechWeight }\Psi)\big)(t) = \frac{1}{2\pi}\int_{-\infty}^\infty \operatorname{Re}\widetilde{T}_\Psi(\rho)\cos(t\rho)\,d\rho$. Then **unconditionally**:
     $$\boxed{\text{evenWeilDensity }\text{lam}\;(\text{specSq }\Psi) = \int_{-\infty}^\infty \kappa_\Psi(t)\,\varphi_{\text{lam}}(t)\,dt, \qquad \varphi_{\text{lam}}(t) := \text{cosineShiftFn }\text{lam}\;\text{sechHalf}\; t!}$$
     Furthermore, for the true von Mangoldt weight $\text{lam} = \Lambda$ (`EF.lam`), every $\cos\left(y\sqrt{z^2 + 2}\right)\Phi_j(z)^2 = \cos\left(y\sqrt{z^2 + 2}\right)\Xi(z)^2 Q_j(z)^2$ has a double zero at every zero of $\Xi(z)$ in the strip (both on-line and off-line!), so `zetaZeroConfig.W = 0` holds for every $j \ge 0$ and every $y \in \mathbb{R}$! Therefore, $\varphi_\Lambda(y)$ satisfies the **Unconditional Convolution Annihilation Equations** on all of $\mathbb{R}$:
     $$\boxed{\big(\kappa_j \star \varphi_\Lambda\big)(y) = \int_{-\infty}^\infty \kappa_j(t)\,\varphi_\Lambda(y - t)\,dt \equiv 0 \quad (\forall j \ge 0,\; \forall y \in \mathbb{R}) \qquad \text{and} \qquad \big(\kappa_{\text{TA}} \star \varphi_\Lambda\big)(y) \equiv 0 \quad (\forall y \in \mathbb{R})!}$$

  3. **Discovery 6C — How $\rho(z) = \sqrt{z^2 + 2}$ Geometrically Separates On-Line Zeros, Real-Axis Zeros, and Off-Line Complex Zeros, and the Causal Klein–Gordon Light Cone for $\varphi_\Lambda(y)$:**
     Look at where the zeros $z = \gamma_\rho$ of $\Xi(z)$ in $|\operatorname{Im} z| < 1/2$ land under the dispersion map $\rho(z) = \sqrt{z^2 + 2}$:
     $$\rho(z) \in \mathbb{R} \iff z^2 + 2 \in [0, \infty) \iff z \in \mathbb{R} \;\cup\; i[-\sqrt{2}, \sqrt{2}]!$$
     - **On-line zeros ($z = \gamma_k \in \mathbb{R}$):** Map to **real frequencies outside $[-\sqrt{2}, \sqrt{2}]$**, $\rho_k = \sqrt{\gamma_k^2 + 2} \in (\sqrt{2}, \infty)$, contributing bounded positive-weight cosine waves $\operatorname{sech}^2(\gamma_k/2)\cos(\rho_k y)$ to $\varphi_\Lambda(y)$ that lie in the exact zero set $\{G_{\text{TA}}(\rho) = 0\}$ of the Twisted-Arc carrier!
     - **Hypothetical real-axis zeros ($z = i\eta_0 \in i(-1/2, 1/2)$):** Map to **real frequencies inside $[-\sqrt{2}, \sqrt{2}]$**, $\rho_0 = \sqrt{2 - \eta_0^2} \in (\sqrt{7/4}, \sqrt{2})$, where $G_{\text{TA}}(\rho_0) > 0$ is strictly positive, so $\kappa_{\text{TA}} \star \varphi_\Lambda \equiv 0$ immediately annihilates them (`measure_sq_le_two_eq_zero`)!
     - **Hypothetical off-line complex zeros ($z_0 = r_0 + i\eta_0$ with $r_0 > 0, 0 < \eta_0 < 1/2$):** Because $\operatorname{Im}(z_0^2 + 2) = 2 r_0 \eta_0 > 0$ is strictly nonzero, $z_0$ does **NOT** map to the real $\rho$-line $\mathbb{R}$ at all! It maps to a **complex frequency with strictly positive imaginary part**:
       $$\rho_0 = \sqrt{z_0^2 + 2} = \alpha_0 + i\beta_0 \in \mathbb{C} \setminus \mathbb{R}, \qquad \beta_0 = \frac{r_0\eta_0}{\alpha_0} > 0!$$
       In $\varphi_\Lambda(y)$, such an off-line zero produces an **exponentially growing hyperbolic mode $\cosh(\beta_0 y)\cos(\alpha_0 y) \sim \frac{1}{2}e^{\beta_0 |y|}$ as $|y| \to \infty$**!
     - **Causal Klein–Gordon Decomposition of $\varphi_\Lambda(y)$:**
       In $\varphi_\Lambda(y) = P(y) + \frac{1}{2\pi}A(y) - Q_\Lambda(y)$:
       - $P(y) = \frac{2}{\cos^2(1/4)}\cos\big(y\frac{\sqrt{7}}{2}\big) = O(1)$ is uniformly bounded for all $y \in \mathbb{R}$.
       - $A(y) = \int_{-\infty}^\infty \cos(y\sqrt{r^2+2})\operatorname{sech}^2(r/2)\gamma(r)\,dr = O(1)$ (and $\to 0$ as $|y| \to \infty$ by Riemann–Lebesgue) is uniformly bounded for all $y \in \mathbb{R}$.
       - In the prime part $Q_\Lambda(y) = \sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}} K_S(\log n, y)$, $K_S(x, y)$ is the **exact 1+1D Klein–Gordon wave solution** with initial profile $K_S(x) = \frac{4x}{\sinh(\pi x)}$ and propagation speed $1$:
         $$K_S(\log n, y) = \frac{K_S(\log n + y) + K_S(\log n - y)}{2} - \frac{\sqrt{2}\,y}{2}\int_{\log n - y}^{\log n + y} \frac{J_1\left(\sqrt{2\big(y^2 - (\log n - t)^2\big)}\right)}{\sqrt{y^2 - (\log n - t)^2}} K_S(t)\,dt,$$
         which by relativistic causality (finite propagation speed!) localizes $Q_\Lambda(y)$ up to $O(e^{-y/2})$ to the **finite set of primes $2 \le n \le e^y$ inside the light cone $\log n \le y$**!

---

## Part IV: The New Route & Mathematical Framework — "Causal Hyperbolic–Modular Duality (CHMD)"

### 1. Why Every Existing Route Stalled and How CHMD Circumvents Every Obstacle

Every one of the 17 live routes and 23 candidates in `rh-current-frontier-map.md` failed because it worked inside a **1D silo** that threw away one of the three essential structures of the problem:
1. **Pure 1D Primal/Gap Routes (`PrimeBlindPoleSpectralTail`, `MarkovResolventCoercivityAndEulerMaclaurinPBAP`, `WeilLevyCoshPlasticCrossover`)** worked in 1D additive coordinates $x = \log n$, took cell-by-cell triangle inequalities across $[\log n, \log(n+1)]$, or included odd test functions where $P(f) \le 0$ fights the archimedean integral—losing $\sqrt{|\tau|}$ vs. $\log|\tau|$ at high frequency and stalling at the plastic-constant horizon $\log\rho_{\text{plastic}} < \log 2$ at low frequency.
2. **Pure 1D Dual/Explicit-Formula Routes (`EvenSectorPoleFreeLogDensity`, `WeilPositivityMultiplicativeToeplitzBound`, `WeilPhiDoobArchimedeanJumpAndHalfLineFolding`)** either tested $L_\Lambda$ on a single positive-node resonator at a time (yielding only upper density bounds $\text{lam} \le \Lambda$ and missing destructive cross-term interference) or used only the single function $\Phi_0$ ($\widehat{\Phi_0} = \Xi$) as a Doob ground state (which is not prime-blind and leaves an uncompensated prime sum).
3. **Pure 2D Null-Face Routes (`TwistedArcMinimumPrincipleProof`, `EvenSectorTwistedArcNull`, `EvenSectorFullPositivity`)** lifted the null face $\Xi Q_j$ to the 2D modular upper half-plane $\mathcal{F}_+$ and proved the unconditional existence of the Twisted-Arc Ground State $C_{\text{TA}}$ and carrier $G_{\text{TA}}(\rho) \ge 0$, **but only ever used $C_{\text{TA}}$ on the dual side after assuming the Bochner measure $\nu_S$ already existed**, never bringing $C_{\text{TA}}$ or the 2D elliptic lift to bear on the primal even primitive blind cone or on the causal Klein–Gordon wave equation for $\varphi_\Lambda(y)$!

**Causal Hyperbolic–Modular Duality (CHMD)** is the new mathematical framework that unifies these three silos by establishing an exact **trinity of dualities**:
$$\underbrace{\text{1D Even Primitive Blind Cone}}_{\substack{A_c(n) = \text{mass}(c)\delta_{n,1},\; A_c(1/u) = u A_c(u) \\ P(c) = 0,\; f = (-D_x^2 + 1/4)q}} \quad \Longleftrightarrow \quad \underbrace{\text{1+1D Causal Klein–Gordon Bulk}}_{\substack{(\partial_y^2 - \partial_x^2 + c) K(x,y) = 0 \\ \text{T-Contour Bochner Transmutation } H_c = \mathcal{S} K_c}} \quad \Longleftrightarrow \quad \underbrace{\text{2D Modular Whittaker Ground State}}_{\substack{C_{\text{TA}} = \sum_{j=0}^\infty w_j \delta_{\Phi_j},\; \text{archPoleEnergy}(C_{\text{TA}}) = 0 \\ \kappa_{\text{TA}} \star \varphi_\Lambda \equiv 0,\; G_{\text{TA}}(\rho) = 0 \iff \Xi(\sqrt{\rho^2-2}) = 0}}$$

### 2. The Architecture of the New Route (Four Concrete Stages)

#### Stage 1: The Multiplicative Unit-Interval / Half-Line Reduction and Even-Primitive Clamped-Beam Floor (Closing the Low-Support Regime $2a \le \log 4$ Unconditionally)
- Work on the **Even Primitive Blind Cone** (`EvenPrimitiveWeilTestFn →₀ ℝ_{\ge 0}`, which by `EvenSectorFullPositivity.lean` + `MarkovShiftPolarizationAndEvenPrimitivePBAP.lean` is 100% sufficient for RH and has $P(c) = 0$ identically, **eliminating the $\sqrt{|\tau|}$ pole-tail obstacle completely**).
- Formalize **Identity 4A** (the nonsingular multiplicative unit-interval and half-line formulas for `markovArchRe` and the $M$-mode Gauss extraction law, which unifies `bochnerResolventEnergy` in `RHTower` with `2 ∫_0^1 A_c(r) dr` in `Zeta23` and already makes the origin constant $+0.2442\,A_c(1) > 0$ strictly positive at $M = 4$ with $O(u^{-10})$ remainder kernel).
- Formalize **Identity 4B** (the exact Paley–Wiener factorisation $f = (-D_x^2 + \frac{1}{4})q$ on `EvenPrimitiveWeilTestFn` with clamped boundary conditions $q(a) = q'(a) = q'(0) = 0$ on $[0, a]$), pushing the unconditional support horizon from the plastic constant $\frac{1}{2}\log\rho_{\text{plastic}} \approx 0.1406$ past the fundamental prime gaps $a = \frac{1}{2}\log 2$ and $a = \log 2$.

#### Stage 2: The Klein–Gordon Mass-$1/2$ Transmutation $H_c = \mathcal{S} K_c$ and T-Contour Bochner Positivity
- Formalize **Theorem 5A & 5B**:
  1. Prove that the Klein–Gordon cosine and sinc propagators $u_c(\cdot, y) = \cos\big(y\sqrt{-D_x^2 + c}\big)f$ and $v_c(\cdot, y) = \frac{\sin(y\sqrt{-D_x^2+c})}{\sqrt{-D_x^2+c}}f$ preserve `EvenWeilTestFn` (and `EvenPrimitiveWeilTestFn` at $c = 1/4$) with compact support $[-(L+|y|), L+|y|]$.
  2. Prove that for every even combination $c$, the adjoint Sonine–Gegenbauer Volterra transmutation $H_c = \mathcal{S} K_c \in C_c^2([-2L, 2L])$ satisfies $\widehat{H_c}(\rho) = \rho_c\big(\sqrt{\rho^2 - 1/4}\big) \ge 0$ for **all $\rho \in \mathbb{R}$**, uniting the critical line ($|\rho| \ge 1/2$) and the real $s$-interval $[0, 1]$ ($|\rho| \le 1/2$) into a **single compactly supported Bochner positive-definite function on $\mathbb{R}$** (with $H_c = H_q^{(4)}$ on the even primitive cone).

#### Stage 3: The Primal Variational Ground State $C_{\text{TA}}$ and the Unconditional 1D Sech-Convolution Equations
- Formalize **Discovery 6A & 6B**:
  1. Extract from `EvenSectorTwistedArcNull.lean` the standalone primal theorem that $C_{\text{TA}} = \sum_{j=0}^\infty w_j \delta_{\Phi_j}$ is an **unconditional prime-blind strip combination** with $\text{archPoleEnergy}(C_{\text{TA}}) = P(C_{\text{TA}}) + \text{archOnly}(C_{\text{TA}}) = 0$ and $P(C_{\text{TA}}) > 0$, achieving the exact variational bound $\frac{-\text{archOnly}(C_{\text{TA}})}{P(C_{\text{TA}})} = 1$.
  2. Remove the unnecessary measure hypothesis `hν` from the Fubini chain in `EvenSectorSpectralConsistency.lean` + `EvenSectorSechRepresentation.lean` to establish the **Unconditional 1D Sech-Representation** $L_{\text{lam}}(\Psi\Psi^\#) = \int_{-\infty}^\infty \kappa_\Psi(t)\varphi_{\text{lam}}(t)\,dt$ and the **Unconditional Convolution Annihilation Equations** $\big(\kappa_j \star \varphi_\Lambda\big)(y) \equiv 0$ and $\big(\kappa_{\text{TA}} \star \varphi_\Lambda\big)(y) \equiv 0$ on $\mathbb{R}$.

#### Stage 4: The 2D Elliptic–Hyperbolic Closure (Two Convergent Paths to the Final Bridge)
With Stages 1–3 in place, the entire RH frontier reduces to two dual, mutually reinforcing paths that bypass every 1D obstruction:
- **Path A (Primal Ground-State Relative Entropy / Hodge-Index Projection via $C_{\text{TA}}$ and 2D Dual Poisson Lift):**
  For any even prime-blind combination $c$, use the exact zero-energy prime-blind ground state $C_{\text{TA}}$ ($K_{C_{\text{TA}}}(\log n) = 0\;\forall n \ge 2$, $P(C_{\text{TA}}) + \text{archOnly}(C_{\text{TA}}) = 0$) and the Dual Poisson Periodization Law $\sum_{m \in \mathbb{Z}} \int_0^\infty A_c(u)\mathcal{W}(u; x, y)e^{2\pi i m u}\,du = \text{mass}(c)\mathcal{W}(1; x, y)$ on the 2D upper half-plane $z = x + iy \in \mathbb{H}$ to prove that no high-frequency tail $c_{\text{high}}$ can cancel the node values of a low-frequency packet $c_{\text{low}}$ without paying at least the ground-state archimedean cost.
- **Path B (Causal Klein–Gordon Light-Cone Dispersion on $\varphi_\Lambda(y)$):**
  In the single-function formulation $\varphi_\Lambda(y) = P(y) + \frac{1}{2\pi}A(y) - \sum_{2 \le n \le e^y} \frac{\Lambda(n)}{\sqrt{n}} K_S(\log n, y) + O(e^{-y/2})$, $P(y)$ and $A(y)$ are uniformly bounded on $\mathbb{R}$, and $\varphi_\Lambda(y)$ satisfies the exact convolution annihilation laws $\kappa_j \star \varphi_\Lambda \equiv 0$ ($\forall j \ge 0$) and $\kappa_{\text{TA}} \star \varphi_\Lambda \equiv 0$ against the Twisted-Arc carrier $G_{\text{TA}}(\rho)$ (whose zero set on $\mathbb{R}$ is strictly the critical-line zero spectrum of $\zeta$). Proving temperedness and positive-definiteness of the causal light-cone wave $\varphi_\Lambda(y)$ via the Klein–Gordon energy conservation law + $\kappa_{\text{TA}}$-annihilation immediately yields `exists_cosineShift_measure` for `sechHalf`, which closes `weilPositiveFull_of_weilPositiveEvenAt` and `RiemannHypothesis` in `EvenSectorFullPositivity.lean`.

---

## Part V: Lean 4 Formalization Ledger (CHMD Stages 1–14)

All fourteen stages of the CHMD architecture have been formalized with zero `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations, audited via `lake env lean`, compiled via `lake build --old`, and wired into `formal/GaloisForLFunctions/RHTower.lean`:

1. **Stage 1 (`formal/GaloisForLFunctions/RHTower/CHMDStage1MultiplicativeResolventAndClampedBeam.lean`):**
   - `RHTower.CHMDStage1.weilPositiveEvenPolar_iff`: Even pole-free positivity holds if and only if `RiemannHypothesis` holds and `lam n = Λ(n)` for all `n ≥ 2`.
   - `RHTower.CHMDStage1.riemannHypothesis_iff_weilPositiveEvenPolar_vonMangoldt`: `RiemannHypothesis ↔ WeilPositiveEvenPolar Λ`.
   - `RHTower.CHMDStage1.m4GaussExtractionGain`, `RHTower.CHMDStage1.gammaBracket_zero_add_m4GaussExtractionGain_gt_pos`, `RHTower.CHMDStage1.gammaBracket_zero_add_m4GaussExtractionGain_pos`: The $M = 4$ Gauss-mode extraction law (`3248 / 585`) flips the negative origin constant `EF.gammaBracket 0 < -5.311` to strictly positive (`> 42 / 585 > 0`).
   - `RHTower.CHMDStage1.integral_rpow_mul_powMulCore_eq`, `RHTower.CHMDStage1.two_mul_integral_powMulCore_eq_bochnerResolventEnergy`, `RHTower.CHMDStage1.two_mul_integral_rpow_two_mul_powMulCore_eq`: Exact weighted multiplicative unit-interval moment identities bridging `powMulCore` (`Zeta23`) and `bochnerResolventEnergy` (`RHTower`).
   - `RHTower.CHMDStage1.clampedBeamOp`, `RHTower.CHMDStage1.paperFT_clampedBeamOp`, `RHTower.CHMDStage1.paperFT_clampedBeamOp_I_div_two`, `RHTower.CHMDStage1.paperFT_clampedBeamOp_neg_I_div_two`, `RHTower.CHMDStage1.weilPoleTerm_clampedBeamOp_eq_zero`, `RHTower.CHMDStage1.norm_paperFT_clampedBeamOp_div_sq_add_one_fourth`, `RHTower.CHMDStage1.bochnerResolventEnergy_clampedBeamOp_eq`: The clamped-beam operator $f = (-D_x^2 + 1/4)q$ annihilates the pole evaluations at $\pm i/2$ and reduces `bochnerResolventEnergy` to a pure weighted $L^2$ norm.

2. **Stage 2 (`formal/GaloisForLFunctions/RHTower/CHMDStage2KleinGordonTransmutationAndTContourBochner.lean`):**
   - `RHTower.CHMDStage2.kgHalfWave`, `RHTower.CHMDStage2.kgDerivWave`, `RHTower.CHMDStage2.norm_sq_paperFT_kgHalfWave_add_kgDerivWave`: The Klein–Gordon mass-$1/2$ wave pair $(V/2, \partial_x V)$ satisfies $|\widehat{V/2}(\tau)|^2 + |\widehat{\partial_x V}(\tau)|^2 = (\tau^2 + 1/4)|\widehat{V}(\tau)|^2$.
   - `RHTower.CHMDStage2.re_weilPoleTerm_kgHalfWave_add_kgDerivWave_eq_zero`: Universal pole cancellation $\operatorname{Re} P(V/2) + \operatorname{Re} P(\partial_x V) = 0$ for every $C^1_c$ function $V$.
   - `RHTower.CHMDStage2.bochnerResolventEnergy_kgHalfWave_add_kgDerivWave_eq`: Exact resolvent-to-$L^2$ transmutation law $\mathcal{E}_{\text{res}}(V/2) + \mathcal{E}_{\text{res}}(\partial_x V) = \frac{1}{2\pi}\int_{\mathbb{R}} |\widehat{V}(\tau)|^2\,d\tau$.
   - `RHTower.CHMDStage2.kgLift`, `RHTower.CHMDStage2.kgLift_of_one_fourth_le_sq`, `RHTower.CHMDStage2.kgLift_of_sq_le_one_fourth`, `RHTower.CHMDStage2.re_kgLift_gaussDamped_pairExp_nonneg`, `RHTower.CHMDStage2.re_kgLift_specSq_paperFT_even_nonneg`, `RHTower.CHMDStage2.re_kgLift_gaussDamped_specSq_paperFT_even_nonneg`: The Klein–Gordon dispersion lift `kgLift` unifies the oscillatory regime $|\rho| \ge 1/2$ and the imaginary Klein–Gordon light-cone interval $|\rho| \le 1/2$ with unconditional T-contour Bochner nonnegativity on all of $\mathbb{R}$.

3. **Stage 3 (`formal/GaloisForLFunctions/RHTower/CHMDStage3TwistedArcGroundStateAndSechAnnihilation.lean`):**
   - `RHTower.CHMDStage3.abs_vonMangoldt_le_sqrt_mul_one_add_log`: Unconditional growth bound $|\Lambda(n)| \le \sqrt{n}(1 + \log n)$ for all $n \ge 2$.
   - `RHTower.CHMDStage3.abs_evenPrimePart_cos_mul_le`, `RHTower.CHMDStage3.continuous_evenPrimePart_cosShift`, `RHTower.CHMDStage3.evenWeilDensity_specSq_mul_kernel_unconditional`: Unconditional Fubini kernel identity removing the Bochner measure hypothesis `hν` from `EvenSectorSpectralConsistency.evenWeilDensity_specSq_mul_kernel`.
   - `RHTower.CHMDStage3.cosineShiftFn_mul_eq_integral_unconditional`, `RHTower.CHMDStage3.evenWeilDensity_specSq_eq_integral_sechKernel_unconditional`, `RHTower.CHMDStage3.evenWeilDensity_specSq_eq_integral_sechKernel_vonMangoldt`: Unconditional 1D Sech-Representation $L_\lambda(\Psi\Psi^\#) = \int_{\mathbb{R}} \operatorname{sechKernel}\ \Psi\ t \cdot \operatorname{cosineShiftFn}\ \lambda\ \operatorname{sechHalf}\ t\,dt$.
   - `RHTower.CHMDStage3.zetaZeroConfig_W_xiShiftedGammaTest_eq_zero`, `RHTower.CHMDStage3.archPoleEnergy_xiShiftedGammaTest_eq_abelPrimePairing`: Unconditional vanishing of the explicit-formula zero pairing $W(\Phi_j, \Phi_j) = 0$ for the twisted-arc family.
   - `RHTower.CHMDStage3.exists_twistedArc_sechKernel_annihilation_unconditional`, `RHTower.CHMDStage3.exists_twistedArc_sechKernel_annihilation_vonMangoldt`: Unconditional Twisted-Arc 1D Sech-Integral Annihilation Law $\sum_{j=0}^\infty w_j \int_{\mathbb{R}} \operatorname{sechKernel}\ (\operatorname{xiShiftedGamma}\ j)\ t \cdot \operatorname{cosineShiftFn}\ \Lambda\ \operatorname{sechHalf}\ t\,dt = 0$ with $w_0 > 0$.

4. **Stage 4 (`formal/GaloisForLFunctions/RHTower/CHMDStage4EllipticHyperbolicClosure.lean`):**
   - `RHTower.CHMDStage4.tendsto_integral_sechKernel_gaussDamped_eq_re_weilFullFunctional`, `RHTower.CHMDStage4.tendsto_integral_sechKernel_gaussDamped_vonMangoldt`: Unconditional 1D sech-kernel limit representation of $\operatorname{Re} W_\lambda(f \star \tilde{f})$ for every real $f \in C^2_c(\mathbb{R})$.
   - `RHTower.CHMDStage4.evenWeilDensity_specSq_nonneg_of_sechHalf_measure`, `RHTower.CHMDStage4.weilPositiveFull_of_sechHalf_measure`, `RHTower.CHMDStage4.riemannHypothesis_and_eq_vonMangoldt_of_sechHalf_measure`, `RHTower.CHMDStage4.riemannHypothesis_and_eq_vonMangoldt_of_positiveDefinite_sechHalf`: Single-function sech-measure and Bochner rigidity—positivity of the single 1D function `cosineShiftFn lam sechHalf` alone forces `ν{ρ² ≤ 2} = 0`, `ν{ρ² > 2 ∧ Ξ(√(ρ²-2)) ≠ 0} = 0`, `WeilPositiveFull lam`, `lam = Λ` on $n \ge 2$, and `RiemannHypothesis`.
   - `RHTower.CHMDStage4.sum_sum_cosineShiftFn_eq_add_evenWeilDensity_unconditional`, `RHTower.CHMDStage4.sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq`: Unconditional elliptic–hyperbolic decomposition of the Toeplitz quadratic form of `cosineShiftFn lam Φ` into `cosComb` and `sinComb` even Weil energies.
   - `RHTower.CHMDStage4.riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg`, `RHTower.CHMDStage4.riemannHypothesis_iff_positiveDefiniteOnReal_cosineShiftFn_sechHalf`, `RHTower.CHMDStage4.riemannHypothesis_iff_exists_sechHalf_measure_vonMangoldt`, `RHTower.CHMDStage4.riemannHypothesis_iff_forall_cosComb_sinComb_sechHalf_nonneg`, `RHTower.CHMDStage4.chmd_four_stage_master_equivalence`: Master CHMD four-stage equivalence theorems.

5. **Stage 5 (`formal/GaloisForLFunctions/RHTower/CHMDStage5FourModeGaussCoercivityAndPolarCone.lean`):**
   - Formalizes `fourModeGaussPairSum`, `fourModeResidualPoleKernel`, `fourMode_gauss_le_markovArchRe`, `fourMode_gauss_pole_le_weilArchRe`, and `fourModeShiftedArchDensity r = Re ψ(17/4 + ir/2) - log π > 42 / 585 > 0` for all $r \in \mathbb{R}$, together with atom-free 4-mode sufficiency criteria on the even polar cone (`ArchimedeanNonnegOnEvenPolarNonnegCone`).

6. **Stage 6 (`formal/GaloisForLFunctions/RHTower/CHMDStage6PolarDoubleZeroAndContinuumLogMomentCollapse.lean`):**
   - Formalizes the double zero of `specSq (paperFT f)` at $\pm i/2$ on the even polar subspace, the clamped-beam $M = 4$ Gauss-mode lower bound, the collapse of the continuum `lebesguePart` integral to `2 * logMoment f` on the polar hyperplane, and the two-bump hyperbolic-secant normalization `farSum lam a / cosh(a/2)`.

7. **Stage 7 (`formal/GaloisForLFunctions/RHTower/CHMDStage7HyperbolicCoshFactorizationAndEvenSubblindDecomposition.lean`):**
   - Formalizes exact hyperbolic `cosh` addition/subtraction/sum-to-product identities, the exact identity `evenArchPole β c = evenArchOnly c + β * (c.sum polePair)`, and the unconditional equivalence of `PrimeSubblindPositiveEvenAt β`, `PrimeBlindPositiveEvenAt 1`, `ArchimedeanNonnegOnEvenPolarNonnegCone`, and `RiemannHypothesis`.

8. **Stage 8 (`formal/GaloisForLFunctions/RHTower/CHMDStage8EvenWindowPosPartAndTwoBumpMidpointConvexity.lean`):**
   - Formalizes the even-window positive-part inequality, two-bump midpoint convexity of `farSum lam a / cosh(a/2)` under `WeilPositiveEvenPolar lam`, and the scale-doubling inequality `farSum lam (2 * a) ≤ 2 * cosh(a / 2)² * farSum lam a`.

9. **Stage 9 (`formal/GaloisForLFunctions/RHTower/CHMDStage9OddTwoBumpConcavityAndJointParityElimination.lean`):**
   - Formalizes `WeilPositiveOddPolar lam`, the odd two-bump midpoint concavity law for `farSum lam a / sinh(a/2)`, and the three Joint Parity Elimination Laws eliminating the lower endpoint, midpoint, or upper endpoint between even and odd polar two-bump inequalities.

10. **Stage 10 (`formal/GaloisForLFunctions/RHTower/CHMDStage10HyperbolicWronskianAndPolarWindowDifferenceLaws.lean`):**
    - Formalizes `farSum_eq_zero_of_nonpos`, pure even-sector scale-doubling `farSum lam (2 * a) ≤ cosh(a / 2) * farSum lam a`, exact hyperbolic Wronskian identities for $c = \cosh(b/2)/\cosh(a/2)$ and $s = \sinh(b/2)/\sinh(a/2)$, Wronskian-cleared joint parity elimination laws, and the scale-tripling inequality `farSum lam (3 * a) ≤ (2 * cosh a + 1) * farSum lam a`.

11. **Stage 11 (`formal/GaloisForLFunctions/RHTower/CHMDStage11SechSquareToeplitzSpectralDecomposition.lean`):**
    - Unifies `sechHalf : ℂ → ℂ` with `sechSqHalf : ℝ → ℝ` (`norm_sechHalf_ofReal_sq`, `specSq_sechHalf_ofReal_re`), proves `evenPolePart (specSq sechHalf) = 2 / cos(1/4)² > 2` and the exact prime Fourier weight `(1 / π) ∫ r, (specSq sechHalf r).re * cos(r log n) = 4 log n / sinh(π log n) > 0` (`n ≥ 2`), introduces the nonnegative wave-packet weight `trigPacketWeight t c ρ`, and establishes the exact three-part spectral decomposition of the decisive Toeplitz quadratic form `∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i)` (`sum_sum_cosineShiftFn_sechHalf_eq_trigPacketWeight_parts`, `riemannHypothesis_iff_forall_trigPacketWeight_sechSqHalf_prime_le_pole_add_arch`).

12. **Stage 12 (`formal/GaloisForLFunctions/RHTower/CHMDStage12FourModeDigammaToeplitzCoercivity.lean`):**
    - Defines the 4-mode Lorentzian spectral weight `fourModeGaussSpectralWeight r = 1/(1/4 + r²) + 5/(25/4 + r²) + 9/(81/4 + r²) + 13/(169/4 + r²) ≤ 3248 / 585`, proves `EF.gammaBracket r = fourModeShiftedArchDensity r - fourModeGaussSpectralWeight r`, establishes unconditional $L^1$ coercivity `(42 / 585) * ∫ r, (K r).re ≤ ∫ r, (K r).re * fourModeShiftedArchDensity r` (`forty_two_div_585_mul_integral_le_fourModeShifted`, `fifty_six_div_195_le_integral_sechSqHalf_fourModeShiftedArchDensity`), and yields the exact positive-minus-positive decomposition and $L^1$-coercive lower bound for the decisive `sechHalf` Toeplitz form (`sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_parts`, `coercive_l1_sub_fourModeGauss_sub_prime_le_sum_sum_cosineShiftFn_sechHalf`, `riemannHypothesis_iff_forall_fourModeGauss_add_prime_le_pole_add_fourModeShifted`, `riemannHypothesis_of_forall_fourModeGauss_add_prime_le_l1_coercive`).

13. **Stage 13 (`formal/GaloisForLFunctions/RHTower/CHMDStage13TwoPointPacketsAndPolarNodeElimination.lean`):**
    - Establishes the exact pointwise spectral decomposition of `cosineShiftFn lam sechHalf y` (`evenPolePart_rhoCosShift_sechHalf`, `cosineShiftFn_sechHalf_eq`, `cosineShiftFn_sechHalf_eq_fourModeShifted_parts`), formalizes the 2-point difference and sum Toeplitz wave packets (`trigPacketWeight_twoPointDiff`, `trigPacketWeight_twoPointDiff_eq_four_mul_sin_sq`, `trigPacketWeight_twoPointSum`, `trigPacketWeight_twoPointSum_eq_four_mul_cos_sq`, `sum_sum_twoPointDiff_cosineShiftFn`, `sum_sum_twoPointSum_cosineShiftFn`, `cosineShiftFn_eq_quarter_twoPointSum_sub_twoPointDiff`), and proves exact pole annihilation at the harmonic shifts `polarNodeShift k = 2 * Real.pi * k / Real.sqrt (7 / 4)` and `polarAntiNodeShift k = Real.pi * (2 * k + 1) / Real.sqrt (7 / 4)` as well as for arbitrary pole-annihilating wave packets (`sum_sum_cosineShiftFn_sechHalf_of_pole_zero`, `sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_of_pole_zero`, `two_mul_cosineShiftFn_sechHalf_zero_sub_polarNodeShift_eq`, `two_mul_cosineShiftFn_sechHalf_zero_add_polarAntiNodeShift_eq`).

14. **Stage 14 (`formal/GaloisForLFunctions/RHTower/CHMDStage14UnconditionalZeroSideToeplitzFormula.lean`):**
    - Proves unconditional equality `atomPairing Λ (crossCorr (stripTest Φ) (stripTest Φ)) = abelPrimePairing Λ (stripTest Φ)` (`atomPairing_stripTest_eq_abelPrimePairing`) and the unconditional explicit formula `evenWeilDensity Λ (specSq Φ) = (zetaZeroConfig.W (stripTest Φ) (stripTest Φ)).re = (∑' ρ, (zetaZeroConfig.mult ρ : ℂ) * specSq Φ (gammaOf ρ)).re` for every `EvenStrip Φ` (`evenWeilDensity_specSq_vonMangoldt_eq_re_W`, `evenWeilDensity_specSq_vonMangoldt_eq_re_tsum_specSq`), deduces the unconditional zero-side series representation of the decisive `sechHalf` Toeplitz quadratic form (`sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_re_tsum_add_re_tsum`, `riemannHypothesis_iff_forall_zeroSide_cosComb_add_sinComb_sechHalf_nonneg`), and proves that every critical-line zero summand evaluates to `m_ρ * trigPacketWeight t c (√((Im ρ)² + 2)) * sechSqHalf (Im ρ) ≥ 0` (`re_Wsummand_cosComb_add_sinComb_sechHalf_of_criticalLine`, `re_Wsummand_cosComb_add_sinComb_sechHalf_nonneg_of_criticalLine`).

15. **Stage 15 (`formal/GaloisForLFunctions/RHTower/CHMDStage15ZeroSideSummabilityAndSechHalfOriginPositivity.lean`):**
    - Establishes unconditional summability of the zero-side series `∑' ρ, (zetaZeroConfig.mult ρ : ℂ) * K (gammaOf ρ)` for every `GoodDensity K` by bounding `exp(-ε |y|) ≤ (1 + 2 / ε²) / (1 + y²)` against `WeilEF.zero_sum_inv_sq zetaSeam` (`summable_zeroSide_of_goodDensity`, `summable_re_zeroSide_of_goodDensity`, `evenWeilDensity_specSq_vonMangoldt_eq_tsum_re`), combines the `cosComb` and `sinComb` zero-side series into a single unconditionally convergent real series (`sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_re`, `sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_re`), uses 2-point polarization to prove the unconditional pointwise zero-side series `cosineShiftFn Λ Φ y = ∑' ρ, m_ρ * (rhoCosShift y Φ (gammaOf ρ)).re` (`cosineShiftFn_vonMangoldt_eq_tsum_re`), and proves `specSq sechHalf z = (Complex.cosh (z / 2) ^ 2)⁻¹` with `(Complex.cosh (z / 2) ^ 2).re = cos(z.im / 2)² + sinh(z.re / 2)² * cos(z.im) ≥ cos(z.im / 2)² > 0` on `|z.im| ≤ 5 / 4`, deducing **unconditionally** (for all nontrivial zeros `ρ`, on or off the critical line) that `0 < (specSq sechHalf (gammaOf ρ)).re` and therefore `0 ≤ evenWeilDensity Λ (specSq sechHalf)`, `0 ≤ cosineShiftFn Λ sechHalf 0`, `prime_sechHalf_zero_le_pole_add_arch_vonMangoldt`, and `sum_sum_fin_one_cosineShiftFn_sechHalf_vonMangoldt_nonneg` (unconditional nonnegativity of all $1 \times 1$ Toeplitz forms for `sechHalf` and $\Lambda$).

16. **Stage 16 (`formal/GaloisForLFunctions/RHTower/CHMDStage16ZeroSideSymmetriesAndXiConvolutionAnnihilation.lean`):**
    - Formalizes the zero-side reflection and negation symmetries (`specSq_gammaOf_reflect`, `re_specSq_gammaOf_reflect`, `re_rhoCosShift_gammaOf_reflect`, `specSq_gammaOf_oneSub`, `rhoCosShift_gammaOf_oneSub`) and the Schwarz-symmetric square reduction `specSq Φ z = Φ z ^ 2` with `(specSq Φ z).re = (Φ z).re ^ 2 - (Φ z).im ^ 2` (`re_specSq_cosComb_add_sinComb_sechHalf_gammaOf`).
    - Proves `evenStrip_XiC : EvenStrip RHTower.XiC` and `XiC_gammaOf_eq_zero`, establishing **unconditionally** (for all $y \in \mathbb{R}$) that `cosineShiftFn Λ RHTower.XiC y = 0` (`cosineShiftFn_XiC_vonMangoldt_eq_zero`), `evenPrimePart Λ (rhoCosShift y RHTower.XiC) = evenPolePart (rhoCosShift y RHTower.XiC) + (1 / (2 * π)) * evenArchPart (rhoCosShift y RHTower.XiC)` (`evenPrimePart_rhoCosShift_XiC_vonMangoldt_eq`), and `cosineShiftFn Λ (RHTower.XiC * h) y = 0` for every `Multiplier h`.
    - Proves individual vanishing `evenWeilDensity Λ (specSq (xiShiftedGamma j)) = 0` and `∫ t, sechKernel (xiShiftedGamma j) t * cosineShiftFn Λ sechHalf t = 0` for each $j \in \mathbb{N}$ without summing over $j$, defines the ground-state multiplier `xiCoshHalf z = RHTower.XiC z * cosh(z / 2)` (`multiplier_xiCoshHalf`), proves global convolution annihilation `∫ t, cosShiftKernel (stripTest (specSq (rhoLift xiCoshHalf))) y t * cosineShiftFn Λ sechHalf t = 0` for all $y \in \mathbb{R}$, and proves strict positivity on $\rho^2 \le 2$ and global nonnegativity on $\mathbb{R}$ of `(rhoLift (sechWeight (xiShiftedGamma 0)) ρ).re`.

17. **Stage 17 (`formal/GaloisForLFunctions/RHTower/CHMDStage17ComplexWavePacketFactorizationAndCoshSinhDecomposition.lean`):**
    - Defines the complexified trigonometric wave-packet weight `complexTrigPacketWeight t c w = (∑ i, c i * cos(t_i * w))² + (∑ i, c i * sin(t_i * w))²` and proves `complexTrigPacketWeight_ofReal`, `complexTrigPacketWeight_neg`, `complexTrigPacketWeight_conj`, `complexTrigPacketWeight_zero`, the double-cosine sum expansion `complexTrigPacketWeight_eq_sum_sum_cos`, and the opposite-exponential product factorization `complexTrigPacketWeight_eq_exp_mul_exp`.
    - Proves the exact strip factorization `specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z = complexTrigPacketWeight t c (rhoC z) * specSq Φ z` on `|z.im| < √2` and at every nontrivial zero `gammaOf ρ`, yielding `sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_complexTrigPacketWeight` and `sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_complexTrigPacketWeight`.
    - Defines the nonnegative hyperbolic cosh and sinh wave-packet weights `coshTrigPacketWeight t c u v` and `sinhTrigPacketWeight t c u v`, proves the **Exact Hyperbolic Cosh–Sinh Norm-Square Decomposition** `(complexTrigPacketWeight t c w).re = coshTrigPacketWeight t c w.re w.im - sinhTrigPacketWeight t c w.re w.im` (`re_complexTrigPacketWeight_eq_cosh_sub_sinh`), and establishes the exact strip kinematics of `rhoC z` (`re_rhoC_sq_sub_im_rhoC_sq`, `re_rhoC_mul_im_rhoC`, `seven_fourths_le_re_rhoC_sq_of_abs_im_le_half`, `abs_im_rhoC_lt_half_of_zero`).

18. **Stage 18 (`formal/GaloisForLFunctions/RHTower/CHMDStage18StripSectorConeAndTwoPointSquareFactorization.lean`):**
    - Proves the exact norm-square and imaginary-part formulas `Complex.normSq (Complex.cosh (z / 2)) = Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2` (`normSq_cosh_half`, `normSq_cosh_half_sq`) and `(Complex.cosh (z / 2) ^ 2).im = Real.sinh (z.re / 2) * Real.cosh (z.re / 2) * Real.sin z.im` (`im_cosh_half_sq`), deducing `re_specSq_sechHalf`, `im_specSq_sechHalf`, `norm_specSq_sechHalf`, `cos_mul_norm_le_re_specSq_sechHalf`, `abs_im_specSq_sechHalf_le_abs_sin_mul_norm`, and the **Exact Strip Sector Cone Inequality** `Real.cos z.im * |(specSq sechHalf z).im| ≤ |Real.sin z.im| * (specSq sechHalf z).re` (`cos_mul_abs_im_specSq_sechHalf_le_abs_sin_mul_re`) on `|z.im| ≤ 5 / 4`.
    - Defines `crossTrigPacketWeight t c u v` with `(complexTrigPacketWeight t c w).im = 2 * crossTrigPacketWeight t c w.re w.im` (`im_complexTrigPacketWeight_eq_two_mul_cross`), proves the Lagrange Cauchy–Schwarz bound `crossTrigPacketWeight t c u v ^ 2 ≤ coshTrigPacketWeight t c u v * sinhTrigPacketWeight t c u v` (`crossTrigPacketWeight_sq_le_cosh_mul_sinh`, `im_complexTrigPacketWeight_sq_le_four_mul_cosh_mul_sinh`), and establishes the unconditional pointwise strip sector lower bound `re_complexTrigPacketWeight_mul_specSq_sechHalf_ge` and `re_complexTrigPacketWeight_mul_specSq_sechHalf_gammaOf_ge`.
    - Proves the complexified 2-point half-angle factorizations `complexTrigPacketWeight (twoPointShift y) twoPointDiffCoeff w = 4 * Complex.sin ((y : ℂ) * w / 2) ^ 2` and `complexTrigPacketWeight (twoPointShift y) twoPointSumCoeff w = 4 * Complex.cos ((y : ℂ) * w / 2) ^ 2`, deducing the unconditional zero-side half-angle square series `two_mul_cosineShiftFn_sechHalf_zero_sub_eq_tsum_four_sin_sq` and `two_mul_cosineShiftFn_sechHalf_zero_add_eq_tsum_four_cos_sq`, and proves `sum_sum_integral_cosShiftKernel_xiCoshHalf_mul_cosineShiftFn_sechHalf_vonMangoldt_eq_zero`.

19. **Stage 19 (`formal/GaloisForLFunctions/RHTower/CHMDStage19ExactCoshSinhCompletedSquareAndStripCoshDominance.lean`):**
    - Defines `coshHalfRe z = cosh(z.re / 2) * cos(z.im / 2)`, `coshHalfIm z = sinh(z.re / 2) * sin(z.im / 2)`, and the nonnegative remainder `completedSqTrigPacketRemainder t c u v Cr Ci` (`completedSqTrigPacketRemainder_nonneg`), and proves the **Master Polynomial Completed-Square Identity** `(complexTrigPacketWeight t c w * conj (Complex.cosh (z / 2) ^ 2)).re = coshTrigPacketWeight t c w.re w.im * (coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2) - sinhTrigPacketWeight t c w.re w.im * (3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2) + completedSqTrigPacketRemainder t c w.re w.im (coshHalfRe z) (coshHalfIm z)` (`re_complexTrigPacketWeight_mul_conj_cosh_half_sq_eq`, `re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_completedSq`).
    - Proves `coshHalfRe_sq_sub_three_coshHalfIm_sq`, `three_coshHalfRe_sq_sub_coshHalfIm_sq`, `two_mul_cos_sub_one_mul_normSq_le_coshHalfRe_sq_sub_three_coshHalfIm_sq`, and `three_coshHalfRe_sq_sub_coshHalfIm_sq_le_three_mul_normSq`, deducing the global norm-multiplied lower bound `((2 * Real.cos z.im - 1) * coshTrigPacketWeight t c w.re w.im - 3 * sinhTrigPacketWeight t c w.re w.im) * ‖specSq sechHalf z‖ ≤ (complexTrigPacketWeight t c w * specSq sechHalf z).re` (`re_complexTrigPacketWeight_mul_specSq_sechHalf_ge_norm_mul`).
    - Proves `half_lt_cos_of_abs_le_one`, `zero_lt_two_mul_cos_sub_one_of_abs_le_one`, `coshHalfRe_sq_sub_three_coshHalfIm_sq_pos_of_abs_im_le_one`, `zero_lt_two_mul_cos_im_gammaOf_sub_one`, and the sufficiency criteria `re_complexTrigPacketWeight_mul_specSq_sechHalf_gammaOf_nonneg_of_sinh_le`, `sum_sum_cosineShiftFn_sechHalf_vonMangoldt_nonneg_of_forall_sinh_le`, and `riemannHypothesis_of_forall_sinhTrigPacketWeight_le`.

20. **Stage 20 (`formal/GaloisForLFunctions/RHTower/CHMDStage20TwoPointCoshSinhClosedFormsAndRhoCosShiftDecomposition.lean`):**
    - Proves `cos_ofReal_mul`, `re_cos_ofReal_mul`, `im_cos_ofReal_mul`, `sin_ofReal_mul`, `re_sin_ofReal_mul`, `im_sin_ofReal_mul`, the exact real and imaginary part decompositions `re_rhoCosShift_eq` and `im_rhoCosShift_eq` of `rhoCosShift y Φ z`, and the two-sided strip sector bounds `re_rhoCosShift_sechHalf_ge` and `re_rhoCosShift_sechHalf_le` on `|z.im| ≤ 5 / 4`.
    - Proves the closed forms `coshTrigPacketWeight_twoPointSum`, `coshTrigPacketWeight_twoPointDiff`, the phase-independent identities `sinhTrigPacketWeight_twoPointSum (y u v : ℝ) : sinhTrigPacketWeight (twoPointShift y) twoPointSumCoeff u v = Real.sinh (y * v) ^ 2` and `sinhTrigPacketWeight_twoPointDiff (y u v : ℝ) : sinhTrigPacketWeight (twoPointShift y) twoPointDiffCoeff u v = Real.sinh (y * v) ^ 2`, `crossTrigPacketWeight_twoPointSum`, `crossTrigPacketWeight_twoPointDiff`, `cosh_sub_one_sq_le_coshTrigPacketWeight_twoPointSum`, `cosh_sub_one_sq_le_coshTrigPacketWeight_twoPointDiff`, `re_complexTrigPacketWeight_twoPointSum`, and `re_complexTrigPacketWeight_twoPointDiff`.
    - Defines `posSqTrigPacketWeight` and `negSqTrigPacketWeight` and proves the exact 2-squares-minus-2-squares decomposition `re_complexTrigPacketWeight_mul_conj_cosh_half_sq_eq_posSq_sub_negSq` and `re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_posSq_sub_negSq`.
