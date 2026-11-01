# Consolidated Mathematical Assessment: Walls, Breakthrough Routes, Thresholds, and Foundational Synthesis

---

## 0. Unified State of the Corpus and Anatomy of the Walls

Across 63 research programmes and all active route families, every live formulation of the Riemann Hypothesis over `ℤ` reduces to reading a single nonnegative even integer on a single codimension-one hyperplane:

$$\kappa(K_\zeta) = \#\{\rho : \xi(\rho) = 0,\ \operatorname{Re}\rho > \tfrac{1}{2}\} \in 2\mathbb{N} \cup \{\infty\}$$

evaluated on the pole-orthogonal hyperplane $v_1^\perp = \{x : \langle x, v_1\rangle = 0\}$ ($v_{1,n} \propto n^{-1/2}$), or equivalently:
- the affine pole-successor glued Krein index $\kappa(\phi_c) = \kappa(K_\zeta) + 1 \in \{1, 3, 5, \dots, \infty\}$ at $\infty$ or at any prime $p$ (`AdelicKreinGeometry`: `negIndex_weilArchState_eq_rightZeros`, `negIndex_weilPadicState_eq_rightZeros`);
- the quantized even collision charge $O = \sum_\rho m_\rho(H_\rho - m_\rho) \in 2\mathbb{N}$ on critical/collided forms (`HilbertianExplicitFormulas`: $O = 0 \iff O < 2 \iff \text{critical}$ on windows; `ConjugateDiagonalGeometry`: `isFredholmOp_integerThetaCollisionOperator`);
- the uniform boundedness of the coprime inter-tower coupling $C_K(u,v) = K(uv) - K(u) - K(v) + K(1)$ on $\langle 2, 3\rangle \times \langle 5, 7\rangle$ (`ArithmeticCouplingTheory`: `riemannHypothesis_iff_exists_bound_coprimeCrossDiff`).

All 33 surviving routes hit **three unified mathematical walls** on $v_1^\perp$:

| Unified Wall | Precise Mathematical Obstruction | Sharp Quantitative Boundary in Lean |
| :--- | :--- | :--- |
| **`U-Σ` (Orientation / Edge Crossing)** | Preserving positivity of $W_{\phi,c,N}\big|_{v_1^\perp}$ across the detection edge $\tau(c)\log N \asymp 1$ (`EdgeHodgeTheory`: `riemannHypothesis_iff_eventually_hyperplaneEdge_eq_top`), where low-conductor floors decay while prime/shell/coherent residuals grow or persist. | Universal PSD holds up to $c \le (\log N)^\alpha$ ($\alpha < 1/144$; packets $\alpha < 1/19$; nonpositive unit confinement $\alpha < 1/16$ via $c^{16}$ separate shell cost). RH-completeness holds at $c_N \asymp L(\log L)^2$ ($L = \log\log N$, `steklovDCProfile`) or $2(\log N)^{\alpha > 0}$ (`unitBump`). |
| **`U-Π` (Trans-$\sqrt{x}$ Prime Precision)** | Controlling signed multiplicative oscillations ($\mu$, $\Lambda$, shifted prime pairs, near-band cyclotomic modes) past the Plancherel / Bombieri–Vinogradov / Nyquist threshold $X = T$, $M = N^{1/2}$, $d \sim Q$. | Sub-threshold Gram traces lock at $2/3$ ($\mathrm{HD}(1) \approx 0.6725$ with Montgomery–Taylor kernel; $+10^{-8}$ via `IGP`). Parity-blind dispersion diverges for all $\lambda > 1$ (`parityBlind_dispersion_diverges_above_threshold`). Coherent prime mode $P_Q(a)$ carries norm $\sum_{p\le Q} \frac{\log p}{p} = \log Q + O(1)$ on $v_1^\perp$ (`CSAR`). |
| **`U-Γ` (Twin & Gauge Selectivity)** | Separating genuine $\zeta$ from fake arithmetic objects that share functional equation, integrality, Ramanujan bounds, or spectral gaps: Golden curve ($q=5$, $\kappa=1$), tempered Beurling twins, Liouville/Dirichlet gauge twins, and sparse prime-sign flips $\omega_P$. | Any gauge-invariant bound forces $\Theta \ge 3/4$ (`threeQuarters_le_of_gaugeInvariant_bound`). Single-prime flips $p \ge 11$ attain maximal hyperplane gap $2\log 2$ yet violate Weil positivity (`maximal_gap_does_not_select_the_source`). `CompletedPositiveSystem 1` characterizes $\mathbb{R}^\times \zeta$, while $\kappa = 2$ already permits off-line zeros (`SBWF`). |

---

## 1. New Proof Mechanisms That Circumvent or Destroy a Wall

Cross-referencing formal theorems proved in separate modules exposes **four non-killed proof mechanisms** that either destroy a specific sub-wall or bypass an entire obstruction class.

### 1.1 Resolving the Profile-Schedule Gap + Pre-Norm Coherent/Shell Cancellation (`TMWP` + `RIT` + `CAF` + `SSh` + `CSAR`)
- **Walls attacked**: Destroys the profile mismatch (`Σ-1`) and separate shell payment $c^{16}$ (`Σ-2`), compressing `U-Σ` + `U-Π` to a two-seam Schur complement.
- **Unconditional Lean anchors**:
  1. *Elimination of the `C²` vs `C^∞` schedule gap on intermediate conductors*: For `tiltedUnitSpline`, RH-completeness on $v_1^\perp$ requires $\alpha > 1/2$, disjoint from `CAF`'s exceptional-conductor theorem ($\alpha < 1/4$). However, `CAF`'s `eventually_exceptionalConductors_above_polylog_empty` and `tendsto_completeWeil_conductorSubspace_negIndex_div_zero` hold for **every** $C^2$ profile supported in $[0,1]$ with $\int \phi^2 > 0$. Applying them to:
     - `steklovDCProfile` at its exact RH-complete schedule $c_N = K L(\log L)^2 = o((\log N)^\alpha)$ for all $\alpha > 0$ (`TMWP`: `riemannHypothesis_iff_steklovDCProfile_critical_multiples`), or
     - an incommensurable two-scale sum of smooth autoconvolutions $\phi(u) = (\eta * \eta)(u - \tfrac{1}{2}) + (\eta_\lambda * \eta_\lambda)(u - \tfrac{1}{2}) \in C_c^\infty([0,1])$ ($\phi \ge 0$, $|\hat\phi(\xi)| = |\hat\eta(\xi)|^2 + \lambda|\hat\eta(\lambda\xi)|^2 > 0$ for all $\xi \in \mathbb{R}$, eliminating real Fourier zeros!) at $c_N = 2(\log N)^\alpha$ with $0 < \alpha < 1/32$ (`RIT`: `riemannHypothesis_iff_completeWeil_hodgeIndex_rpow_log`),
     puts **both** exact RH-completeness on $v_1^\perp$ **and** unconditional positivity $W_{\phi,c_N,N}(v_m) \ge \frac{1-2\theta}{4}\log m > 0$ for every individual conductor $m \in [\lceil (\log N)^A\rceil, \lfloor N^\theta\rfloor]$ ($0 < \theta < 1/2$, any $A > 0$ for `steklovDCProfile`) **into the exact same overlap regime**.
  2. *Destroying the $c^{16}$ separate-payment wall*: The $c^{16}$ barrier arises solely when the non-ratio successor shell $\mathrm{NR}$ ($n = km + h$, $0 < |h| \le \lfloor c\rfloor$) is bounded separately against $\varepsilon D_N + C S_N$ (`SSh`). On the top-band witness, `SSh` proves the **coupled difference** $2\cdot\mathrm{Pole} - \mathrm{NR}$ cancels down to $O(G(c + 1 + \log N))$ uniformly for $1 \le c \le N/4$. Simultaneously, `CSAR` (`PrimeGeneratorOrthogonalRows`) proves on prime-supported packets that $G F_a = P_Q(a) - \sum_{p\le Q} \mathrm{tameDifferent}(p)\,a_p e_p$, where the orthogonal residual has cutoff-independent norm $\le \frac{\log 2}{2} L_Q(a)$ and all logarithmic growth sits in the **single rank-1 scalar functional** $P_Q(a)$.
- **Exact mechanism to close**: Perform block Haynsworth Schur reduction on $v_1^\perp$ at $c_N = K L(\log L)^2$ with respect to the triple decomposition $V_{\text{low}}([2, (\log N)^\varepsilon)) \oplus V_{\text{BV}}([(\log N)^\varepsilon, N^\theta]) \oplus V_{\text{BV}}^\perp$, keeping $2\cdot\mathrm{Pole} + \Gamma - \mathrm{NR} - P_Q$ grouped inside a single rank-2 scalar channel **before** applying Cauchy–Schwarz.

### 1.2 Lossless Four-Prime Inter-Tower Coupling + Mertens Nondivisibility Polarization (`ACoT` + `CSAR` + `AKG`)
- **Walls circumvented**: Completely bypasses full $\mathbb{Q}_{>0}$ assembly, running $\log N - \gamma$ counterterms, and Diophantine approximation losses.
- **Unconditional Lean anchors**:
  - `BoundedCouplingIsTheRiemannHypothesis`: $\text{RH} \iff \sup_{(u,v) \in \langle 2,3\rangle \times \langle 5,7\rangle} \|C_{\mathrm{ratCorr}}(u,v)\| < \infty$, and `zetaZeroWidth_le_iff_coupling_rate` gives $\sup(\operatorname{Re}\rho - \tfrac{1}{2}) \le \sigma \iff |\operatorname{Re} C_{\mathrm{ratCorr}}(u,v)| \le C e^{\sigma h(u,v)}$ with **zero exponent loss**.
  - Because $C_K(u,v) = K(uv) - K(u) - K(v) + K(1) = W((T_{u^{-1}} - 1)f, (T_v - 1)f)$ is a double difference across coprime semigroups, every axial self-energy, constant mode, and separable diagonal divergence vanishes identically (evading `AKL`'s `negIndex_localAssembly_eq_top` without archimedean counterterm tuning).
  - `ACoT`'s Mertens polarization rewrites prime energy on centered incidence packets $F_b(n) = \sum_{p \in P} b_p(\mathbf{1}_{p\mid n} - 1/p)$ in terms of exact nonnegative nondivisibility counts $J_N(F_b) \ge 0$ modulated by $\log N + \mu(N/n)$, while `CSAR` (`AffineWindowEnergy`) makes complete-period conductor energy observable at quadratic horizon $N \sim Q^2$ rather than $Q!$.
- **Exact mechanism to close**: Bound the four-point CRT divisibility-incidence discrepancy between $\langle 2,3\rangle$-differences and $\langle 5,7\rangle$-differences at horizon $N \sim (uv)^2$, using $\mathbb{Z}$-successor intervals to enforce `U-Γ` selectivity (since sparse flips $\omega_p$ for $p \notin \{2,3,5,7\}$ enter $C_{\mathrm{ratCorr}}(u,v)$ only through composite cofactors inside the exact explicit-formula window $\le e^{2L+8}$).

### 1.3 Two-Cutoff Compensation + $\{2,3\}$ Escape-Row Confinement + `JAS` Chain Exclusion (`ACompT` + `ADR` + `RHTower`)
- **Walls circumvented**: Eliminates single-cutoff harmonic divergence $H_N \sim \log N$ (`Π-1` / `Π-4`) and continuum power-tail escape (`Σ-7`).
- **Unconditional Lean anchors**:
  - `RHTower/JointAncestryQuasiRHChainExclusion` (`riemannHypothesis_iff_jasDressedPSD_one_and_quasi`):
    $$\text{RH} \iff \mathrm{JasDressedPSD}(1) \ \wedge\ \bigl(\exists \alpha < \tfrac{1}{2},\ \mathrm{XiZeroHalfPlaneBound}(\alpha)\bigr).$$
    Any unconditional Quasi-RH ($\alpha < 1/2$) **eliminates off-line chain escape** and reduces full RH to `JasDressedPSD 1`.
  - `ACompT`: While single-cutoff pronic/divisor operators diverge at $\varepsilon \le 1/2$ via $H_N$, the two-cutoff difference $S_Q - S_P$ cancels the harmonic pole and converges in operator norm for $\varepsilon > 1/3$ ($\operatorname{Re} s > 5/6$), with `exists_compensationDefect_le_inv_log_pow` giving $(1 - \alpha_P)^2 + \|R_P\|^2/\|L_P\|^2 \ll (\log P)^{-m}$ for every $m$ on $0 < \varepsilon < 1/2$.
  - `ADR` (`riemannZeta_add_eq_zero_iff_exists_rankOneEscapeRow`): At the row level, renormalized inversion plus Euler laws at just the two primes $\{2, 3\}$ confines all bounded-defect escape vectors to exact $\zeta$-zero eigenspaces.
- **Exact mechanism to close**: Lift weak-* limits of two-cutoff compensated packets $(S_Q - S_P) u_n$ to row solutions invariant under $\{2,3\}$-Hecke transitions (closing `ADR`'s escape-to-row bridge), then combine with Quasi-RH ($\alpha < 1/2$) to discharge `JAS` chain escape.

### 1.4 Non-Holomorphic Resolvent-Theta Identity + Dyadic Collision-Fredholm Transfer (`HEF` + `CDG` + `RBG`)
- **Walls circumvented**: Bypasses holomorphic calibration rigidity (`HEF`: `eq_weilWeight_of_calibrated`, which forbids any entire explicit-formula weight from equalling $|F|^2$ off the critical line) and replaces fragile real inequalities by an integer topological index.
- **Unconditional Lean anchors**:
  - `HEF`: $(\sigma - \tfrac{1}{2}) S(s) - \operatorname{Re}(\xi'/\xi)(s) = D(s) \ge 0$ ($D = 0 \iff \text{RH}$), evaluated explicitly via theta-prime at $s = 4$ (`xiResolventDepth_four_eq_thetaPrime`).
  - `CDG` (`isFredholmOp_integerThetaCollisionOperator`, `floor_finiteThetaCollisionReading_eq_of_stage`): The horizontal collision charge $O(T) \in 2\mathbb{N}$ on $[-T, T]$ equals the integer Wiener–Hopf Fredholm index of an explicit finite integer-theta operator, so **any** upper bound $O(T) < 2$ forces $O(T) = 0$.
  - `RBG` / `CDG` (`heckeDefect_sq_le_two_scale`): Lossless nonlinear two-scale amplification $E(L)^2 \le D(f)\bigl(E(2L) - 4 E(L)\bigr)$ transfers a single subexponential bound on the collided Hecke defect $E(2^k L)$ at one high dyadic scale down to **all** smaller scales ($W = D \iff E = 0 \iff \text{RH}$).
- **Exact mechanism to close**: Bound the moving divisor tail of `CDG`'s positive integer-theta reading of $E(f, L)$ at a single logarithmic scale $L \asymp \log T$ strongly enough to force unit-window increment $\Delta O(T) < 2$ (hence $\Delta O(T) = 0$ by parity quantization $O \in 2\mathbb{N}$).

---

## 2. Wildly Different Approaches to RH Not Touching the Existing Walls

### 2.1 Invariant Meta-Constraints Any Valid Proof Must Satisfy
Before proposing orthogonal routes, the Lean corpus establishes strict impossibility theorems ruling out 45 classical "wildly different" templates (`rh-killed-routes.md`):
1. **No integer Frobenius or commuting ring correspondence** (`AGT`: `approxRingEndomorphism_classification`; `ACS`: `heckeCorrespondence_no_square_relation`): Over $\mathbb{Z}$, multiplicative dilations form a free abelian monoid of isometric boosts without a degree-scaling endomorphism $x \mapsto x^q$.
2. **No gauge-invariant or finitely-determined proof beyond $3/4$** (`AGT`: `threeQuarters_le_of_gaugeInvariant_bound`): Any argument invariant under prime phases $G = \operatorname{Hom}(\mathbb{N}_{\ge 1}, S^1)$ (such as pure $L^2$ large-sieve / Montgomery–Vaughan bounds) stops at $\operatorname{Re} s \le 3/4$.
3. **No height-positivity / functional-equation proof without $\mathbb{Z}$-incidence** (`SBWF`: `completedPositiveSystem_one_iff`): `CompletedPositiveSystem 1` characterizes $\mathbb{R}^\times \zeta$, while $\kappa = 2$ already admits off-line zeros.
4. **No finite-alphabet SFT or orthogonal high-moment amplifier** (`ART`: `isPrimeLength_of_realization`, `pow_sum_le_moment_of_isBrauer`): Finite additive SFTs collapse to commutative prime loops with nuclearity breakdown at $s = 1$; rank $\pi(y) \to \infty$ forces Brauer $2k$-th moment cost $\binom{r+k-1}{k}$ unless moments are evaluated by a $k$-independent algebraic identity.

Thus, an approach that **never touches `U-Σ`, `U-Π`, or `U-Γ` in their Weil/Gram/sieve form** must operate outside quadratic positivity, finite SFTs, and $L^2$ Dirichlet polynomials altogether, while natively fusing $+1$ and $\times p$ on $\mathbb{Z}$. Three genuinely orthogonal paradigms satisfy all four meta-constraints:

### 2.2 Paradigm A: Infinite-Alphabet `PSL₂(ℤ)` Gauss–Mayer Nuclear Transfer & `A₁` Loop-Eisenstein Scattering
- **Why it avoids `ART`'s SFT collapse and all three Gram walls**: `ART` kills *finite-alphabet* SFTs because prime-length cycles are forced to be disjoint or freely mixed ($\sigma_* \in (1,2)$). By contrast, the continued-fraction Gauss map $T(x) = \{1/x\}$ on $(0,1]$ has a **countably infinite alphabet** $\mathbb{N}_{\ge 1}$ generated by the non-commuting pair $z \mapsto z + 1$ (additive successor!) and $z \mapsto 1/z$ (archimedean inversion!), whose group is literally $\mathrm{PSL}_2(\mathbb{Z})$.
- **Native connection to the corpus**: Mayer's transfer operator $\mathcal{L}_s f(z) = \sum_{n=1}^\infty (z+n)^{-2s} f(\frac{1}{z+n})$ is **nuclear of order $0$** on holomorphic disks, and its Fredholm determinant factorizes Selberg's zeta function together with the $\mathrm{SL}_2(\mathbb{Z})$ Eisenstein scattering matrix $\phi(s) = \Lambda(2s-1)/\Lambda(2s)$. In `RenormalizedIntersectionTheory`, the `A₁` loop-Eisenstein factor $\Lambda(s)/\Lambda(s+1)$ is already proved to have pole count in $(-1/2, 0)$ equal to $\kappa(K_\zeta)$.
- **Wildly different mechanism**: Instead of proving positivity of a Hermitian form (`U-Σ`), study **spectral/dynamical exclusion of scattering resonances** in $(-1/2, 0)$ via non-abelian $\mathrm{PSL}_2(\mathbb{Z})$ modular symbols, hyperbolic geodesic coding, and Padé/continued-fraction approximants—where $+1$ and $\times$ are unified in $2\times 2$ integer matrices $\bigl(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\bigr)$, rendering Beurling/Liouville/prime-flip twins (`U-Γ`) non-modular at step zero.

### 2.3 Paradigm B: Arithmetic Transcendence & Nonlinear Böttcher–Monodromy Period Rigidity
- **Why it never touches quadratic positivity (`U-Σ`) or $L^2$ sieve barriers (`U-Π`)**: All existing routes linearize $\zeta$ into Hilbert spaces, Fourier transforms, or Dirichlet polynomials. In `Bottcher` and `ArithmeticHarmonicAnalysis`, two nonlinear rigidities appear:
  1. Böttcher coordinates conjugate entire/meromorphic flows near infinity to canonical power maps, whose critical-point monodromy obstructions encode zero locations geometrically rather than spectrally;
  2. `AHA` (`algebraic_primeLogTrace_firstJets_vanish_iff`) proves that while real-log auxiliary functions have blind transverse jets, **Baker / Gelfond–Schneider linear independence of $\log p$ over $\overline{\mathbb{Q}}$** forces first vertical jets at algebraic points to detect *all* partial derivatives simultaneously.
- **Wildly different mechanism**: Formulate off-line quartets $\{\rho, 1-\rho, \bar\rho, 1-\bar\rho\}$ ($\operatorname{Re}\rho \ne 1/2$) as **symmetry-breaking monodromy/period defects** of a nonlinear differential or Mahler/q-difference equation coupled to integer theta/factorial periods, and exclude $\operatorname{Re}\rho \ne 1/2$ by **transcendence / Diophantine height lower bounds** (André–Oort / Bost–Charles / formal-group integrality over $\mathbb{Z}$) rather than norm inequalities. Transcendence methods routinely cross $\sqrt{x}$ (`U-Π`) without Cauchy–Schwarz and depend rigidly on exact $\mathbb{Z}$-integrality (`U-Γ`).

### 2.4 Paradigm C: Two-Place ($2$-Adic $\leftrightarrow$ Archimedean) Krein-State Reciprocity
- **Unconditional Lean foundation**: `AdelicKreinGeometry` proves **both** `negIndex_weilArchState_eq_rightZeros` (glued at $\infty$) **and** `negIndex_weilPadicState_eq_rightZeros` (glued at any prime $p$, in particular $p = 2$):
  $$\kappa(\phi^{(\infty)}) = \kappa(\phi^{(2)}) = \kappa(K_\zeta) + 1.$$
- **Why it is structurally orthogonal**: Every archimedean route fights smooth Fourier tails and the overlap edge $\tau(c)\log N \asymp 1$ (`U-Σ`). On $\mathbb{Q}_2$, valuation balls $2^k \mathbb{Z}_2$ are **simultaneously open and closed**: indicator functions of $2$-adic spheres are locally constant with **compact $2$-adic Fourier support and zero tail leakage**. A Čerednik–Drinfeld-style two-place comparison or $2$-adic interpolation of the glued state $\phi^{(2)}$ shifts the index computation from archimedean oscillatory integrals to ultrametric tree operators and $S$-unit reciprocity on $\mathbb{Z}[1/2]^\times$.

---

## 3. Opportunities to Prove Improved Quasi-RH Beyond $1/8 < \operatorname{Re} s < 7/8$

**Yes — there are concrete, quantified opportunities to beat $7/8 = 0.875$, both for all Dirichlet $L$-functions (targeting $23/27 \approx 0.8519$ and $5/6 \approx 0.8333$) and specifically for $\zeta(s)$ (targeting $5/6$ and $3/4 = 0.75$).**

### 3.1 Exact Diagnosis of Where $7/8$ Comes From in Lean
The corpus reveals two distinct mechanisms generating $7/8$:
1. **Prime-Detector Gram Tradeoff (`QuasiRHDetectorScaleBudget.lean`, `QuasiRHDetectorGramTradeoff.lean`)**: In the 3-term Gram upper bound $1 + P^\nu + P^\kappa / Y$ ($X = Z^x$, $Y = Z^{1-\mathrm{slots}-x}$, $P = Y/X$), `gramProfile_published_boundary` proves
   $$\mathrm{gramProfileBoundary}\!\left(\tfrac{17}{48}, \tfrac{1}{6}, \tfrac{1}{6}, 2\right) = \frac{7}{8}.$$
   Retuning $(x,y)$ at fixed $\mathrm{slots} = 1/6$ leaves $7/8$ invariant (`fixed_slot_boundary`), while increasing $\mathrm{slots} > 1/6$ triggers the zero-retained-length reflected face $\max(0, \frac{6\cdot\mathrm{slots}-1}{5})$ (`retunedBoundary_sharp_minimum`).
2. **Cyclotomic / Escaped-Möbius Resonance (`CAF`, `BVI`)**: In `BVI` (`firstBlood_fourThirds_escapedMoebius_iff`), bandwidth $\lambda = 4/3$ maps to $\theta(\lambda) = \frac{\lambda-1}{2\lambda} = \frac{1}{8}$ ($1 - \theta = 7/8$). In `CAF` (`ChebyshevCyclotomicTail.lean`), splitting $\mathrm{Remainder}(N) = \mathrm{Far}(N,K) + \mathrm{Near}(N,K)$ at $K = \lceil (N+1)^{1/4}\rceil$ gives $\mathrm{Far} \le 288 N(N+1)/K = O(N^{7/4})$, corresponding to $r/2 = 7/8$.

### 3.2 Opportunity 3A: Breaking $7/8 \to 23/27 \approx 0.85185$ ($4/27 < \operatorname{Re} s < 23/27$) via Subfield-Projected Shift Moments
- **No improvement to $\kappa = 2$ needed**: `ordinaryGramBoundary_sharp_minimum` proves that keeping the ordinary frequency exponent at its trivial value $\kappa = 2$ and improving **only** the exceptional-frequency exponent $\nu$ from $1/6$ toward $0$ lowers the zero-free boundary monotonically from $7/8$ to **$23/27$** at $(x = 5/18, \mathrm{slots} = 1/6)$. Even a small power saving $s > 0$ at $(17/48, 1/6)$ immediately yields **$7/8 - s/16$** (`gram_power_saving_boundary`).
- **Why $\nu = 1/6$ can be broken**: `QuasiRHSubfieldMoment.lean` (`exists_sextic_subfield_moment_obstruction`) proves that the $q = |S|^3$ obstruction to fourth-moment bounds on $\sum_x |\sum_{a\in S} \chi(x-a)|^4$ arises **exclusively** when $\chi$ has small multiplicative order (specifically order $6$ in $\mathbb{F}_{r^2}/\mathbb{F}_r$ with $6 \mid r+1$) so $\chi|_{\mathbb{F}_r^\times} \equiv 1$ and $S$ concentrates on $\mathbb{F}_r$-affine cosets! Meanwhile:
  - `QuasiRHCharacterCorrelation.lean` (`fourShiftCharacterSum_crossRatio`, `threePointCharacterSum_energy`) proves full square-root cancellation off matching cross-ratios over the complete field;
  - `QuasiRHSubfieldProjection.lean` (`subfield_affineLine_packet_sum`) **already constructs** the exact affine-line occupancy projection measuring $|S \cap (x - u\mathbb{F}_r)|$.
- **Actionable attack**: Unlike arbitrary worst-case subsets $S \subset \mathbb{F}_{r^2}$, the shift sets $S$ produced by prime-detector archimedean windows are projections of **rational/integer arithmetic progressions/intervals**, which have rigid Katz / Bourgain–Chang / Stepanov non-concentration on proper $\mathbb{F}_r$-subfields. Bounding affine-line occupancy on detector shifts lowers $\nu < 1/6$ directly, pushing Quasi-RH below $7/8$ toward **$23/27$**.
- **Bonus at conductor $q = 1$ ($\zeta(s)$ alone)**: `ChenGuptaLiModulusCrossover.lean` (`cgl_source_power_crossover`, `cgl_conductor_one_bounds`) proves the $7/3$ zero-density term dominates Guth–Maynard's $30/13$ **only for $q > T^{12}$**. For $\zeta(s)$ ($q = 1$), the active density exponent is $30/13 \approx 2.3077 < 7/3$, coupled with `RDS2`'s short-window dispersion at $17/30$ (`ShortWindowDispersionAtSeventeenThirtieths.lean`).

### 3.3 Opportunity 3B: Reaching $5/6 \approx 0.8333$ and $3/4 = 0.75$ for $\zeta(s)$ via Chebyshev Cyclotomic Near-Band (`CAF`)
In the detector Gram model, `gramProfile_five_sixths_feasible_iff` requires $\nu \le 1/15$ and $\kappa + 4\nu \le 4/3$ for $5/6$, and `unitGramBoundary_sharp_minimum` proves an absolute floor of **$29/36 \approx 0.8056 > 3/4$** unless the zero-retained-length reflected face is cancelled.

**`CAF` (`ChebyshevCyclotomicCompletion.lean`, `ChebyshevCyclotomicTail.lean`) completely bypasses that $29/36$ floor for $\zeta(s)$:**
- `chebyshevEnergy_power_bound_iff_cyclotomic` proves unconditionally that $\zeta(s) \ne 0$ outside $[1 - r/2, r/2]$ iff $\mathrm{chebyshevCyclotomicRemainder}(N) = O_\varepsilon(N^{r+\varepsilon})$.
- `chebyshevCyclotomicRemainder_eq_far_add_near` + `chebyshevCyclotomicFar_le` **already prove unconditionally**:
  $$\mathrm{Far}(N, K) \le \frac{288\,N(N+1)}{K}.$$
- Setting $K = \lceil (N+1)^{1/3}\rceil$ proves $\mathrm{Far} = O(N^{5/3})$ (**$5/6$ strip**), leaving **only $\le 2 N^{1/3}$ near-constant modes** ($1 \le k \le K$ or $N+1-K \le k \le N$, each of large primitive conductor $m = \frac{N+1}{\gcd(N+1,k)} \ge N^{2/3}$).
- Setting $K = \lceil \sqrt{N+1}\rceil$ (`chebyshevCyclotomicFar_sqrt_le`) **already proves unconditionally** $\mathrm{Far} \le 288 N\sqrt{N+1} = O(N^{3/2})$ (**$3/4$ strip**, `three_quarters_strip_iff_chebyshevCyclotomicRemainder_subpower`), leaving **only $\le 2\sqrt{N}$ near-constant modes** of primitive conductor $m \ge \sqrt{N+1}$!
- Crucially, **$3/4$ is the exact `AGT` gauge-invariance boundary** (`threeQuarters_le_of_gaugeInvariant_bound`): thus $5/6$ and $3/4$ do **not** even violate gauge invariance—they require only moving-conductor Vaughan/large-sieve dispersion on $\le 2K$ smooth long-wavelength Fourier modes of $\psi(n) - n$ (paired with `ACompT`'s two-cutoff operator $S_Q - S_P$, which already converges unconditionally on $\operatorname{Re} s > 5/6$).

### 3.4 Strategic Multiplier: Any Unconditional Quasi-RH Upgrades `JasDressedPSD 1` to Full RH
By `riemannHypothesis_iff_jasDressedPSD_one_and_quasi` (`JointAncestryQuasiRHChainExclusion.lean:1173`), proving **any** unconditional strip $1 - \beta < \operatorname{Re} s < \beta$ ($\beta < 1$, whether $7/8$, $23/27$, $5/6$, or $3/4$) for $\zeta(s)$ permanently kills off-line `JAS` chain escape and reduces the full Riemann Hypothesis to `JasDressedPSD 1`.

---

## 4. Opportunities to Prove At Least 75% of Zeros Lie on the Critical Line

**Yes — 75% ($\ge 3/4$) is the single closest landmark theorem on the frontier of the corpus.** Currently formalized unconditionally: $\ge 67.250071\% - \varepsilon$ simple critical zeros (`lamzouri_montgomeryTaylor_simpleCritical_epsilon` + `IGP` pinching). Three independent, formally anchored routes lead to $\ge 75\%$, with **Route 4.1 sitting right on the factor-$2$ sieve parity boundary**.

### 4.1 Route 4.1 (Highest Immediate Feasibility): Bandwidth-$4/3$ Smooth Certificate + Frullani-Centered Sieve + Gabor Pinching (`TTPC` + `IGP`)
- **Unconditionally proved in Lean (`ParitySensitiveRamanujanStabilizerTransfer.lean:1643`, `zeta_primeCoalescent_certificate_simple_and_offLineMultiple`)**:
  For every $0 < \eta < 1/3$ and $\varepsilon > 0$, there exists a smooth window profile $u$ such that for all large $T$:
  $$\left(\frac{29}{36} - \varepsilon\right) N(T, 2T) - \mathrm{primeCoalescentSurplus}(u,\eta,T) + M_{\mathrm{off}}(T, 2T) \le N_0^{\mathrm{s}}(T, 2T).$$
- **Exact Slack Arithmetic**:
  - Since $\frac{29}{36} - \frac{3}{4} = \frac{1}{18} \approx 5.56\%$, we have a **positive $+\frac{1}{18} N(T,2T)$ error budget** before dropping below $75\%$ *simple* critical zeros!
  - Furthermore, `oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy` splits the odd-prime even-shift sum into the parity-locked $Q$-modulus Ramanujan stabilizer model—whose Hardy–Littlewood / Ward–Mertens contribution is **strictly negative**, equal to $-\frac{1}{144} N(T,2T)$ (`calibration_five_models_four_thirds`), raising total slack above the true HL value to $\frac{1}{18} + \frac{1}{144} = \frac{1}{16} = 6.25\%$—plus the zero-mean `stabilizerDiscrepancyOddCoalSum`.
- **The Exact Factor-$2$ Sieve Discovery (`CoalescentSieveAnatomyAndModelCalibration.lean:540` & `NarrowStripClosePairEnergyAndExchangeRate.lean:90`)**:
  - Why did naive upper sieves fail? Putting absolute values around the dyadic kernel $f_{\mathrm{dyadic}}(u) = \frac{\sin 2u - \sin u}{u}$ *before* sieving (`affineTransModel (1+Υ) 1`) destroys Frullani cancellation $\int_0^\infty \frac{\sin 2u - \sin u}{u}\,du = 0$ of the Poisson main term, giving surplus $\frac{\Upsilon}{16} \le \frac{1}{18} \iff \Upsilon \le \frac{8}{9} < 1$ (impossible).
  - By contrast, when Frullani cancellation of the Poisson main term is **retained first** (`affineTransModel Υ 0`, or narrow-strip Cesàro energy $\mathrm{narrowStripCesaroEnergy}(F,\delta) \le B$ at $\lambda = 1 + \delta$), the condition $2 - \mathrm{frobeniusFormFactor}(F, 1+\delta) \ge \frac{3}{4}$ reduces to
    $$(12B - 15)\delta^2 - 6\delta + 1 \le 0, \qquad \Delta = 48(2 - B).$$
    At $\delta = 1/3$ ($\lambda = 4/3$), the surplus is $\frac{9\Upsilon - 10}{144} \le \frac{1}{18} \iff \mathbf{\Upsilon \le 2}$ (**$B = 2$ gives $(3\delta - 1)^2 \le 0$, hitting $75.00\%$ on the nose at $\lambda = 4/3$!**).
  - **The Clincher (Crossing $75\%$ Strictly Above the Factor-$2$ Parity Ceiling)**: $\Upsilon = 2$ is the exact linear-sieve parity factor! Adding **any strictly positive unconditional zero-side Gabor pinching slack $\delta_{\mathrm{pinch}} > 0$** on the bandwidth-$4/3$ Gram matrix (generalizing `IGP`'s unconditional $2\operatorname{Re}\langle v_x, v_y\rangle^2$ extraction from $\lambda = 1$ to $\lambda = 4/3$) shifts the budget from $\frac{1}{18}$ to $\frac{1}{18} + \delta_{\mathrm{pinch}}$, relaxing the required spectral-sieve factor to
    $$\Upsilon \le 2 + 16\,\delta_{\mathrm{pinch}} > 2.$$
    Moreover, one can also tune $\lambda \in (\frac{15-\sqrt{33}}{8}, \frac{4}{3}]$ (since $2 - (\frac{1}{\lambda} + \frac{\lambda}{3}) \ge \frac{3}{4}$ already for $\lambda \ge \frac{15-\sqrt{33}}{8} \approx 1.1569$, e.g. $\lambda = 6/5$ where $X = T^{6/5}$ is much shorter and the diagonal core is $\frac{23}{30} = 76.67\%$).

### 4.2 Route 4.2: Hedenmalm Critical-Feature (HCF) 7-Center Finite Source Majorant (`RHTower/Hedenmalm`)
- **Unconditionally proved in Lean**:
  - `criticalFeaturePhaseCovariance_four_pi_complement_upper_iff_criticalLine_lower` + `criticalFeatureSourcePhaseCorrectedBudget_fourPiThirds_upper`: The unconditional `Zeta23` ceiling on the HCF phase covariance is $\frac{4\pi}{3} N(n)$ (certifying $2/3$); saving **$\frac{\pi}{3}$** ($B_{\mathrm{HCF}}(n) \le (\pi + o(1))N(n)$) is **equivalent** to $N_0(n) \ge (\frac{3}{4} - o(1))N(n)$.
  - `criticalFeatureCanonicalCriticalLineCount_threeQuarters_lower_of_regularPhaseSourcePieceMajorant_sevenCenter` (`HedenmalmCriticalFeatureSevenTenthsSevenCenterFiniteSourceReceiver.lean:109`) already eliminates deep off-line zeros ($> 0.7$-band) unconditionally via Selberg's exponential near-line zero-density estimate (`SCPE`), reducing $\ge 75\%$ critical-line zeros to a **single finite, phase-preserving pole-Gamma source-piece majorant** below $\frac{1}{8}\mathrm{criticalFeatureShallowReflectedSevenCenterCharge} \approx 1.3082$.

### 4.3 Route 4.3 (Zero Trans-$\sqrt{x}$ Prime Input): Sub-Threshold ($\lambda \to 1^-$) Spectral Slack & Two-Grid De-Locking (`ACS` + `IGP` + `SCPE`)
- **Unconditionally proved in Lean (`BreakingTheCoalescenceBlindSpotAndThreeQuarters.lean:321`, `ProjectedDisplacementPaysNegativePartCredit.lean:197`)**:
  Below the $\sqrt{x}$ barrier ($\lambda \to 1^-$, so prime sums are **100% unconditional** with zero sieve input!),
  $$\bigl(H(\lambda) - \varepsilon\bigr) N + \mathrm{zeroSideSlack} \le N_0^*, \qquad \mathrm{zeroSideSlack} = 2\operatorname{tr} Q_- + \mathrm{posSlack} + \mathrm{onSlack}.$$
  Certifying $\ge 75\%$ requires only $\mathrm{zeroSideSlack} \ge \frac{1}{12} N$ (or $\approx 0.0775 N$ over `HD(1)`).
- **Why the $2/3$ blind spot can be broken**: The $2/3$ barrier occurs *only* if off-line pairs coalesce vertically onto the critical line (paying `projectedDisplacementEnergy` whenever they do not!) *and* critical double zeros lock onto exact half-grid ordinates (otherwise double zeros pay $\frac{1}{6}N > \frac{1}{12}N$ in `onSlack`!). Averaging the certificate across **two incommensurable/shifted sampling grids** forbids simultaneous half-grid locking of double zeros, while `SCPE` (`exists_shallow_zetaZeros_sq_multiplicity_and_closePairs_le`) bounds shallow multiplicity and close-pair clustering linearly in $T\log T$. (Alternatively, `HigherInertiaCertifiesSixteenTwentyFirsts.lean` proves the quartic polynomial $q_\star$ certifies **$16/21 \approx 76.19\%$** whenever fourth-moment kurtosis satisfies $\kappa_4 \le \frac{2503}{768} \approx 3.259$, vs $13/4 = 3.25$ for GUE.)

---

## 5. The 3 Highest-Leverage Open Questions for Breakthrough Progress

To maximize concrete, formalizable breakthroughs—achieving $\ge 75\%$ critical-line zeros and improved Quasi-RH along the path to full RH—research should concentrate on **three exact mathematical questions**:

### Priority 1: Signed Frullani-Centered Prime-Pair Discrepancy + Gabor Pinching at $\lambda \in [6/5, 4/3]$
> **Question 1**: *Can we combine unconditional zero-side Gabor pinching slack $\delta_{\mathrm{pinch}} > 0$ (`IGP`) at bandwidth $\lambda \in [6/5, 4/3]$ with a Frullani-preserving bilinear/dispersion upper bound on `stabilizerDiscrepancyOddCoalSum` (`TTPC`) corresponding to effective spectral-sieve constant $\Upsilon \le 2 + 16\,\delta_{\mathrm{pinch}}$?*

- **Why #1**: Every surrounding bridge (`SmoothWeightedCertificateAtFourThirds`, `ParitySensitiveRamanujanStabilizerTransfer`, `CoalescentSieveAnatomyAndModelCalibration`) is **already formalized in Lean**. Because $\Upsilon = 2$ is the exact parity threshold where $75\%$ holds with zero zero-side slack, extracting explicit `IGP` off-diagonal Gram slack at $\lambda = 4/3$ pushes the required prime-pair upper bound *above* the factor-$2$ parity barrier, making $\ge 75\%$ *simple* critical-line zeros achievable by bilinear dispersion without solving the twin-prime parity problem.

### Priority 2: Moving-Conductor Cyclotomic Near-Band ($K \le \sqrt{N}$) & Subfield-Line Shift Dispersion ($\nu < 1/6$)
> **Question 2**: *(a) For $\zeta(s)$, prove nontrivial cancellation $\mathrm{chebyshevCyclotomicNear}(N, K) = O_\varepsilon(N^{r+\varepsilon})$ on the $\le 2K$ near-constant cyclotomic modes of $\psi(n)-n$ of primitive conductor $m \ge (N+1)/K$ at $K = N^{1/3}$ ($r = 5/3 \implies 5/6$ Quasi-RH) and $K = \sqrt{N}$ ($r = 3/2 \implies 3/4$ Quasi-RH). (b) For general $L(s,\chi)$, bound $\mathbb{F}_r$-affine-line occupancy (`QuasiRHSubfieldProjection`) of prime-detector shift sets to drive $\nu < 1/6$ toward $0$ ($23/27$ Quasi-RH).*

- **Why #2**: Directly delivers improved Quasi-RH beyond $7/8$ (`CAF` already proved $\mathrm{Far} \le 288 N\sqrt{N+1}$ unconditionally!), operates entirely **before** the $3/4$ gauge-invariance wall (`AGT`), and—by `riemannHypothesis_iff_jasDressedPSD_one_and_quasi`—any unconditional Quasi-RH for $\zeta(s)$ immediately kills off-line `JAS` chain escape in the full RH programme.

### Priority 3: Pre-Norm Coherent-Pole Cancellation (`2·Pole + Γ - NR - P_Q`) & Four-Prime Coupling on $\langle 2,3\rangle \times \langle 5,7\rangle$
> **Question 3**: *Can the rank-1 coherent prime mode $P_Q(a)$ (`CSAR`) and non-ratio successor shell $\mathrm{NR}$ (`SSh`) be cancelled **before taking norms** against $2\cdot\mathrm{Pole} + \Gamma$ in the two-seam Schur complement at the `steklovDCProfile` edge $c_N = K L(\log L)^2$—or equivalently, can coprime CRT incidence bound $C_{\mathrm{ratCorr}}(u,v)$ uniformly on $\langle 2,3\rangle \times \langle 5,7\rangle$ (`ACoT`)?*

- **Why #3**: This is the exact core of full RH. By `CAF` (`eventually_exceptionalConductors_above_polylog_empty`) + `TMWP` (`steklovDCProfile`), individual conductors in $[(\log N)^\varepsilon, N^\theta]$ are *already* strictly positive at an RH-complete schedule; and by `CSAR` + `SSh`, both `P_Q(a)` and `NR` collapse once paired with the pole *prior* to Cauchy–Schwarz. Solving pre-norm cancellation on the coherent prime channel destroys `U-Σ` and `U-Π` simultaneously.

---

## 6. Blueprint for a New Field of Mathematics: *Biarithmetic Hodge–Coupling Theory*

Interpreting `U-Σ`, `U-Π`, and `U-Γ` as questions for which existing mathematics lacks native tools reveals **why** classical disciplines stall—and defines the exact structure of the missing field.

### 6.1 Why Existing Fields Cannot Supply the Tools
1. **Algebraic & Arakelov Geometry** prove Weil's RH for curves via the ring of correspondences $\mathbb{Z}[\mathrm{Frob}_q]$ and the Castelnuovo–Severi inequality on $C \times C$. Over $\mathbb{Z}$, `AGT` (`approxRingEndomorphism_classification`) proves no nontrivial completely multiplicative map has bounded additive defect, and `ACS` (`heckeCorrespondence_no_square_relation`) proves Hecke correspondences form a boost monoid with no conformal square relation, while the Golden fake curve ($q=5$) satisfies integrality, functional equation, Witt integrality, and Adams laws yet violates RH.
2. **Classical Analytic Number Theory** splits explicit formulas into diagonal main terms plus error terms and applies triangle/Cauchy–Schwarz/large-sieve norms. By `AGT` (`threeQuarters_le_of_gaugeInvariant_bound`), phase-blind norms stall at $3/4$; by `CSAR` (`PrimeGeneratorOrthogonalRows`) and `SSh`, taking norms *before* cancelling the rank-1 coherent prime mode $P_Q(a)$ and shell $\mathrm{NR}$ against the pole creates artificial $\log Q$ and $c^{16}$ divergences.
3. **Functional Analysis & Krein Operator Theory** preserve finite negative indices under norm-convergent limits, but over $\mathbb{Q}$ hit the Kakutani $0 \to \infty$ local index jump at $s = 1/2$ (`AKG`: `negIndex_localHecke`), affine subgroup index blowup $\kappa(1_{\mathbb{Z}}) = \infty$ (`AKG`), and holomorphic calibration rigidity (`HEF`: `eq_weilWeight_of_calibrated`).

### 6.2 Definition of the Field: *Biarithmetic Hodge–Coupling Theory*
**Core Thesis**: *The mathematics of renormalized indefinite intersection forms, pre-norm rank-one coherent couplings, and integer topological indices on rings where addition and multiplication interact without a Frobenius endomorphism.*

#### 1. Fundamental Questions of the Field
1. **Degenerating Edge Index Persistence (`U-Σ`)**: When a family of indefinite Hermitian forms $W_{c_N,N}$ on $v_1^\perp$ degenerates along a critical curve $\tau(c_N)\log N \asymp 1$ where bulk modes grow ($\sim \log m$) while head floors shrink ($\sim (\log N)^{-1}$), what algebraic/homotopical structure prevents spectral zero-crossings (`EHT`: `eventually_not_exists_crossingFree_path_of_not_rh`)?
2. **Pre-Norm Sum–Product Cancellation (`U-Π`)**: How do we compute Schur complements and relative quadratic forms **modulo rank-one coherent channels** ($P_Q(a)$, $2\cdot\mathrm{Pole} - \mathrm{NR}$, $S_Q - S_P$) so cancelling infinite-energy pole components are quotiented out *algebraically before Hilbert-space completion*?
3. **Biarithmetic Rigidity & Source Selection (`U-Γ`)**: What minimal algebraic compatibility between unipotent successor ($n \mapsto n+1$), hyperbolic prime boosts ($n \mapsto pn$), and two-place $(\infty, 2)$ gluing uniquely rigidifies $\mathbb{Z}$ against Beurling, Golden, Liouville, and sparse prime-flip deformations?
4. **Frobenius-at-Infinity Realization**: What arithmetic correspondence on finite integer-theta / divisor-jet modules intertwines the positive collided pairing $D(f) = \sum m_\rho |\hat f(\rho)|^2$ (`CDG`) with Hecke translations ($E(f,L) = 0$)?

#### 2. Point of View / Methodology
- **Identities before norms**: Never separate a renormalized difference ($C_K(u,v)$, $2\cdot\mathrm{Pole} - \mathrm{NR}$, $G F_a - P_Q(a)$, $S_Q - S_P$) into divergent summands bounded by $|\cdot|$. Treat coupled differences as primitive morphisms in a relative category.
- **Integer indices over real estimates**: Replace fragile $o(1)$ floor estimates by **quantized even topological invariants** ($\kappa \in 2\mathbb{N}$, collision Fredholm index $O \in 2\mathbb{N}$) that cannot change without an explicit discrete obstruction (`CDG`, `EHT`, `AKG`).
- **Two-tower / two-place reciprocity**: Replace global infinite-prime limits by finite generator presentations ($\langle 2,3\rangle \times \langle 5,7\rangle$ in `ACoT`; $\{2,3\}$ escape confinement in `ADR`; $(\infty, 2)$ Krein state equality in `AKG`).

#### 3. Primary Mathematical Objects
- **Coprime Coupling Bialgebras**: Double-difference kernels $C_K : G_1 \times G_2 \to \mathbb{C}$ on coprime finitely generated multiplicative lattices embedded in an additive successor ambient ($\mathbb{Z}$).
- **Coherent-Quotient Schur Bundles**: Triples $(\mathcal{H}_N, W_N, \mathcal{C}_N)$ where $\mathcal{C}_N = \operatorname{span}(v_1, P_Q, \text{shell partner})$ is a finite-rank pole-coherent subspace paired nondegenerately before norm completion on $\mathcal{H}_N / \mathcal{C}_N$.
- **Edge-Hodge Degenerations**: One-parameter resolution families over scaling horizons $(N, c_N)$ equipped with graded Ramanujan conductor filtrations $V_{M_1} \subset V_{M_2} \subset \mathcal{H}_N$ and divisor-jet connections $J_m(n) = \sum_{d\mid(m,n)} \mu(m/d)\,d\log d$.
- **Collided Fredholm Modules**: Finite integer-theta Wiener–Hopf operators (`CDG`) whose topological winding/Fredholm index computes horizontal spectral multiplicity defects $O \in 2\mathbb{N}$.

#### 4. Formal Language
- **Krein–Langer–Haynsworth Survival Calculus**: Exact inertia laws $\kappa(W) = \kappa(W|_A) + \kappa(W / A)$ on Pontryagin completions (`HKT`, `AID`, `RBG` survival cones).
- **Non-Abelian Affine / Baumslag–Solitar Correspondence Rings**: Modules over $\mathrm{Aff}^+(\mathbb{Q})$ and $\mathrm{BS}(1, p) = \langle a, t \mid t a t^{-1} = a^p\rangle$ (`RBG` cell dilation `cellDilate_two`, covariant *only* at the Euler gauge).
- **Cyclotomic & Mertens Incidence Cohomology**: Cyclotomic different/discriminant weights $\mathrm{tameDifferent}(m) = \log m - \sum_{p\mid m}\frac{\log p}{p-1}$ (`AIT`, `CSAR`) and Mertens nondivisibility forms $J_N(F)$ (`ACoT`).

#### 5. Foundational Principles
1. **Conservation of Negative Squares Across Places**: Gluing a product-formula correlation kernel at any place $v \in \{\infty, 2, 3, \dots\}$ yields the identical Pontryagin index $\kappa + 1$ (`AKG`).
2. **Coherent Rank-One Concentration**: All logarithmic divergence of prime incidence on $v_1^\perp$ concentrates in a rank-one scalar mode $P_Q(a)$, leaving an $\ell^2$-orthogonal residual bounded by $\frac{\log 2}{2} L_Q(a)$ (`CSAR`).
3. **Parity & Index Quantization**: Off-line/multiplicity defects are quantized in $2\mathbb{N}$ ($\kappa \in 2\mathbb{N}$, $O \in 2\mathbb{N}$); proving an open inequality $< 2$ proves exact vanishing $= 0$ (`HEF`, `CDG`).
4. **Nonlinear Dyadic Amplification**: Subexponential control of collided Hecke defect $E(2^k L)$ at one high scale forces $E \equiv 0$ across all scales via $E(L)^2 \le D(E(2L) - 4E(L))$ (`RBG`).
5. **Non-Gauge-Invariance Law**: Any theorem crossing $\Theta = 3/4$ must explicitly break prime-phase torus invariance via additive $\mathbb{Z}$-successor incidence (`AGT`).

#### 6. Mandatory Admissibility Criteria (Falsifiability Filter)
Every candidate definition, invariant, or theorem in *Biarithmetic Hodge–Coupling Theory* must pass five tests:
1. **Curve Calibration**: Specializes over $\mathbb{F}_q[T]$ to a clean, uniform proof of Weil's theorem without invoking $\mathrm{Frob}_q$ polynomial relations unavailable over $\mathbb{Z}$ (`EHT`, `ACompT`).
2. **Full Fake-Source Rejection**: Provably fails on (i) the Golden fake curve ($q=5$), (ii) tempered Beurling systems without integer gaps, (iii) Liouville / real-gauge twists ($\lambda$), and (iv) sparse single-prime flips $\omega_p$ for $p \ge 11$ (which pass the $2\log 2$ gap test!).
3. **Edge Validity**: Remains non-vacuous at $\tau(c_N)\log N \asymp 1$ (no superpolynomial floor divided by polynomial error).
4. **Exponent Losslessness**: Transfers bounds between arithmetic couplings and spectral zero widths with zero Baker/Diophantine exponent degradation (`ACoT`).
5. **$k$-Independent Amplification**: Any high-order amplification uses an exact algebraic/Fredholm identity rather than orthogonal moment expansion (`ART`).

#### 7. Concrete Research Topics of the New Field
1. **Relative Haynsworth Calculus for Coherent-Pole Triples**: General theory of finite-horizon indefinite forms whose ground-state pole, shell partner, and rank-1 coherent prime functional cancel inside a low-rank boundary block.
2. **Four-Prime CRT Incidence Discrepancy Theory**: Sharp additive-multiplicative correlation bounds for double differences across coprime rank-2 semigroups $\langle 2,3\rangle \times \langle 5,7\rangle$ in $\mathbb{Z} \cap [1, N]$.
3. **Moving-Conductor Cyclotomic & Subfield Dispersion**: Bilinear cancellation for long-wavelength cyclotomic components ($m \ge \sqrt{N}$) of arithmetic functions and non-concentration of rational shift sets on finite-field subcosets.
4. **Baumslag–Solitar Gauge Cohomology**: Cohomological obstructions to gauge-twisting $\mathrm{BS}(1,2) \cup \mathrm{BS}(1,3)$ modules, turning `RBG`'s Liouville defect (`hsDefect >= 2J`) into a uniform selector against remote prime flips $p \to \infty$.
5. **Discrete Fredholm Index Theory of Truncated Theta Flows**: Direct source-side winding bounds $< 2$ for `CDG`'s `integerThetaCollisionOperator` at logarithmic stopping horizons.
6. **Two-Place $(\infty, 2)$ Pontryagin Transport**: Explicit intertwining operators between the ultrametric $2$-adic glued state $\phi^{(2)}$ and the archimedean edge family $W_{\phi,c_N,N}$.
