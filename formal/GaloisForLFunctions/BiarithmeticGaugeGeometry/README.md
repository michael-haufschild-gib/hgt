# Biarithmetic Gauge Geometry (BGG)

**One question.** Every multiplicative operator on $\mathbb{N}_{\ge 1}$ — every diagonal horizon weight,
ratio shift $n \mapsto m n$, prime Hecke tower, and product crossing kernel — is unitarily intertwined
across the infinite prime gauge torus $\Omega_{\mathcal{P}} = \prod_p S^1$: it cannot tell the Euler
vacuum $\mathbf{1}$ ($\zeta(s)$) from the Liouville vacuum $\boldsymbol{-1}$ ($\lambda(n) = (-1)^{\Omega(n)}$,
$\zeta(2s)/\zeta(s)$) or a vertical Kronecker shift $\omega_\gamma(p) = p^{i\gamma}$. Conversely,
every completed Bochner–Hadamard positive system on the continuous half-line $\mathbb{R}_{>0}$ admits
rational pole-zero surgeries that exit the discrete integer log-lattice $\{\log n : n \ge 1\}$. What
non-commuting $(+1, \times p)$ gauge geometry breaks unitary prime-torus symmetry **selectively at the
Euler vacuum**, survives continuous Hadamard deformations in higher degree, eliminates discrete
lattice-truncation surplus on polar-neutral states, and rotates additive torsion without collapsing
onto the Poisson pole mode?

Biarithmetic Gauge Geometry is the gauge theory of the **ax + b arithmetic semigroup** acting simultaneously
on the prime torus $\Omega_{\mathcal{P}}$, the logarithmic continuum cell partition
$I_n = [\log n, \log(n+1))$, the degree-$4$ height-coupled Bochner–Hadamard class, and primitive
rational-torsion fibres $(\mathbb{Z}/q\mathbb{Z})^\times$. Its basic invariant is the **successor
gauge connection** $A_\omega(n) = \overline{\chi_\omega(n)}\,\chi_\omega(n+1)$, whose holonomy across
multiplicative shortcuts $n \mapsto p n$ measures the failure of $+1$ and $\times p$ to commute at
gauge $\omega$. Its guiding sentence:

> *Multiplicative scaling alone is gauge-blind on $\Omega_{\mathcal{P}}$, and continuous Bochner
> positivity alone is chirally soft on $\operatorname{Re} s = \tfrac{1}{2}$; arithmetic rigidity lives
> in the non-abelian holonomy between additive successor transport $+1$, discrete integer log-cells,
> and multiplicative prime scaling $\times p$.*

Its basic principle:

> *Every multiplicative positivity law must be paired with an explicit gauge-fixing connection —
> Catalan successor holonomy on $\Omega_{\mathcal{P}}$, discrete $O(2^{-\sigma})$ log-lattice support
> in Hadamard space, polar-neutral continuum cell subdivision on $[0, \infty)$, or fixed-point-free
> rational-torsion rotation on $(\mathbb{Z}/q\mathbb{Z})^\times$ — and every broken two-sided
> symmetry must be replaced by its exact chiral survivor.*

Namespace `GaloisForLFunctions.BiarithmeticGaugeGeometry`; umbrella `BiarithmeticGaugeGeometry.lean`.
Everything is unconditional; `RiemannHypothesis` appears only as the conclusion of explicit structural
criteria or inside equivalences.

---

## 1. Place in the research

Across the corpus, purely multiplicative spectral-positivity routes, continuum Bochner–Weil forcing
routes, discrete log-lattice Toeplitz routes, and monomial rank-$2$ theta routes each terminate at a
sharp structural obstruction:

1. **Unitary gauge blindness on $\mathbb{N}_{\ge 1}$:** Prime Hecke towers see only the
   multiplicative semigroup. Twisting a test vector by $\chi_\omega(n)$ unitarily identifies $\zeta$
   with Liouville's $\zeta(2s)/\zeta(s)$ (which has a dense barrier of poles on $\operatorname{Re} s = \tfrac{1}{2}$).
2. **Continuous Hadamard deformability in degree $4$:** In degree $1$ ($\kappa = 1, d = 1$),
   `CompletedPositiveSystem 1 1` collapses up to real scalars to $\zeta$ (`SBWF`). Lifting to the
   degree-$4$ height-coupled carrier $\zeta_\gamma(s) = \zeta(s)^2 \zeta(s+i\gamma)\zeta(s-i\gamma)$
   in `HeightCoupledSystem 2 1 1 γ` (`ACP`) contracts off-critical quartets at zero pole cost
   ($\Delta\kappa = 0$), raising the question of whether two-sided scalar rigidity (`CoupledRigid γ`)
   also holds in degree $4$. BGG proves unconditionally that **`CoupledRigid γ` is false** at
   infinitely many Hardy critical ordinates — and extracts the exact one-sided survivor
   `CentralVanishingCeiling γ` that accommodates critical-line splittings while still implying RH.
3. **Discrete lattice reflected-diagonal surplus:** Restricting the archimedean–polar
   crossing kernel $-k_{\mathrm{arch}}(-u, v)$ to diagonal nodes $u = v = \log n$ produces linear
   growth $\frac{(n-1)^2}{2n} - \frac{n^3}{n^4-1} > \frac{n}{6}$, swamping bounded prime combs, while
   naive $[1, X]$ lattice truncation breaks translation invariance. BGG proves that restoring
   off-diagonal crossing pairs $(a, b) \in [2, X]^2$ collapses the entire linear term into a **single
   rank-one polar square** that vanishes identically on polar-neutral states, while logarithmic cells
   $I_n = [\log n, \log(n+1))$ subdivide $\log m$-shifts with **zero boundary smearing**.
4. **Monomial $\mathbb{Z}^2$ theta diagonal collapse:** Separable monomial dilations
   $(m_1, m_2) \mapsto (q_1 m_1, q_2 m_2)$ factor into 1D marginals and fix zero torsion $(0, 0)$.
   BGG replaces zero torsion by primitive rational torsion $(\mathbb{Z}/q\mathbb{Z})^\times$, where
   dyadic scaling $u \mapsto 2u$ acts **without fixed points** for every odd $q \ge 3$ and the
   bi-torsion contrast $\Delta_{q_1, q_2}$ kills the $n = 0$ Poisson pole mode identically.

| Programme | Interface with BGG |
|---|---|
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md) | **Complementary twin.** AET studies real-valued *counting / effectivity functions* $h^0$ on polar surfaces, quadratic Riemann inequalities, Tate limits, and the Stepanov integrality floor; BGG studies *gauge connections, vacuum intertwiners, chiral Hadamard deformations, continuum log-cells, and torsion stabilizers*. Zero overlap of objects or declarations. |
| [StripBochnerWeilForcing](../StripBochnerWeilForcing/README.md) | Supplies `CompletedPositiveSystem`, `completedPositiveSystem_one_one_eq_zeta`, `polarSum`, and `real_anchor_of_posDef_polarSum`; BGG proves why scalar rigidity breaks in degree $4$ and proves the chiral failure of inward critical collapse. |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | Supplies `HeightCoupledSystem`, `coupledQuartetSymSquare`, and `contractComplexQuartet_heightCoupled`; BGG refutes `CoupledRigid γ`, proves `Θ(σ^{-3})` lattice escape of `coupledQuartetSymSquare`, and isolates `CentralVanishingCeiling γ`. |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Supplies `archPairKernel` and `archReflectedDiagWeight`; BGG proves rank-one polar collapse across $(a, b) \in [2, X]^2$ and exact cancellation of the linear diagonal on the polar-neutral hyperplane. |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md), [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Orbit Hodge index and scaling-surface geometry; BGG supplies the exact logarithmic cell-subdivision bridge between continuum Weil test functions and discrete arithmetic profiles. |
| [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | Prime gauge torus and Kronecker flows; BGG adds the unitary lattice intertwiner theorem, the successor connection $A_\omega$, Catalan $\{2, 3, 4\}$ holonomy reconstruction, and all-height Baker-free repulsion. |
| [ArithmeticPolarization](../ArithmeticPolarization/README.md) | Polarization laws and rectangular theta diagonal collapse; BGG supplies fixed-point-free dyadic torsion rotation and the pole-cancelled bi-torsion contrast $\Delta_{q_1, q_2}$. |
| [BiarithmeticGeometry](../BiarithmeticGeometry/README.md), [BezoutValuationIncidence](../BezoutValuationIncidence/README.md), [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md) | Box log-torsion, Bézout coprimality of consecutive integers, and signed successor dilation; BGG unifies them as curvature and remainder operators of $(+1, \times p)$. |
| [SquareRootThreshold](../SquareRootThreshold/README.md), [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Bi-scale envelopes and width bounds; BGG supplies the $m$-uniform disjoint-block biarithmetic Sobolev bound on Euclidean cell remainders. |

---

## 2. Motivation: Why Biarithmetic Gauge Geometry?

1. **Why multiplicative positivity alone can never isolate $\zeta$.**
   Let $\omega \in \Omega_{\mathcal{P}}$ assign a unit complex phase $\omega(p) \in S^1$ to each prime,
   extended completely multiplicatively to $\chi_\omega : \mathbb{N} \to \mathbb{C}$ ($\chi_\omega(0) = 0$).
   On $\ell^2(\mathbb{N}_{\ge 1})$, multiplication $(U_\omega \psi)(n) = \chi_\omega(n)\psi(n)$ is
   unitary, preserves every support cutoff $[1, X]$ and every diagonal weight $W_{\mathrm{diag}}(n)|\psi(n)|^2$,
   and intertwines every ratio shift $\overline{\psi(a)}\psi(am)$ with $\chi_\omega(m)\overline{\psi(a)}\psi(am)$.
   At real sign gauges $\omega(p) \in \{\pm 1\}$ — in particular the **Liouville vacuum**
   $\omega_{\boldsymbol{-1}}(p) = -1$, where $\chi_{\boldsymbol{-1}}(n) = \lambda(n)$ generates
   $\zeta(2s)/\zeta(s)$ — $U_\omega$ simultaneously intertwines product kernels $\chi_\omega(ab) q(a) q(b)$!
   Any proof architecture that discards $+1$ cannot distinguish an Euler product without poles on
   $\operatorname{Re} s = \tfrac{1}{2}$ from its Liouville twin with infinitely many poles on
   $\operatorname{Re} s = \tfrac{1}{2}$.

2. **Why Catalan $\{1, 2, 3, 4\}$ is the minimal gauge-fixing plaquette, and why height drift is bounded.**
   Along the additive successor graph $n \to n + 1$, $U_\omega$ ceases to be scalar: it induces the
   covariant connection $A_\omega(n) = \overline{\chi_\omega(n)}\chi_\omega(n+1)$. Flatness
   $A_\omega(n) = 1$ on $1 \le n \le N$ forces $\omega(p) = 1$ for all primes $p \le N + 1$. Already
   on $\{2, 3, 4 = 2^2\}$, the two links $A_\omega(2) = \overline{\omega(2)}\omega(3)$ and
   $A_\omega(3) = \overline{\omega(3)}\omega(2)^2$ reconstruct both $\omega(2) = A_\omega(2)A_\omega(3)$
   and $\omega(3) = A_\omega(2)^2 A_\omega(3)$ algebraically! A Kronecker vertical shift
   $\omega_\gamma(p) = p^{i\gamma}$ tries to mimic the Liouville vacuum when $2^{i\gamma} \approx -1$
   and $3^{i\gamma} \approx -1$ simultaneously. Elementary parity separation $2^a \ne 3^b$ (no Baker
   theory required) forces an explicit all-height repulsion floor
   $(1 + \cos(\gamma \log 2)) + (1 + \cos(\gamma \log 3)) \ge \tfrac{1}{50} e^{-|\gamma|}$.

3. **Why higher-degree Bochner–Hadamard forcing is chiral, not rigid.**
   In `HeightCoupledSystem 2 1 1 γ`, at any critical zero $\xi(\tfrac{1}{2} + i\gamma) = 0$ (infinitely
   many exist by Hardy's theorem), $\Lambda_\gamma(s) = (2\xi(s))^2(2\xi(s+i\gamma))(2\xi(s-i\gamma))$
   has a zero of order $\ge 2$ at $s = \tfrac{1}{2}$. Multiplying by the **outward critical-splitting
   multiplier** $W_\beta(s) = \frac{(s - 1/2)^2 + \beta^2}{(s - 1/2)^2}$ ($\beta \ne 0$) cancels the
   double pole at $\tfrac{1}{2}$, preserves entire order-$1$ structure and functional symmetry, and has
   nonnegative Bochner Laplace weight $2 e^{-(\sigma - 1/2)t}(1 - \cos(\beta t)) \ge 0$! Hence
   `CoupledRigid γ` is **unconditionally false**. Yet the inverse **inward critical collapse**
   $W_\beta^{-1}$ ($\Delta\operatorname{ord}_{1/2} = +2$) violates the Post–Widder real-anchor law and
   is **not** Bochner-positive, whereas off-critical quartet contraction increases central order by
   $\Delta\operatorname{ord}_{1/2} = +4$! Bochner positivity on the critical line is **one-way
   (outward-only)**: the true degree-$4$ invariant is the one-sided **Central Vanishing Ceiling**
   $\operatorname{ord}_{1/2}(\Lambda) \le \operatorname{ord}_{1/2}(\Lambda_\gamma)$. Moreover, both
   $W_\beta$ and `coupledQuartetSymSquare` decay algebraically like $\Theta(\sigma^{-3})$ as
   $\sigma \to +\infty$, escaping the exponential $O(2^{-\sigma})$ decay of any discrete Dirichlet
   log-lattice series.

4. **Why logarithmic continuum cells heal discrete lattice truncation.**
   Pointwise restriction to $\{\log n\}$ creates both the linear diagonal surplus $+(n-1)^2/(2n)$ and
   cutoff non-invariance. Across all pairs $(a, b) \in [2, X]^2$,
   $-k_{\mathrm{arch}}(-\log a, \log b) = \frac{(a-1)(b-1)}{2\sqrt{ab}} - \frac{(ab)^{3/2}}{(ab)^2 - 1}$:
   the linear growth is a **rank-one boundary-pole square** $\tfrac{1}{2}(\sum_{n=2}^X \frac{n-1}{\sqrt{n}} q_n)^2$
   that vanishes identically on the codimension-$1$ polar-neutral hyperplane! Meanwhile, replacing
   point masses at $\log n$ by step functions on logarithmic cells $I_n = [\log n, \log(n+1))$ of width
   $w_n = \log(n+1) - \log n$ turns $\log m$-translation into **exact Euclidean subdivision**
   $I_a + \log m = \bigsqcup_{r=0}^{m-1} I_{am+r}$ ($\sum_{r<m} w_{am+r} = w_a$), splitting every shift
   correlation into the $r = 0$ divisibility spine plus a Euclidean-remainder defect bounded
   **uniformly in $m$** by the biarithmetic Sobolev energy $\sum_k k(c_{k+1} - c_k)^2$.

---

## 3. Objects and Language

| Geometric / Gauge Concept | Biarithmetic Realization | Lean Declaration |
|---|---|---|
| Infinite prime gauge torus $\Omega_{\mathcal{P}} = \prod_p S^1$ | Unit-modulus prime phase assignment (`1` off primes) | `PrimeGauge` |
| Canonical gauge vacua ($\zeta$, $\lambda$, $\zeta(\cdot + i\gamma)$) | $\omega_{\mathbf{1}}(p)=1$, $\omega_{\boldsymbol{-1}}(p)=-1$, $\omega_\gamma(p)=p^{i\gamma}$ | `PrimeGauge.eulerGauge`, `PrimeGauge.liouvilleGauge`, `PrimeGauge.kroneckerGauge` |
| Completely multiplicative gauge character $\chi_\omega$ | Factorization lift $\prod_p \omega(p)^{v_p(n)}$ | `PrimeGauge.gaugeChar` |
| Unitary Hilbert intertwiner $U_\omega$ | Pointwise twist $(U_\omega \psi)(n) = \chi_\omega(n)\psi(n)$ | `gaugeTwist`, `twistedLatticeForm` |
| Discrete successor gauge connection $A_\omega$ | Parallel transport $\overline{\chi_\omega(n)}\chi_\omega(n+1)$ along $n \to n+1$ | `succConn` |
| Outward / inward critical multipliers $W_\beta, W_\beta^{-1}$ | $((s-1/2)^2+\beta^2)/(s-1/2)^2$ and its reciprocal | `criticalSplitMultiplier`, `inwardCollapseMultiplier` |
| Two-sided vs. chiral degree-$4$ rigidity | Scalar proportionality to $\zeta_\gamma$ vs. $\operatorname{ord}_{1/2}(\Lambda) \le \operatorname{ord}_{1/2}(\Lambda_\gamma)$ | `CoupledRigid`, `CentralVanishingCeiling` |
| Discrete Dirichlet log-lattice asymptotic class | Exponential real-axis decay $|G(\sigma)| \le C \cdot 2^{-\sigma}$ | `HasDirichletLatticeDecay` |
| Polar crossing amplitude & Lévy crossing kernel | $s(n) = (n-1)/\sqrt{n}$ and $(ab)^{3/2}/((ab)^2 - 1)$ | `polarCrossingAmplitude`, `archLevyProductWeight`, `fullArchCrossingForm` |
| Logarithmic continuum cell & shift correlation | $I_n = [\log n, \log(n+1))$, width $w_n = \log(n+1)-\log n$ | `logCellWidth`, `continuumCellShiftCorr`, `divisibleCellSpine`, `euclideanCellRemainder` |
| Biarithmetic Sobolev energy | Weighted discrete derivative $\sum_{k=1}^N k (c_{k+1} - c_k)^2$ | `cellL2NormSq`, `biarithmeticSobolevEnergy` |
| Rational-torsion rotation & Ramanujan kernel | $u \mapsto p u$ on $(\mathbb{Z}/q\mathbb{Z})^\times$ and $c_q(x) = \sum_{u \in (\mathbb{Z}/q\mathbb{Z})^\times} e(ux/q)$ | `torsionMulEquiv`, `ramanujanTorsionSum` |
| Pole-cancelled bi-torsion contrast | $\Delta_{q_1, q_2}(n) = \varphi(q_2)c_{q_1}(n) - \varphi(q_1)c_{q_2}(n)$ | `biTorsionContrast` |

**Terminology.**
- **Gauge-blind operator:** an operator on $\mathbb{N}_{\ge 1}$ unitarily intertwined by $U_\omega$ across all real sign gauges $\omega \in \{\pm 1\}^{\mathcal{P}}$ (hence unable to separate $\zeta$ from $\lambda$).
- **Catalan plaquette:** the consecutive quadruple $\{1, 2, 3, 4 = 2^2\}$, the unique minimal window where prime powers $2^2$ and $3^1$ meet at successor distance $1$.
- **Chiral Bochner surgery:** a meromorphic multiplier preserving `HeightCoupledSystem` in one sign of $\Delta\operatorname{ord}_{1/2}$ (`W_β`, outward, $\Delta\operatorname{ord}_{1/2} = -2$) whose inverse (`W_β⁻¹`, inward, $\Delta\operatorname{ord}_{1/2} = +2$) fails Bochner positivity.
- **Polar-neutral hyperplane:** the codimension-$1$ subspace $\sum_{n=2}^X \frac{n-1}{\sqrt{n}} q(n) = 0$ orthogonal to the boundary-pole crossing mode.
- **Stabilizer escape:** a coprime prime action $u \mapsto p u$ on primitive additive torsion $(\mathbb{Z}/q\mathbb{Z})^\times$ with zero fixed points.

---

## 4. Mechanisms

1. **Unitary Prime-Torus Intertwining vs. Catalan Holonomy Reconstruction (`PrimeGaugeTorusAndVacuumIntertwiners`).**
   `gaugeTwist` preserves every diagonal quadratic form (`diagForm_gaugeTwist_eq`) and intertwines
   multiplicative ratio shifts by $\chi_\omega(m)$ (`ratioShift_gaugeTwist_eq`). For real sign gauges
   (`IsRealSignGauge`), $\sigma_\omega(ab) = \sigma_\omega(a)\sigma_\omega(b)$ and $\sigma_\omega(n)^2 = 1$
   make combined diagonal + ratio + product quadratic forms unitarily equivalent to `eulerGauge`
   (`realSign_latticeForm_eq`, `nonneg_realSign_latticeForm_iff`). By contrast, flatness of
   `succConn ω` on $[1, N]$ characterizes $\omega(p) = 1$ for all primes $p \le N + 1$
   (`succConn_flat_iff_primes_eq_one`), and the two links `succConn ω 2`, `succConn ω 3` reconstruct
   $\omega(2)$ and $\omega(3)$ identically (`catalan_holonomy_two`, `catalan_holonomy_three`).

2. **Determinant Elimination & Baker-Free Diophantine Repulsion (`QuantitativeCatalanDiophantineRepulsion`).**
   Approximating $\cos(\gamma \log p) \approx -1$ selects odd integers $u_2, u_3$ with
   $1 + \cos(\gamma \log p) \ge \frac{2}{\pi^2}(\gamma \log p - u_p \pi)^2$ and
   $|u_p| \le \frac{|\gamma|\log p}{\pi} + 1$. Forming the cross-combination
   $(\log 3)\delta_2 - (\log 2)\delta_3 = \pi(u_3 \log 2 - u_2 \log 3)$ **eliminates $\gamma$
   identically**, reducing the joint cosine deficit to the integer gap $|2^{|u_3|} - 3^{|u_2|}| \ge 1$
   (`abs_odd_mul_log_two_sub_odd_mul_log_three_ge`). Since $\frac{\log 2 \cdot \log 3}{\pi} < \tfrac{1}{2}$,
   $2^{|u_3|} + 3^{|u_2|} \le 5 e^{|\gamma|/2}$, yielding the explicit all-height bound
   `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ (1/50) exp(−|γ|)` (`liouville_kronecker_repulsion_ge`).

3. **Chiral Bochner Splitting & Cubic Lattice-Decay Separation (`ChiralDeformationAndNonRigidityOfHeightCoupledSystems`).**
   On $\operatorname{Re} s = \sigma > \tfrac{1}{2}$, $\operatorname{Re}(-W_\beta'/W_\beta)(\sigma + iu)$
   is the Laplace–cosine transform of $2 e^{-(\sigma - 1/2)t}(1 - \cos(\beta t)) \ge 0$
   (`re_neg_logDeriv_criticalSplitMultiplier_eq`, `isEvenPosDef_criticalSplitMultiplier`). Iterating
   `dslope` twice at $s = \tfrac{1}{2}$ whenever $\xi(\tfrac{1}{2} + i\gamma) = 0$ constructs
   $(\zeta_\gamma \cdot W_\beta, \Lambda_\beta) \in \text{HeightCoupledSystem } 2\ 1\ 1\ \gamma$ with
   $\operatorname{ord}_{1/2}(\Lambda_\beta) = \operatorname{ord}_{1/2}(\Lambda_\gamma) - 2$, refuting
   `CoupledRigid γ` at unboundedly many Hardy ordinates (`exists_gt_not_coupledRigid`,
   `not_forall_coupledRigid`). Conversely, $W_\beta^{-1}$ is a $3$-point polar sum with real-anchor
   weight $-2 < +1$, failing `IsEvenPosDef` by `real_anchor_of_posDef_polarSum`
   (`not_isEvenPosDef_inwardCollapseMultiplier`). On the real ray $\sigma \to +\infty$, $\sigma^3$
   annihilates any $O(2^{-\sigma})$ Dirichlet log-lattice derivative (`tendsto_cube_mul_zero_of_dirichletLatticeDecay`)
   while converging to $2\beta^2 > 0$ on $W_\beta$ and $4b^2 + 4a^2 > 0$ on `coupledQuartetSymSquare`
   (`criticalSplit_escapes_dirichletLattice`, `coupledQuartet_escapes_dirichletLattice`).

4. **Polar-Neutral Rank-One Cancellation & Euclidean Cell Subdivision (`EuclideanCellRemainderAndPolarNeutralCollapse`).**
   Decomposing $-k_{\mathrm{arch}}(-\log a, \log b) = \frac{1}{2}s(a)s(b) - \frac{(ab)^{3/2}}{(ab)^2-1}$
   (`neg_archPairKernel_eq_polar_sub_levy`) collapses $\sum_{a,b \in [2,X]} (-k_{\mathrm{arch}}) q_a q_b$
   into $\frac{1}{2}(\sum s(n)q_n)^2 - \text{Lévy}$ (`fullArchCrossingForm_eq_polar_sq_sub_levy`),
   cancelling the linear diagonal $+(n-1)^2/(2n)$ identically when $\sum s(n)q_n = 0$
   (`reflectedDiag_add_offDiagPolar_eq_neg_levy`). On continuum logarithmic cells, telescoping gives
   $\sum_{r=0}^{m-1} w_{am+r} = w_a$ (`sum_logCellWidth_mul_add_eq`), factoring shift correlations
   without smearing (`continuumCellShiftCorr_eq_spine_add_remainder`). Disjointness of Euclidean blocks
   $\{am + j : 0 \le j < m\}$ across $a \ge 1$ bounds the remainder by Cauchy–Schwarz uniformly in $m$
   (`euclideanCellRemainder_sq_le`, `abs_euclideanCellRemainder_le_of_supported`).

5. **Fixed-Point-Free Torsion Rotation & Pole-Cancelled Bi-Torsion Contrast (`RamanujanTorsionStabilizersAndMonomialCollapse`).**
   Separable monomial dilations factor into 1D marginals (`monomial_theta_sum_factors`) and fix $(0,0)$.
   On $(\mathbb{Z}/q\mathbb{Z})^\times$, multiplication by coprime $p$ has zero fixed points whenever
   $(p : \mathbb{Z}/q\mathbb{Z}) - 1$ is a unit (`torsionMulEquiv_no_fixed_points_of_sub_one_isUnit`);
   at $p = 2$, $2 - 1 = 1$ is a unit in **every** odd modulus $q \ge 3$
   (`dyadic_torsion_rotation_fixed_point_free`). Summing over the unit orbit gives $c_q(x)$, which is
   coprime-dilation invariant (`ramanujanTorsionSum_coprime_mul`), mean-zero for $q \ge 2$
   (`sum_ramanujanTorsionSum_eq_zero`), and has Parseval energy $q\varphi(q)$
   (`sum_normSq_ramanujanTorsionSum`). Forming $\Delta_{q_1, q_2}(n) = \varphi(q_2)c_{q_1}(n) - \varphi(q_1)c_{q_2}(n)$
   annihilates $n = 0$ (`biTorsionContrast_zero`) while separating $1, q_1, q_2$ with opposite signs
   for distinct primes $q_1 \ne q_2$ (`biTorsionContrast_primes_values`).

---

## 5. Foundational Pillar Theorems

| Pillar | Mathematical Statement | Lean Theorem(s) |
|---|---|---|
| **G1 Prime-Torus Blindness vs. Catalan Rigidity** | Real sign-gauge lattice forms (diagonal + ratio + product) are unitarily equivalent to the Euler vacuum; `succConn` flatness on $[1,N]$ characterizes $\omega(p)=1$ ($\forall p \le N+1$); $\{2,3,4\}$ holonomy reconstructs $(\omega(2),\omega(3))$ and flips sign on $3 \to 4$ at Liouville. | `realSign_latticeForm_eq`, `nonneg_realSign_latticeForm_iff`, `succConn_flat_iff_primes_eq_one`, `catalan_holonomy_two`, `catalan_holonomy_three`, `succConn_liouville_three` |
| **G2 All-Height Catalan Diophantine Repulsion** | Parity gap $|u_3 \log 2 - u_2 \log 3| \ge (2^{|u_3|} + 3^{|u_2|})^{-1}$ for odd $u_2, u_3$ forces $(1+\cos(\gamma\log 2))+(1+\cos(\gamma\log 3)) \ge \frac{1}{50}e^{-|\gamma|}$ for all $\gamma \in \mathbb{R}$, and $|\gamma| \ge \log(1/(50\varepsilon))$ under $\varepsilon$-proximity. | `abs_odd_mul_log_two_sub_odd_mul_log_three_ge`, `liouville_kronecker_repulsion_ge`, `abs_height_ge_of_liouville_approx` |
| **G3 Disproof of `CoupledRigid` & Chiral Deformation Law** | Outward splitting $W_\beta$ is Bochner-positive and refutes `CoupledRigid γ` at unboundedly many Hardy ordinates; inward collapse $W_\beta^{-1}$ fails Bochner positivity; both $W_\beta$ and `coupledQuartetSymSquare` escape $O(2^{-\sigma})$ Dirichlet lattice decay via $\Theta(\sigma^{-3})$ asymptotics. | `isEvenPosDef_criticalSplitMultiplier`, `exists_criticalSplit_deformation_of_xi_zero`, `exists_gt_not_coupledRigid`, `not_forall_coupledRigid`, `not_isEvenPosDef_inwardCollapseMultiplier`, `criticalSplit_escapes_dirichletLattice`, `coupledQuartet_escapes_dirichletLattice` |
| **G4 Chiral Central Vanishing Ceiling** | The one-sided ceiling `CentralVanishingCeiling γ` ($\operatorname{ord}_{1/2}(\Lambda) \le \operatorname{ord}_{1/2}(\Lambda_\gamma)$) is strictly satisfied by every outward $W_\beta$ deformation ($\Delta\operatorname{ord}_{1/2} = -2$) yet excludes off-critical quartets ($\Delta\operatorname{ord}_{1/2} = +4$) and implies `RiemannHypothesis`. | `criticalSplit_strictly_below_centralCeiling`, `xi_ne_zero_of_centralVanishingCeiling`, `riemannHypothesis_of_forall_centralVanishingCeiling` |
| **G5 Polar-Neutral Rank-One Collapse & Cell Subdivision** | Restoring off-diagonal polar pairs cancels `archReflectedDiagWeight`'s linear growth on $\sum s(n)q_n = 0$; continuum cells $I_n = [\log n, \log(n+1))$ satisfy $\sum_{r<m} w_{am+r} = w_a$ and an $m$-uniform disjoint-block biarithmetic Sobolev remainder bound. | `fullArchCrossingForm_eq_polar_sq_sub_levy`, `reflectedDiag_add_offDiagPolar_eq_neg_levy`, `exists_nonzero_polarNeutral_profile`, `sum_logCellWidth_mul_add_eq`, `continuumCellShiftCorr_eq_spine_add_remainder`, `abs_euclideanCellRemainder_le_of_supported` |
| **G6 Torsion Stabilizer Escape & Bi-Torsion Contrast** | Separable monomial $\mathbb{Z}^2$ dilations collapse to 1D marginals; dyadic rotation $u \mapsto 2u$ on $(\mathbb{Z}/q\mathbb{Z})^\times$ is fixed-point-free for every odd $q \ge 3$; $\Delta_{q_1, q_2}$ kills the $n=0$ pole mode, is coprime-dilation invariant, and sign-separates $q_1 \mid n$ from $q_2 \mid n$. | `monomial_theta_sum_factors`, `dyadic_torsion_rotation_fixed_point_free`, `ramanujanTorsionSum_coprime_mul`, `sum_normSq_ramanujanTorsionSum`, `biTorsionContrast_zero`, `biTorsionContrast_primes_values` |
| **G7 Master Synthesis** | Unified unconditional conjunction of Pillars G1–G6. | `biarithmetic_gauge_geometry_master_theorem` |
| **G8 Lattice Real Anchor & Rational Classification** | A nonnegative Dirichlet lattice plus a finite polar sum with even positive-definite sections has nonnegative polar scale weight, and its rightmost weighted pole is real with dominant weight. Every nontrivial rational deformation `ζ_γ · ∏(s − zᵢ)^{mᵢ}` is anchored at `ξ(σ* + iγ) = 0`: rigid at every height whose line is `ξ`-zero-free (unconditionally at `γ = 0`), exact central descent otherwise; the rational ceiling at `γ ≠ 0` is equivalent to no off-critical zero at ordinate `γ`, and to RH at all heights. | `polarScaleWeight_nonneg_of_lattice_posDef`, `lattice_real_anchor`, `rationalDeformation_real_anchor`, `rationalDeformation_rigid_of_xi_ne_zero_on_line`, `rationalDeformation_central_descent`, `rationalCentralVanishingCeiling_iff`, `riemannHypothesis_iff_forall_rationalCentralVanishingCeiling` |
| **G9 Anchor-Line Positivity & Capacity** | On every vertical line bounding the weighted poles, the residue divisor of a positive exponential-cosine density is even positive definite; for rational deformations of lattice systems, `β ↦ −M(σ + iβ)` is positive definite. Consequences: in `HeightCoupledSystem 2 1 1 γ` without off-critical zeros at `γ`, each created upper-half critical zero costs two central orders (`W_β` extremal); in `CompletedPositiveSystem κ d`, rational deformations of `ζ^d` have boundary capacity `(κ − d)/2` (the capacity `κ/2` is never attained) and are trivial when `κ ≤ d`. | `lineResidue_isEvenPosDef`, `rationalDeformation_lineResidue_isEvenPosDef`, `analyticOrderAt_add_eq_of_eq_mul_rationalMultiplier`, `rationalDeformation_critical_conservation`, `rationalDeformation_zetaPow_boundary_capacity`, `rationalDeformation_zetaPow_rigid` |
| **G10 Off-Line Rigidity of Positive Prime-Mass Deformations** | If `−F'/F + ζ_γ'/ζ_γ` is the Laplace transform of any nonnegative measure, then — absent off-critical zeros at ordinate `γ` — `Λ` has exactly the zeros of `Λ_γ` off the critical line and no larger central order (Landau at the abscissa of the Lebesgue-thickened measure). The positive ceiling at `γ ≠ 0` is equivalent to no off-critical zero at `γ`, and to RH at all heights. | `positiveDeformation_orders_and_anchor`, `positiveDeformation_offLine_rigid`, `exists_positiveDeformation_above_ceiling`, `positiveCentralVanishingCeiling_iff`, `riemannHypothesis_iff_forall_positiveCentralVanishingCeiling` |
| **G11 Square-Root Deficit Law** | The rigidity survives a holomorphic perturbation on `Re s > σ_E`, `σ_E < 1/2`. Hence an arithmetic member `−F'/F = Σ b(n)n^{−s}` (`b ≥ 0`) of `HeightCoupledSystem 2 1 1 γ` that exceeds the central order of `ζ_γ` (without off-critical zeros at `γ`) must remove prime mass of at least square-root size: `Σ (b_γ(n) − b(n))⁺ n^{−s}` has abscissa `≥ 1/2`. | `perturbedDeformation_offLine_rigid`, `latticeMember_offLine_rigid_of_subcritical_deficit`, `centralExcess_forces_squareRoot_deficit` |
| **G12 Deficit–Excess Law** | At the threshold the deficit's Abelian residue bounds the excess: if `Σ d(n)n^{−s}` converges on `Re s > 1/2`, then `liminf_{σ↓1/2} (σ − ½) Σ d(n)n^{−σ} ≥ ord_{1/2} Λ − ord_{1/2} Λ_γ`. | `deficit_residue_ge_centralExcess` |
| **G13 Positive Coupled Rigidity** | Without off-critical zeros at `γ`, the critical jump `t ↦ ord_{½+it} Λ_γ − ord_{½+it} Λ` of a positive deformation is even positive definite (so bounded by the central drop), and a deformation with no central drop is `K ζ_γ`. Positive rigidity at `γ` ⟺ no zero of `ξ` on `Im s = γ`; RH ⟺ every positive deformation at every height is trivial or strictly lowers the centre. | `criticalJump_isEvenPosDef`, `positiveDeformation_trivial_of_central_le`, `positiveCoupledRigid_iff`, `riemannHypothesis_iff_forall_positiveChiral` |
| **G14 Strong Multiplicity One** | Without off-critical zeros at `γ`, an arithmetic member (`−F'/F = Σ b(n)n^{−s}`, `b ≥ 0`) whose deficit against `b_γ` converges on `Re s > ½` with zero Abel residue at `½` and which keeps the central order has `b = b_γ` and `F = K ζ_γ`; with G12 the Abel residue of the deficit is the exact invariant. Unconditional at zero-free ordinates. | `latticeMember_eq_of_negligible_deficit`, `latticeMember_eq_of_subcritical_deficit`, `not_tendsto_deficit_residue_of_ne`, `latticeMember_eq_of_xi_ne_zero_on_line` |
| **G15 Multi-Prime Repulsion** | For `N ≥ 2` distinct primes, `Σ_j (1 + cos(γ log p_j)) ≥ γ² e^{−2τL}/(32Nτ²)` with `τ = (N(|γ|L/π + 1))^{1/(N−1)}`, `L = Σ log p_j` (Siegel's lemma + unique factorization, Baker-free); for every `ε > 0` finitely many primes give `≥ exp(−|γ|^ε)` at large height. | `multiPrime_repulsion`, `exists_primes_repulsion_ge_exp_neg_rpow` |
| **G16 Landau–Wronskian Principle and ζ^d Rigidity** | Entire `Λ, Λ₀` with `Λ₀'/Λ₀ − Λ'/Λ = 𝓛ν + E` on a ray (`ν ≥ 0`) have the same divisor right of the abscissa, which, if positive, is a real zero of `Λ₀` of higher order. For `CompletedPositiveSystem κ d` with `κ ≤ d`: a positive excess over `ζ^d` forces `κ = d`, `F = K ζ^d`; an arithmetic member with deficit against `dΛ` of abscissa `< ½` has `b = dΛ`. Unconditional. | `landauWronskian_orders_and_anchor`, `zetaPowDeformation_trivial`, `latticeMember_eq_zetaPow` |
| **G17 Abel–Gram Law and Boundary Capacity** | Across any vertical line at or right of the abscissa, divisor jumps are Abel limits of `𝓛ν`, form an even positive-definite function, and are bounded by the real jump. Deformations of `ζ^d` (positive, or arithmetic with deficit abscissa `< 1`) carry at most `(κ − d)/2` boundary zeros; none when `κ ≤ d + 1`. | `jump_isEvenPosDef_of_rel`, `sum_jump_le_of_rel`, `zetaPowDeformation_boundary_capacity`, `latticeMember_ne_zero_on_boundary` |

---

## 6. Questions the Programme Aims to Answer

1. **How can an operator distinguish $\zeta(s)$ from its Liouville twin $\zeta(2s)/\zeta(s)$ and
   vertical shifts $\zeta(s+i\gamma)$ before appealing to strip holomorphy?**
   Never through multiplicative diagonal, ratio, or product kernels alone (G1), and locally on
   $\{1, 2, 3, 4\}$ through the successor connection $A_\omega(2), A_\omega(3)$, whose proximity to
   the Liouville vacuum along the Kronecker line costs $|\gamma| \ge \log(1/(50\varepsilon))$ (G2).
   Across $N$ primes the repulsion is stretched-exponential, $\exp(-c|\gamma|^{1/(N-1)})$, so finitely
   many primes beat every $\exp(-|\gamma|^\varepsilon)$ (G15).

2. **What replaces false scalar uniqueness (`CoupledRigid γ`) in higher-degree Bochner–Hadamard forcing?**
   Two-sided uniqueness fails because collided critical-line zeros can split *outward* via $W_\beta$
   ($\Delta\operatorname{ord}_{1/2} = -2$), whereas Bochner positivity forbids *inward* critical
   collapse ($\Delta\operatorname{ord}_{1/2} = +2$) while permitting *inward* contraction of
   off-critical quartets ($\Delta\operatorname{ord}_{1/2} = +4$) (G3). Thus the exact surviving target
   is the chiral one-sided ceiling `CentralVanishingCeiling γ` — or restricting the coupled class to
   discrete $O(2^{-\sigma})$ Dirichlet log-lattice support, which blocks rational Hadamard surgery
   altogether (G3, G4). On rational deformations the answer is exact (G8): two-sided rigidity holds at
   every height whose horizontal line carries no zero of $\xi$, outward descent is forced otherwise,
   and the ceiling at $\gamma \ne 0$ is equivalent to the absence of off-critical zeros at ordinate $\gamma$.
   The same holds for every deformation adding nonnegative prime mass (G10): a violator of the full
   ceiling must remove prime mass of at least square-root size (G11). On the positive sector two-sided
   rigidity holds exactly at the zero-free ordinates (G13): positive deformations are trivial or lower
   the central order, and pay for every critical zero they move from the centre.

3. **How do continuum translation-invariant Weil forms descend to discrete arithmetic profiles on
   $[1, X]$ without linear diagonal blowup or cutoff smearing?**
   By projecting onto the codimension-$1$ polar-neutral hyperplane $\sum_{n=2}^X \frac{n-1}{\sqrt{n}} q_n = 0$
   (which kills the rank-one polar square identically) and embedding discrete profiles as step
   functions on logarithmic cells $I_n = [\log n, \log(n+1))$, where $\log m$-shifts subdivide cleanly
   into the divisibility spine plus an $m$-uniform Sobolev remainder (G5).

4. **How can prime scaling act non-trivially on theta characteristics without re-introducing the
   $n = 0$ Poisson pole mode?**
   By working on primitive rational torsion $(\mathbb{Z}/q\mathbb{Z})^\times$ at odd moduli $q \ge 3$
   (where $u \mapsto 2u$ is fixed-point-free) and pairing two moduli in the pole-cancelled contrast
   $\Delta_{q_1, q_2}(n) = \varphi(q_2)c_{q_1}(n) - \varphi(q_1)c_{q_2}(n)$ (G6).

---

## 7. Traps

| Trap | Structural Truth |
|---|---|
| Adding a clever positive diagonal weight or product kernel on $[1, X]$ can separate $\zeta$ from $\lambda$ | Every real sign gauge $\omega \in \{\pm 1\}^{\mathcal{P}}$ intertwines diagonal + ratio + product forms unitarily (`nonneg_realSign_latticeForm_iff`, G1). |
| Since `CompletedPositiveSystem 1 1` is rigid up to scalars, `HeightCoupledSystem 2 1 1 γ` should also be scalar-rigid (`CoupledRigid γ`) | **False** at infinitely many Hardy critical zeros $\xi(\tfrac{1}{2}+i\gamma)=0$: outward critical splitting $W_\beta$ stays inside `HeightCoupledSystem 2 1 1 γ` (`not_forall_coupledRigid`, G3). |
| Since outward critical splitting $W_\beta$ is Bochner-positive, critical zeros can be moved freely in both directions along $\operatorname{Re} s = \tfrac{1}{2}$ | **False**: inward collapse $W_\beta^{-1}$ violates the Post–Widder real-anchor law and fails `IsEvenPosDef` (`not_isEvenPosDef_inwardCollapseMultiplier`, G3). |
| Rational quartet contractions preserve ordinary Dirichlet series structure on $\operatorname{Re} s > 1$ | **False**: every discrete Dirichlet log-lattice series has $O(2^{-\sigma})$ real-axis derivative decay ($\sigma^3 G(\sigma) \to 0$), whereas $W_\beta$ and `coupledQuartetSymSquare` decay as $\Theta(\sigma^{-3})$ (`coupledQuartet_escapes_dirichletLattice`, G3). |
| The linear growth of `archReflectedDiagWeight(n) ~ n/2` is an irreducible archimedean obstruction on $[2, X]$ | It is an artifact of discarding $a \ne b$ polar cross-terms: across $[2, X]^2$ the entire linear part is $\frac{1}{2}(\sum s(n)q_n)^2$, which vanishes identically on polar-neutral states (`reflectedDiag_add_offDiagPolar_eq_neg_levy`, G5). |
| Discretizing continuum shift correlations onto $[1, X]$ inevitably incurs $m$-growing boundary smearing | Logarithmic cells $I_n = [\log n, \log(n+1))$ satisfy $\sum_{r<m} w_{am+r} = w_a$ identically, with Euclidean remainder bounded **independently of $m$** by $\sqrt{\|c\|_{L^2(w)}^2 \cdot \mathcal{E}_{\mathrm{Sob}}(c)}$ (G5). |
| Monomial dilations $(q_1 m_1, q_2 m_2)$ on $\mathbb{Z}^2$ theta series generate genuine 2D arithmetic coupling | Separable weights factor into 1D marginals and fix zero torsion $(0,0)$ (`monomial_theta_sum_factors`, G6). |

---

## 8. Tools

**Imported from the corpus and Mathlib:**
- `CompletedPositiveSystem`, `polarSum`, `real_anchor_of_posDef_polarSum` (`StripBochnerWeilForcing`);
- `HeightCoupledSystem`, `coupledQuartetSymSquare`, `contractComplexQuartet_heightCoupled` (`ArithmeticCorrespondencePositivity`);
- `archPairKernel`, `archReflectedDiagWeight` (`ArithmeticOrientationTheory`);
- `RHTower.xi`, Hardy critical-line zeros (`completedPositiveSystem_one_critical_zeros`);
- `ZMod.stdAddChar`, `AddChar.sum_mulShift`, `ZMod.unitOfCoprime`, `ZMod.card_units_eq_totient` (`Mathlib`).

**Developed in BGG:**
- The prime-gauge intertwiner calculus (`PrimeGauge`, `gaugeTwist`, `twistedLatticeForm`, `succConn`) and algebraic Catalan $\{2, 3, 4\}$ holonomy formulas;
- Determinant-eliminated, Baker-free Diophantine cosine-repulsion bounds across all real heights;
- The chiral Bochner deformation machine (`criticalSplitMultiplier`, `inwardCollapseMultiplier`, `CentralVanishingCeiling`) and cubic $\sigma^3$ log-lattice asymptotics (`HasDirichletLatticeDecay`);
- Polar-neutral rank-one crossing decomposition and logarithmic continuum cell-subdivision / disjoint-block Sobolev calculus (`logCellWidth`, `continuumCellShiftCorr`, `biarithmeticSobolevEnergy`);
- Fixed-point-free torsion-unit equivalences (`torsionMulEquiv`) and pole-cancelled bi-torsion Ramanujan contrasts (`ramanujanTorsionSum`, `biTorsionContrast`).

**Tools targeted next:**
- Multi-prime Bézout holonomy plaquettes ($p^a - q^b = \pm 1, \pm 2$ and Pillai–Mihăilescu towers) tightening height repulsion from $e^{-|\gamma|}$ toward polynomial/sub-exponential decay in $|\gamma|$;
- Discrete log-lattice-preserving height-coupled positivity classes (`DirichletLatticeCoupledSystem`) combining `HeightCoupledSystem` with $O(2^{-\sigma})$ support rigidity;
- Continuum polar-neutral Sobolev test families optimizing the ratio $\mathcal{E}_{\mathrm{Sob}}(c) / \|c\|_{L^2(w)}^2$ on $[1, X]$ while keeping nonzero divisibility-spine correlation;
- Mellin–Poisson duality for $\Delta_{q_1, q_2}$-weighted theta kernels with zero $s = 1$ pole residue.

---

## 9. Open Research Topics

1. **Proving `CentralVanishingCeiling γ` from discrete Dirichlet log-lattice support.**
   Every known counterexample to two-sided `CoupledRigid γ` (`W_β`) decreases $\operatorname{ord}_{1/2}$
   and exits `HasDirichletLatticeDecay` via $\Theta(\sigma^{-3})$ decay, while off-critical quartet
   contractions increase $\operatorname{ord}_{1/2}$ by $+4$ and *also* exit `HasDirichletLatticeDecay`!
   Characterize which Hadamard multipliers preserve **both** `HeightCoupledSystem 2 1 1 γ` and discrete
   integer log-lattice support $\{\log n : n \ge 1\}$. The rational class is classified (G8); open:
   transcendental multipliers with infinitely many singularities, where the Landau anchor needs a
   lattice-sieve beyond finite polar sums.

2. **Polar-neutral Sobolev vs. divisibility-spine optimization on logarithmic cells.**
   On the codimension-$1$ hyperplane $\sum_{n=2}^X \frac{n-1}{\sqrt{n}} w_n c_n = 0$, the linear
   archimedean diagonal vanishes and the Euclidean cell remainder is bounded by
   $\|c\|_{L^2(w)} \cdot \mathcal{E}_{\mathrm{Sob}}(c)^{1/2}$ uniformly in $m$. Construct explicit
   polar-neutral profiles $c$ on $[1, X]$ whose prime divisibility spine $\sum_p \log p \sum_a w_a c_a c_{ap}$
   dominates $\mathcal{E}_{\mathrm{Sob}}(c)^{1/2}$.

3. **Multi-plaquette Diophantine holonomy on $\Omega_{\mathcal{P}}$.** Answered (G15): Siegel's lemma
   on the odd phase centres and unique factorization give $e^{-c|\gamma|^{1/(N-1)}}$ on $N$ primes.
   Open: polynomial repulsion $|\gamma|^{-C}$ (Baker strength) from a growing prime set.

4. **Non-separable bi-torsion theta operators on $\mathbb{Z}^2$.**
   Coupling $\Delta_{q_1, q_2}(m_1 + m_2)$ across diagonal sum-lines $m_1 + m_2 \equiv r \pmod{q_1 q_2}$
   so that prime dilations rotate $(\mathbb{Z}/q_i\mathbb{Z})^\times$ without fixed points while the
   $(0, 0)$ and axis Poisson poles cancel identically.

---

## 10. Success Criteria and Contribution Standards

Biarithmetic Gauge Geometry succeeds when it either (a) establishes `CentralVanishingCeiling γ` for
all $\gamma \ne 0$ (or on a height strip), (b) constructs a polar-neutral continuum-cell family whose
divisibility spine strictly dominates its biarithmetic Sobolev remainder and archimedean Lévy cost, or
(c) proves a sharp no-go theorem for a candidate gauge-fixing mechanism **together with its strongest
unconditional positive survivor**.

| Criterion | Required Test |
|---|---|
| **Prime-gauge selectivity** | Must state explicitly how the construction transforms under $U_\omega$ on $\Omega_{\mathcal{P}}$ and why it separates `eulerGauge` from `liouvilleGauge`. |
| **Chiral & lattice calibration** | Any statement on `HeightCoupledSystem` must be tested against outward critical splitting $W_\beta$ (must hold!) and off-critical quartet contraction (must obstruct!), and state whether it uses discrete $\{\log n\}$ support. |
| **Polar-neutral & cell exactness** | Any discrete $[1, X]$ inequality must account for off-diagonal polar cross-terms and Euclidean cell-subdivision remainders without unproved truncation approximations. |
| **Pole-mode & stabilizer test** | Any theta / torsion construction must vanish on the $n = 0$ pole mode and verify fixed-point-free prime action on its torsion support. |
| **Unconditional proof integrity** | Zero `sorry`, zero added axioms, zero hidden analytic hypotheses, zero `maxHeartbeats` overrides, zero `native_decide`. |

Every contribution to `GaloisForLFunctions/BiarithmeticGaugeGeometry/` must:
1. Be formalized as an unconditional Lean 4 module wired into `BiarithmeticGaugeGeometry.lean`;
2. Pair every negative / impossibility theorem with an explicit, formalized positive survivor (following
   the `not_forall_coupledRigid` $\to$ `CentralVanishingCeiling` and `archReflectedDiagWeight` $\to$
   `reflectedDiag_add_offDiagPolar_eq_neg_levy` paradigm);
3. Separate algebraic gauge identities (true across all $\omega \in \Omega_{\mathcal{P}}$ or all
   separable lattices) from gauge-breaking $(+1, \times p)$ holonomy estimates;
4. Maintain crisp, self-contained mathematical docstrings free of process notes.

---

## Module Architecture

- [`PrimeGaugeTorusAndVacuumIntertwiners.lean`](PrimeGaugeTorusAndVacuumIntertwiners.lean) — Infinite prime gauge torus $\Omega_{\mathcal{P}}$, Euler/Liouville/Kronecker vacua, unitary lattice intertwiners, successor connection `succConn`, flatness theorem, and Catalan $\{2, 3, 4\}$ holonomy reconstruction.
- [`QuantitativeCatalanDiophantineRepulsion.lean`](QuantitativeCatalanDiophantineRepulsion.lean) — Elementary logarithmic gap bounds, parity separation $2^a \ne 3^b$, determinant elimination of $\gamma$, and Baker-free all-height repulsion `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ (1/50) exp(−|γ|)`.
- [`ChiralDeformationAndNonRigidityOfHeightCoupledSystems.lean`](ChiralDeformationAndNonRigidityOfHeightCoupledSystems.lean) — Outward critical splitting $W_\beta$, unconditional disproof of `CoupledRigid γ` at unboundedly many Hardy ordinates, chiral failure of inward collapse $W_\beta^{-1}$, $O(2^{-\sigma})$ vs. $\Theta(\sigma^{-3})$ Dirichlet-lattice separation, and sufficiency of `CentralVanishingCeiling γ` for `RiemannHypothesis`.
- [`EuclideanCellRemainderAndPolarNeutralCollapse.lean`](EuclideanCellRemainderAndPolarNeutralCollapse.lean) — Rank-one polar collapse of `-archPairKernel` across $[2, X]^2$, cancellation of linear reflected-diagonal growth on the polar-neutral hyperplane, exact logarithmic cell subdivision $\sum_{r<m} w_{am+r} = w_a$, and $m$-uniform disjoint-block biarithmetic Sobolev remainder bounds.
- [`RamanujanTorsionStabilizersAndMonomialCollapse.lean`](RamanujanTorsionStabilizersAndMonomialCollapse.lean) — Marginal collapse of separable monomial $\mathbb{Z}^2$ theta sums, fixed-point-free dyadic torsion rotation on $(\mathbb{Z}/q\mathbb{Z})^\times$ for odd $q \ge 3$, Ramanujan torsion sums & Parseval energy $q\varphi(q)$, and pole-cancelled bi-torsion contrasts $\Delta_{q_1, q_2}$.
- [`MasterBiarithmeticGaugeGeometryTheorem.lean`](MasterBiarithmeticGaugeGeometryTheorem.lean) — Capstone module synthesizing Pillars G1–G6 into `biarithmetic_gauge_geometry_master_theorem`.
- [`LatticeSievedPostWidderAndLandauAnchor.lean`](LatticeSievedPostWidderAndLandauAnchor.lean) — Post–Widder annihilation of the logarithmic lattice, positivity of the polar scale weight, evenness ⇒ conjugation symmetry, and the Landau/lattice real anchor.
- [`RationalBochnerDeformationsOfTheHeightCoupledCarrier.lean`](RationalBochnerDeformationsOfTheHeightCoupledCarrier.lean) — Classification of rational deformations of `ζ_γ`, rational rigidity, exact chiral descent, and the rational ceiling ⟺ horizontal zero-free line ⟺ RH.
- [`AnchorLinePositivityAndCapacityOfRationalDeformations.lean`](AnchorLinePositivityAndCapacityOfRationalDeformations.lean) — Positive definiteness of line-residue divisors, the local order law, critical-zero conservation in `HeightCoupledSystem`, and the sharp boundary capacity of rational deformations of `ζ^d` in `CompletedPositiveSystem`.
- [`PositivePrimeMassDeformationsAreRigidOffTheCriticalLine.lean`](PositivePrimeMassDeformationsAreRigidOffTheCriticalLine.lean) — Off-line rigidity and the central ceiling for deformations adding a nonnegative prime-side measure; the positive ceiling ⟺ horizontal zero-free line ⟺ RH.
- [`CentralExcessForcesASquareRootPrimeDeficit.lean`](CentralExcessForcesASquareRootPrimeDeficit.lean) — Atomic surplus measures on the logarithmic lattice and the square-root deficit law for arithmetic members of `HeightCoupledSystem`.
- [`TheDeficitResidueBoundsTheCentralExcess.lean`](TheDeficitResidueBoundsTheCentralExcess.lean) — The quantitative deficit–excess law: the Abelian residue of the prime deficit at the centre bounds the central excess.
- [`PositiveCoupledRigidityAndTheCriticalTransferLaw.lean`](PositiveCoupledRigidityAndTheCriticalTransferLaw.lean) — Critical Gram and transfer laws for positive deformations, Hadamard rigidity at constant central order, and the classification of positive rigidity by horizontal zero-free lines.
- [`StrongMultiplicityOneBelowTheSquareRootDeficit.lean`](StrongMultiplicityOneBelowTheSquareRootDeficit.lean) — Arithmetic members with sub-square-root deficit that keep the central order have the coefficients of `ζ_γ`.
- [`MultiPrimeDiophantineRepulsion.lean`](MultiPrimeDiophantineRepulsion.lean) — Siegel-lemma repulsion of the Liouville vacuum on `N` primes, stretched-exponential in the height.
- [`TheLandauWronskianDeformationPrinciple.lean`](TheLandauWronskianDeformationPrinciple.lean) — Divisor comparison of two entire functions whose logarithmic derivatives differ by the Laplace transform of a nonnegative measure.
- [`TheAbelGramLawOfPositiveDeformations.lean`](TheAbelGramLawOfPositiveDeformations.lean) — Abel limits, transfer bound, Gram law and line capacity for divisor jumps across a vertical line.
- [`StrongMultiplicityOneForPowersOfZeta.lean`](StrongMultiplicityOneForPowersOfZeta.lean) — Rigidity of `ζ^d` in `CompletedPositiveSystem κ d` without pole budget, and strong multiplicity one below the square-root deficit.
- [`TheBoundaryCapacityOfDeformationsOfPowersOfZeta.lean`](TheBoundaryCapacityOfDeformationsOfPowersOfZeta.lean) — The boundary capacity `(κ − d)/2` of deformations of `ζ^d`.
