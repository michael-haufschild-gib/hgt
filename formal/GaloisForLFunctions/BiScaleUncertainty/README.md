# Bi-Scale Uncertainty (BSU)

BSU is the theory of sources and correlation kernels constrained simultaneously by two
incompatible structures on the logarithmic line: the integer grid $\{\log n\}$ (additive,
compressing exponentially) and the hyperbolic weight of the archimedean place (multiplicative,
growing exponentially). It states, as exact unconditional inequalities, what each structure
forces on the other, and expresses the square-root barrier of prime counting as one bi-scale
energy law. RH enters only through equivalences or criteria whose premise is an explicit energy
bound; no theorem asserts such a premise.

Namespace `GaloisForLFunctions.BiScaleUncertainty`; umbrella `BiScaleUncertainty.lean`; flat folder.

---

## 1. Place in the research

BSU supplies the **source, observation and calibration language** for the critical arithmetic
form. Keep its two questions separate:

1. What do prescribed log-node correlations force on a source's archimedean energy? → exact
   uncertainty constants, node-deletion prices, sharp counterexamples.
2. What does the signed prime–polar discrepancy reveal through packets, bands and finite
   observations? → cancellation as a quantitative zero-width measurement.

Neither permits replacing a prime–polar difference by the sum of the sizes of its parts.

**Four orienting pillars:** Krein increment geometry (correlations without a spectral second
moment); the folded-symbol moment problem (power-grid slacks); band/packet growth exponents =
visible zero depth; node criticality (zero-pole positivity needs RH and every prime-power node,
nothing at non-prime-powers: $\log4$ fatal, $\log6$ free).

| Neighbour | Interface |
|---|---|
| [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md) | Factorial sources → complete-form sampling, critical kernels |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Owns period→finite-horizon moment transfer, pronic/residue arithmetic |
| [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md) | Which finite observations pay a Möbius receiver; half-damped phase receiver |
| [SquareRootThreshold](../SquareRootThreshold/README.md) | Zero configurations at a lag/aperture, every-height quantifier |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md), [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Same energy as ground-state / pair-conductance problems |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Parameter transport with horizon-uniform bounds |
| [ScaleSignedIncidenceCriticality](../ScaleSignedIncidenceCriticality/README.md) | Information lost by blind/averaged/sign-insensitive observation |
| [ArithmeticCompensationTheory](../ArithmeticCompensationTheory/README.md), [SignedArithmeticEnergyIncidence](../SignedArithmeticEnergyIncidence/README.md) | Signed derivative work and complete-energy cross terms |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Arithmetic effectivity beyond correlation geometry |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Same prime polynomial beyond Montgomery–Vaughan $X>T$; the band $|\xi|\le\sqrt N$ is exactly that regime |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Band law = growth-unit entry of `widthDictionary_tfae`; node criticality = node test of the selectivity battery |

**Route consumers.** WL: cubic-spline universal probe, finite-shift bounds, multiplicity defect,
deficit endpoint law. FU: prime-clock mass/edge kernels. OWU: odd polar hyperplane. MSC:
squarefree Hilbert source. SZ: Lévy energy pays every arithmetic cusp of the Suzuki source;
finite-jump Weil formula. RB: valuation core of Robin counterexamples. BVI: stratified
observation theory. None of these tools carries the sign a route still needs.

**Criteria for any mechanism aimed at the shared target** (sign of the complete critical form):
fails for a Beurling system with an off-line zero; works at one character and modulus one with
no family average; carries information beyond length = height at square-root precision;
separates $\log4$ from $\log6$. Every receiver reads one number, the width
$\Delta=\sup|\Re\rho-\tfrac12|$; here the unit is the band's growth exponent. A reformulation in
another unit is not progress.

---

## 2. Why

In $x=\log t$ a state $f\in L^2(\mathbb R)$ carries four structures:

1. **Positive-definite cone:** $h_f=f\star\tilde f$, $\hat h_f=|\hat f|^2\ge0$, chord metric
   $\|T_xf-T_yf\|^2=2(h_f(0)-h_f(x-y))$.
2. **Log grid** $\{\log n\}$, spacing $\delta_n=\log\frac{n+1}n\approx1/n$: Nyquist density $e^x$.
3. **Hyperbolic polar weight** $2\cosh(x/2)$ and polar balance $\int_0^\infty h_f\cosh(x/2)=0$.
4. **Singular archimedean energy**
   $\mathcal J(f)=\int_0^\infty(h_f(0)-h_f(x))w_{\text{arch}}(x)dx$, $w_{\text{arch}}=e^{x/2}/\sinh x\sim1/x$
   at $0$, $\sim2e^{-x/2}$ at $\infty$; $w_{\text{arch}}(\log n)=2/\sqrt n+O(n^{-5/2})$ is the
   critical prime weight.

**Where RH sits.** For real compact $f$,
$$\Re W(f)=\Omega(0)h_f(0)+\mathcal J(f)-2\Bigl(\sum_n\frac{\Lambda(n)}{\sqrt n}h_f(\log n)-\int_0^\infty2\cosh(x/2)h_f\Bigr),\quad\Omega(0)=-(\gamma+\tfrac\pi2+\log8\pi).$$
On the polar hyperplane the archimedean part is $\ge0$ iff $|\Omega(0)|h_f(0)\le\mathcal J(f)$ (the
**bi-scale uncertainty inequality**). The prime term vanishes on the **blind cone**
$h_f(\log n)=0$; the sharp question there is $\inf\mathcal J/h_f(0)$ vs $|\Omega(0)|$.

**The barrier.** With $\tilde E(t)=e^{-t/2}(\psi(e^t)-e^t)$, $L=\log(N+2)$:
$\int_0^L\tilde E^2=O(L)$ ⇔ Laplace energy of $\nu_N$ is $O(L)$ ⇔ band energy on
$|\xi|\le\sqrt{N+2}$ is $O(L)$ ⇔ RH. Outside the band everything is bounded; the band is the wall.

**Why "bi-scale".** Probing the band $|\xi|\le\sqrt x$ needs sources of width $\lesssim1/\sqrt x$
while the grid at scale $\log x$ has spacing $1/x$. The origin singularity of $w_{\text{arch}}$
pays for the compression: $n\le w_{\text{arch}}(y)$ on $(0,\delta_n]$, and exponent ½ is exactly
the one making cell budgets $n^{-1/2}\cdot n^{-1}$ summable.

---

## 3. Objects and language

**Sources.** $h_f(x)=\int f(u)f(u+x)du$; increment $h_f(0)-h_f(x)=\tfrac12\|T_xf-f\|^2$; Krein
$(h(x)-h(y))^2\le2h(0)(h(0)-h(x-y))$ — the only regularity ever used. A source *sees* a zero
$\tfrac12+i\gamma$ if $\hat f(\gamma)\ne0$.

**Node sets.** `BlindOn 𝒩`: correlation vanishes at $\log n$, $n\in\mathcal N$. *Gapped*:
arbitrarily far log-gaps of half-width $1/5$ (powers of one integer). *Sub-square-root window
density*: $M(K+1)(1+\log(K+1))\le e^{X/2}$ for node count $K$ on far unit windows ($S$-smooth
integers qualify; the full grid does not). *Clique*: shifts with $h(t_i-t_j)=0$; under grid
blindness every dyadic-odd coset $\{\log(m2^k)\}$ is one.

**Weights.** Forward $w_{\text{arch}}$; dual $e^{-x/2}/\sinh x$; secant core
$\operatorname{sech}(x/2)$ ($w_{\text{arch}}=\operatorname{sech}+w_{\text{dual}}$); reciprocal
$1/w_{\text{arch}}\le ye^{y/2}$ (price of transport); Lévy symbol
$\int(1-\cos tx)w_{\text{arch}}\sim\log|t|$.

**Symbol objects.** For a nonnegative combination $c$ with spectral density $G_c$:
$\mathrm{mass}(c)$, $A(c)=\frac1{2\pi}\int G_c\Omega=\sum c_f(\Omega(0)h_f(0)+\mathcal J(f))$, node values
$v_c(n)$. **Folded symbol** for $q$, $\ell=\log q$: $F(z)=\Omega(\|z\|/\ell)$ on the circle; period
mean $m_q$, cosine coefficients $\varphi_d$, orbit averages $F_d$. **Slack:** $M$ is a blind
(zero-pole) slack on $\mathcal N$ if $A+M\,\mathrm{mass}\ge0$ on the blind (zero-pole) cone; exact
least values `blindSymbolValue`, `zeroPoleBlindSymbolValue`. **Moment value**
$V_q(J)=\inf\{\int Fd\nu:\nu$ prob. on circle, $\int\cos(jz)d\nu=0,\ j\in J\}$.

**Polar objects.** Pole term $2((\int f\cosh\frac u2)^2-(\int f\sinh\frac u2)^2)$. Polar copy
$f-e^{-T/2}f(\cdot-T)$; symmetric copy `evenPolarCopy` kills both moments at $O(e^{-T})$ energy;
distant pair $b-\sigma b(\cdot-T)$: pole $\asymp e^{T/2}$ of either sign at bounded archimedean cost.

**Signed prime–polar objects.** $\nu_N=\sum_{n\le N+2}\Lambda(n)n^{-1/2}\delta_{\log n}-2\cosh(t/2)\mathbf1_{[0,L]}dt$;
packet $P_f=f\star\nu$; stationary packet at shift $\tau$ (linear in $f$, `stationaryPacket`);
zero series $\sum m_\rho e^{i\gamma_\rho\tau}\hat f(\gamma_\rho)$; critical energies
$E(f)=\sum_{\text{crit}}m_\rho^2|\hat f|^2$, $W(f)=\sum_{\text{crit}}m_\rho|\hat f|^2$; gauge derivative
$f'-f/2$; second-order **Weil pole operator** $f''-f/4$ (annihilates $\operatorname{span}\{e^{\pm t/2}\}$);
causal response $R_N=K\star\nu_N$, Laplace energy $\int R_N^2$.

**Deficit objects.** $D(T)=\int_0^T(e^t-\psi(e^t))dt$; incoming amplitude
`ccmPrimeDeficitIncoming` $=e^{-T/2}D(T)$; critical deficit energy (its square); outgoing amplitude
and `weilLagFunctionReal`; spectral form $\Re\sum_\rho m_\rho e^{(\rho-1/2)T}/\rho^2+O((1+T)e^{-T/2})$.

**Probes.** Dilates, tuned probes $\varphi(u/R)\cos\gamma_0u$, boosts $e^{tu}\varphi$; universal
probe = sees every zero (`SeesAllZeros`); explicit: `splineProbe` (boosted cubic spline,
$(\sin z/z)^4$ transform).

**Discrete side.** Coprime shear ($v(kn)$ vs $\Delta v$, $\gcd(n,n+1)=1$); divisor-sieve signals
$s_{N,c}$ on period $N!$, Selberg coordinates $Y_{N,c}$, Ramanujan lag weight $c_e(h)$, translated
and affine moments, top dyadic order, visibility, local Hölder stability.

---

## 4. Mechanisms

1. **Krein geometry.** Peter–Paul ⇒ $\sqrt{h(0)-h}$ subadditive ⇒ doubling, multiple and dyadic
   cascades; harmonic subdivision at a nonpositive node. Derivative-free; the only way information
   moves between lags.
2. **Bessel spheres and origin leverage.** A clique makes translates orthogonal, so collar
   vectors lie in a ball; dual: $\sum w_i(h(0)-h(y-t_i))\ge(\sum w_i-\sqrt{\sum w_i^2})h(0)$. Adding
   origin weight $W_0\to\infty$ (from $w_{\text{arch}}\sim1/y$) transfers collar weight into $\mathcal J$.
   One zero bounds only the reflected pair: fold the Lévy integral.
3. **Nyquist absorption.** $\int_0^{\delta_n}(h(0)-h)\le\frac1n\int_0^{\log2}(h(0)-h)w_{\text{arch}}$;
   canonical weight $\varpi_n$ shares one origin across all scales (shares $\sim n^{-3/2}$ summable
   exactly at ½); gives all-scale von Mangoldt signed coercivity.
4. **Gaps against density.** Distant pairs in far gaps (or node-free points on sub-$\sqrt{}$
   density sets) carry every pole mass at vanishing archimedean and $L^2$ cost ⇒ zero-pole slack =
   blind slack there; width rigidity forbids compressing bounded energy into a far gap
   ($\ge e^{-r_2/2}\log(r_2/r_1)h(0)$). Square-root node density is critical for pole visibility.
5. **Linear Krein smoothing.** Lag-progression averaging removes the square root:
   $\log\frac1{|x-y|}|h(x)-h(y)|\le32\sqrt e\,\mathcal J+2h(0)$, sharp. Beurling–Turán window is
   $\Theta(\log M)$ in both directions (spectral Dirichlet flatness / quarter-shifted designs).
6. **Folded symbol and circle moments.** Blindness at all $q^j$ makes the phase measure uniform ⇒
   bathtub $A\ge m_q\,\mathrm{mass}$, exact. **Signed bathtub** (no blindness):
   $A=m_q\mathrm{mass}+\sum_j\varphi_j\sqrt{q^j}v_c(q^j)+\frac1{2\pi}\int G(\Omega-F\circ\text{phase})$.
   Every power slack is $-V_q(J)$; designs give upper bounds, phase measures lower bounds.
   An extra node helps iff multiplicatively independent of $q$ (incidence, not spacing).
7. **Hyperbolic multipliers.** $C_\alpha,S_\alpha$ (boost group); Casimir
   $(h_{C_\alpha f}-h_{S_\alpha f})/\cosh\alpha x=h_f$; light cone. Source blindness does not transfer
   to multipliers. Odd pole term $=-2(\int f\sinh\frac u2)^2$; on the odd polar hyperplane it
   vanishes for every pole weight. Coherent price $\log2$ sharp. All but countably many boosts are
   universal probes.
8. **Collar allocation as convex optimisation.** Concave coefficient of a physical partition;
   supporting prices certify distance to optimum; attainment via Hilbert coordinates; leading
   tail $4/\sqrt N$.
9. **Signed prime–polar transport.** Annulus averaging + Stieltjes against $\psi(e^x)$ turns prime
   sums into Chebyshev work, paid by Krein and the reciprocal weight. The untruncated Weil
   functional is $\Omega(0)h(0)+\mathcal J-2\,\mathrm{fullPairing}(h)$ for every parity.
10. **Hyperbolic gauge.** $P_f=f-\int e^{-t/2}f(\cdot+t)+\tilde E(L)f(\cdot+L)-\int\tilde E(f'-f/2)(\cdot+t)$:
    all arithmetic sits in $\tilde E$. Cell identity makes $\int\tilde E^2$ a weighted mean square of
    $\psi(n)-m_n$. MV bounds the atomic part off the band. The Laplace energy (not a sharp window)
    is the band-limited object. Renewal chain on geometric ladders.
11. **Band = width.** For $0\le\alpha<\tfrac12$: width $\le\alpha$ ⇔ $\int_0^L\tilde E^2=O(e^{2\beta L})$
    ⇔ Laplace energy ⇔ band energy, $\forall\beta>\alpha$ (resolvent continuation / von Koch).
    Endpoint self-improves: subexponential ⇒ linear. Band slope $\ge\sum n_k^2/|\rho_k|^2$ (Abel
    means against critical characters), so the barrier is never sublinear.
12. **Packets as filters.** Beyond the support $\sum m_\rho e^{i\gamma\tau}\hat f=A_f(\tau)-P_f(\tau)$;
    $P_f=O(e^{\sigma\tau})$ iff $f$ is blind beyond depth $\sigma$; one side suffices (Landau +
    no real zeros); every nonzero packet oscillates; Parseval gives packet–Weil law $W\le E$.
13. **Second-order pole operator.** $f''-f/4$ annihilates the polar space, so packets equal local
    integrals of the incoming/outgoing deficit or the Weil lag against $f''-f/4$ with no
    archimedean $\log2\pi$ term; the autocorrelation of a universal probe is universal.
14. **Hardy energy inequality for the deficit.** Completing the square in $E'+E=2W$:
    $2E(T)+\int_0^TE\le4\int_0^T\tilde E^2$; local $L^2$ window bounds → packet bounds via
    $2\mu|g|\le\mu^2+g^2$.
15. **Zero-density filtering.** Cosine modulation at frequency $\gamma\in[\Gamma,2\Gamma]$ localises
    the deficit's spectral sum to $|\Im\rho|\asymp\Gamma$, replacing worst-zero control by counts.
    Hybrid Ingham/Guth–Maynard/DH gives $N(\sigma,T)\ll T^{1-\frac43(\sigma-\frac12)+o(1)}$ on all of
    $[\tfrac12,1]$, hence frequency-averaged cancellation up to aperture $\alpha\log\Gamma$, $\alpha<\tfrac23$.
16. **Triangular Gram split.** Strictly upper triangular cross Gram is nilpotent: numerical radius
    $\le\cos(\pi/(n+2))\|T\|$; discarded entries kept as explicit error. For synchronized blocks of
    bounded depth only.
17. **Producers.** Chebyshev bi-null stencils ($T(4N)-4T(2N)+4T(N)=O(\log N)$), factorial lifts,
    Müntz completion (pole-free hyperplane has zero completion cost), Nyquist/Taylor polar
    producers, compensated physical producers, spectral designs (midpoint, quarter-shift, orbit).
18. **Coprime shear / Sobolev side.** Multiplicative energy = additive energy × scale; coprime
    projections form a lattice; modulus/clamp lose an exact nodal term.
19. **Observation theory.** Period covariance diagonal in Selberg coordinates with eigenvalue
    $c_e(h)$; affine moments leave one sign per divisibility component; 5th/6th moments recover up
    to one canonical translation; Parseval relation-energy dichotomy on `zeroProductTuples`.
20. **Node criticality.** Farkas duality + pole-weight rigidity + Weil-cone uniqueness: any
    certificate has $\beta=1$, $w=\Lambda$; a node is indispensable iff it is a prime power.
    Deletion prices are local Euler factors $2\Re(-\zeta_p'/\zeta_p)(\tfrac12+it)$; add across primes,
    interact inside a tower; composites are free for the price and forced for its extremals.
21. **Window spectra.** Window ceiling/floor $\sim\pm e^{L/2}$ (polar kernel eigenpair) to dlVP and
    VK precision; $c(L)\le e^{L/2}+O(L)$ ⇒ RH; mirror $|c+\text{floor}|\le4L+O(1)$ by Kronecker;
    every unimodular multiplicative twist has the same extremes. Phases are read by summed damped
    receivers, not by suprema.

---

## 5. Pillar theorems

1. **Krein geometry and logarithmic modulus** (`autocorr_krein_increment_sq_le`,
   `autocorr_zero_sub_progressionSmoothed_le`, `integral_Ioi_autocorr_sq_le_of_integerLog_blind`).
2. **Gaps against density**: zero-pole slack = blind slack on gapped and sub-$\sqrt{}$-density sets
   (`not_zeroPoleBlindPositiveOn_of_gapped`, `zeroPoleBlindSymbolValue_eq_of_density`).
3. **Power-grid moment theorem**: closed forms $V_q(\mathbb N)=m_q$,
   $V_q(\mathbb N\setminus\{d\})=m_q-|\varphi_d|$, $V_q(\{d\nmid j\})=\min F_d$; independence law;
   two-tower enclosure (`powerMomentValue_univ`, `powerMomentValue_punctured`,
   `exists_lt_blindSymbolSlackOn_insert_of_not_mem`, `two_tower_blindSymbolValue_enclosure`).
4. **Band law**: RH ⇔ linear band ⇔ linear Laplace energy; rate = 2·width; no intermediate growth;
   under RH the mean tends to $\sum m_\rho^2/|\rho|^2$ (`riemannHypothesis_iff_meanSquare_band`,
   `riemannHypothesis_iff_forall_meanSquareBandRate`, `tendsto_mean_sq_normalizedLogError`).
5. **Packets**: growth exponent = deepest seen zero; one side suffices; oscillation
   (`packet_lower_iff`, `riemannHypothesis_iff_forall_packet_bddAbove`, `packet_oscillates`, `packet_band_iff`).
6. **Packet–Weil law and multiplicity**: $W\le E$, equality iff simple; $\sup E/W$ = max multiplicity
   (`packet_weil_law`, `multiplicity_ceiling_law`, `two_mul_le_multiplicityDefect`).
7. **Explicit universal probe**: RH ⇔ one spline-weighted prime sum below its polar prediction for
   all $\tau>4$; RH+simplicity ⇔ one packet identity; single-probe Weil positivity via
   `autocorr splineProbe` (`riemannHypothesis_iff_spline_prime_sum_le_of_gt_four`,
   `riemannHypothesis_and_simple_iff_splineProbe`, `riemannHypothesis_iff_autocorr_splineProbe_packet_bddAbove`).
8. **Deficit energy = width**: width $\le\sigma$ ⇔ critical deficit energy/pointwise rates
   $\forall\beta>\sigma$; subexponential ⇔ RH and self-improves to linear; quadratic/cubic signed
   arithmetic targets (coprime cross work, centred off-diagonal, Euler curvature) self-improve to
   linear (`zetaZeroWidth_le_iff_forall_criticalDeficitEnergyRate`,
   `riemannHypothesis_iff_linear_criticalDeficitEnergy`, `riemannHypothesis_iff_quadratic_centeredOffDiagonal`).
9. **Integrated deficit attains the width endpoint**: $|I(T)|\le Be^{\Delta T}$ at $\Delta$ itself;
   under RH $\frac1T\int I^2\to\sum m_\rho^2/|\rho|^4$ (`exists_endpoint_bounds_at_zetaZeroWidth`, `tendsto_mean_ccmPrimeDeficitCriticalEnergy`).
10. **High zeros carry a bounded deficit**: for $\alpha<\tfrac23$ zeros with $|\gamma|\ge e^{T/(2\alpha)}$
    contribute $O(1)$ uniformly in $T$; the deficit is a finite low-zero sum up to $O(1)$; frequency
    averages of the deficit decay like $\Gamma^{-1/2}$ (`exists_highZero_deficitZeroWeight_tsum_le`,
    `exists_abs_incoming_sub_lowZeroDeficitSum_le`, `exists_frequencyAverage_abs_cosineFiltered_ccmPrimeDeficitIncoming_le`).
11. **Node criticality**: zero-pole positivity on $\mathcal N$ ⇔ RH ∧ $\mathcal N\supseteq$ prime
    powers; Euler deletion prices (`zeroPoleBlindPositiveOn_iff`, `not_zeroPoleBlindPositiveOn_diff_four`,
    `zeroPoleBlindPositiveOn_diff_six_iff`, `weilPositiveAt_certificate_rigidity`).
12. **Window spectra read sizes** (`riemannHypothesis_of_windowCeiling_le`,
    `abs_windowCeiling_add_windowFloor_le`, `twistedWindowCeiling_eq`).
13. **Pole compression is graded and reads a size**: $|\mathrm{cross}(a)|\le Ce^{(1+2\alpha)a}$ ⇒
    width $\le\alpha$; $Ce^a$ alone ⇒ RH (`riemannHypothesis_of_abs_ccmWeilPoleCross_le`).
14. **Sharp observation recovery**: exponent $1/6$ globally (optimal), $1/3$ on the top-coordinate
    stratum, cutoff-independent coordinate constants, relation-energy dichotomy
    (`exists_physical_translate_holder`, `no_improved_physical_exponent_near_zero`,
    `quantitative_sign_relation_dichotomy`).

---

## 6. Traps

| Trap | Correct statement |
|---|---|
| Bound by $-h''(0)$ or $\Omega(0)$ alone | Discards $\mathcal J$; use Krein |
| Translation-invariant mean field | Cannot see node positions |
| $f\to|f|$ on sign-changing states | Drops the cross collar; keep the nodal loss |
| One zero bounds an interior increment | Only the reflected pair; fold the interval |
| Finite vs infinite grid decides pole visibility | Gaps vs density decides it |
| Polar constraint improves a power-set bathtub | Zero-pole slack = blind slack $=-m_q$ |
| Second node gain depends on spacing | Incidence law: zero iff multiplicatively dependent |
| Bochner/Beurling commutative reasoning | Translations see only divisibility (shared with Beurling) |
| Source blindness ⇒ multiplier blindness | False (odd six-packet train) |
| Working only on the blind subspace | Kills $\Lambda(n)/\sqrt n$; cannot see off-line countermodels |
| Receiver-only reformulations | Need producers with unconditional errors |
| Windowed Chebyshev energy is band-limited | Sharp window creates jump $\tilde E(L)$; use Laplace energy |
| Growth strictly between linear and exponential | Impossible; subexponential ⇒ linear |
| 2×2 pole criterion needs a sign | It is a size bound $|\mathrm{cross}|\le Ce^a$ |
| Barrier might be $o(L)$ | Slope $\ge1/|\rho|^2$ by Hardy's zero |
| Two-sided packet control needed | One side suffices |
| Packet energy = Weil energy | $W\le E$, equality iff simple |
| Müntz ramp diagonal separates on/off-line zeros | Readouts → 0 on both sides; separation is off-diagonal + polar |
| Chain sine gain is uniform | Decays like $(n+2)^{-2}$ |
| Window extremes read phases | Twist-invariant; use summed damped receivers |
| Bounding high zeros bounds the deficit | Only the low-zero finite sum remains, and it is unbounded by these tools |
| Endpoint constants of $I(T)$ transfer to $\tilde E$ | Different normalisations: $|\rho|^{-4}$ vs $|\rho|^{-2}$ |
| Local cube-root recovery for Möbius rows | Needs a top dyadic coordinate; squarefree rows have none ($N\ge4$) |
| Rebuilding horizon moment transfer here | Owned by BezoutValuationIncidence |

---

## 7. Open problems

1. **The band.** A source-derived bound $\int_0^L\tilde E^2=O(L)$ (equivalently on the spline
   packet, the critical deficit energy, or the Weil-lag energy). Short of it, any explicit strip:
   the deficit has unconditional rate VK ($e^{T-\kappa T^{3/5-\varepsilon}}$) against the needed
   $1+2\alpha$.
2. **Low-zero deficit sum.** High zeros are bounded; bound the finite sum over zeros below
   $x^{1/(2\alpha)}$ (any exponent above $3/4$) without RH, or extend the filtering beyond
   $\alpha<\tfrac23$ (needs better zero-density near $\sigma=\tfrac12$). Turn frequency-averaged
   cancellation into a pointwise or one-sided deficit bound.
3. **Blind cone.** Exact two-tower value; prime-power-blind slack as a function of window length
   (between the Lévy tail floor and the full-grid value); full prime-power-blind polar class (=RH).
4. **Odd sector.** Source-derived bound on the folded-sinh cell variance surviving growing aperture.
5. **Packets and multiplicity.** Finite envelope for the spline packet (=RH); unconditional tail
   bound making `finitePrimeMultiplicityDefect` a certified test of $E(U)=W(U)$; simplicity itself.
6. **Observation.** Cost of observing less (fewer moments, shorter windows); any transfer from
   finite-moment stability to receiver-energy stability.
7. **Producers.** A multi-scale producer with completion cost and receiver readout controlled
   together; sign of $\sum\frac N{pq}(\text{edge}-\text{mass})$ prime-clock kernels.
8. **Selectivity → bound.** Convert node criticality, twist blindness and phase-sensitive damped
   receivers into an exponent improvement on the band or packet.

---

## 8. Tools

Built: Krein calculus; folded symbol + circle moment problem (designs primal, line certificates
dual); polar enforcement devices; hyperbolic gauge and second-order pole operator; packet engine
(linear explicit formula, one-sided Landau, Parseval, tuned/spline probes); deficit energy
inequality and zero-width rate dictionary; zero-density filtering (hybrid IGM–DH exponent, folded
dyadic shells); triangular Gram split; producers; observation theory (Selberg coordinates,
canonical translation, stratified/global stability, relation dichotomy); node-criticality and
deletion-price calculus; window spectra to VK precision.

To build: a source-derived band bound; low-zero deficit control; exact two-tower slack; a
certified finite-prime simplicity test; a producer with joint completion/receiver control.

---

## 9. Working conventions

- Never differentiate a correlation: Krein or its linear smoothing, paid by $\mathcal J$.
- Keep signs (node values, packets, Gram entries); blindness is a sharpness check, stated on a
  named node set (`BlindOn 𝒩`).
- State the regime: grid finite/infinite, regularity class, period vs horizon, polar or not, parity.
- Right coordinates: phase measure for power sets; linear packet for zeros; gauge for packet energy.
- Receivers come with producers. Test against Beurling and the degenerate point.
- Even polar tests are nested subtypes: use `linarith only [...]`, explicit namespace theorems.
  Inside the namespace `open RHTower` resolves locally; write `_root_.RHTower.…`.
- Search other programmes (sieve, Fermi–Nyman, source graph, zero configuration) before building.
