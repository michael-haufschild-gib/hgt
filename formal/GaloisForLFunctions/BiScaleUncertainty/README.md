# Bi-Scale Uncertainty (BSU)

Namespace `GaloisForLFunctions.BiScaleUncertainty`; umbrella `BiScaleUncertainty.lean`; flat folder.

**Question.** On the logarithmic line two incompatible structures constrain every source and
correlation kernel: the integer grid $\{\log n\}$ (additive, compressing exponentially) and the
hyperbolic archimedean weight (multiplicative, growing exponentially). BSU states, as exact
unconditional inequalities, what each structure forces on the other, and expresses the
square-root barrier of prime counting as one bi-scale energy law. RH enters only through
equivalences or criteria whose premise is an explicit energy bound.

---

## 1. Place in the research

BSU supplies the **source, observation and calibration language** for the critical arithmetic
form. Keep its two questions separate:

1. What do prescribed log-node correlations force on a source's archimedean energy? → exact
   uncertainty constants, node-deletion prices, sharp counterexamples.
2. What does the signed prime–polar discrepancy reveal through packets, bands and finite
   observations? → cancellation as a quantitative zero-width measurement.

Neither permits replacing a prime–polar difference by the sum of the sizes of its parts.

| Neighbour | Interface |
|---|---|
| arithmetic-positivity-theory | Factorial sources → complete-form sampling, critical kernels |
| BezoutValuationIncidence | Owns period→finite-horizon moment transfer, pronic/residue arithmetic |
| TransHorizonIncidenceMechanics | Which finite observations pay a Möbius receiver |
| SquareRootThreshold | Zero configurations at a lag/aperture, every-height quantifier |
| ArithmeticCriticalityTheory, ArithmeticIncidencePositivity | Same energy as ground-state / pair-conductance problems |
| ScaleSignedIncidenceCriticality | Information lost by blind/averaged/sign-insensitive observation |
| ArithmeticCompensationTheory, SignedArithmeticEnergyIncidence | Signed derivative work, complete-energy cross terms |
| TransThresholdPairCorrelation | Same prime polynomial beyond $X>T$; the band $|\xi|\le\sqrt N$ is that regime |
| ArithmeticOrientationTheory | Band law = growth-unit entry of `widthDictionary_tfae`; node criticality = node test |

Route consumers: WL (spline probe, multiplicity defect, deficit endpoint law), FU (prime-clock
kernels), OWU (odd polar hyperplane), SZ (Lévy energy pays every arithmetic cusp of the Suzuki
source). None of these tools carries the sign a route still needs.

**Criteria for any mechanism aimed at the sign of the complete critical form:** fails for a
Beurling system with an off-line zero; works at one character, modulus one, no family average;
carries information beyond length = height at square-root precision; separates $\log4$ from
$\log6$. Every receiver reads one number, the width $\Delta=\sup|\Re\rho-\tfrac12|$; here its unit
is the band's growth exponent. A reformulation in another unit is not progress.

---

## 2. Why

In $x=\log t$ a state $f\in L^2(\mathbb R)$ carries four structures:

1. **Positive-definite cone:** $h_f=f\star\tilde f$, $\hat h_f=|\hat f|^2$, chord metric $\|T_xf-T_yf\|^2=2(h_f(0)-h_f(x-y))$.
2. **Log grid** $\{\log n\}$, spacing $\delta_n\approx1/n$: Nyquist density $e^x$.
3. **Hyperbolic polar weight** $2\cosh(x/2)$, polar balance $\int_0^\infty h_f\cosh(x/2)=0$.
4. **Singular archimedean energy** $\mathcal J(f)=\int_0^\infty(h_f(0)-h_f(x))w_{\rm arch}(x)dx$,
   $w_{\rm arch}=e^{x/2}/\sinh x$ ($\sim1/x$ at 0, $\sim2e^{-x/2}$ at $\infty$); $w_{\rm arch}(\log n)=2/\sqrt n+O(n^{-5/2})$.

**Where RH sits.** For real compact $f$,
$\Re W(f)=\Omega(0)h_f(0)+\mathcal J(f)-2\bigl(\sum_n\frac{\Lambda(n)}{\sqrt n}h_f(\log n)-\int_0^\infty2\cosh(x/2)h_f\bigr)$,
$\Omega(0)=-(\gamma+\tfrac\pi2+\log8\pi)$. On the polar hyperplane the archimedean part is $\ge0$ iff
$|\Omega(0)|h_f(0)\le\mathcal J(f)$ (**bi-scale uncertainty inequality**). The prime term vanishes on
the **blind cone** $h_f(\log n)=0$.

**The barrier.** $\tilde E(t)=e^{-t/2}(\psi(e^t)-e^t)$, $L=\log(N+2)$: $\int_0^L\tilde E^2=O(L)$ ⇔
Laplace energy of $\nu_N$ is $O(L)$ ⇔ band energy on $|\xi|\le\sqrt{N+2}$ is $O(L)$ ⇔ RH. Outside the
band everything is bounded; the band is the wall.

**Why "bi-scale".** Probing $|\xi|\le\sqrt x$ needs sources of width $\lesssim1/\sqrt x$ while the grid
at scale $\log x$ has spacing $1/x$. The origin singularity of $w_{\rm arch}$ pays for the compression;
exponent ½ is exactly the one making cell budgets $n^{-1/2}\cdot n^{-1}$ summable.

---

## 3. Objects and language

**Sources.** $h_f(x)=\int f(u)f(u+x)du$; increment $h_f(0)-h_f(x)=\tfrac12\|T_xf-f\|^2$; Krein
$(h(x)-h(y))^2\le2h(0)(h(0)-h(x-y))$, the only regularity ever used. A source *sees*
$\tfrac12+i\gamma$ if $\hat f(\gamma)\ne0$.

**Node sets.** `BlindOn 𝒩`; *gapped* (arbitrarily far log-gaps, e.g. powers of one integer);
*sub-square-root density* (node count $K$ on far unit windows with $M(K+1)(1+\log(K+1))\le e^{X/2}$);
*clique* (shifts with $h(t_i-t_j)=0$).

**Weights.** $w_{\rm arch}$; dual $e^{-x/2}/\sinh x$; secant core $\operatorname{sech}(x/2)$;
reciprocal $1/w_{\rm arch}\le ye^{y/2}$ (price of transport); Lévy symbol $\sim\log|t|$.

**Symbol objects.** For a nonnegative combination $c$: $\mathrm{mass}(c)$, $A(c)=\sum c_f(\Omega(0)h_f(0)+\mathcal J(f))$,
node values $v_c(n)$. **Folded symbol** for $q$: $F(z)=\Omega(\|z\|/\log q)$ on the circle, mean $m_q$,
cosine coefficients $\varphi_d$. Blind / zero-pole slack: least $M$ with $A+M\,\mathrm{mass}\ge0$ on
the cone (`blindSymbolValue`, `zeroPoleBlindSymbolValue`). **Moment value**
$V_q(J)=\inf\{\int Fd\nu:\int\cos(jz)d\nu=0,\ j\in J\}$.

**Polar objects.** Polar copy $f-e^{-T/2}f(\cdot-T)$; `evenPolarCopy` kills both moments at $O(e^{-T})$
energy; distant pair $b-\sigma b(\cdot-T)$ has pole $\asymp e^{T/2}$ of either sign at bounded cost.

**Signed prime–polar objects.** $\nu_N=\sum_{n\le N+2}\Lambda(n)n^{-1/2}\delta_{\log n}-2\cosh(t/2)\mathbf1_{[0,L]}dt$;
packet $P_f=f\star\nu$ (`stationaryPacket`); critical energies $E(f)=\sum m_\rho^2|\hat f|^2$,
$W(f)=\sum m_\rho|\hat f|^2$; gauge derivative $f'-f/2$; **Weil pole operator** $f''-f/4$
(annihilates $e^{\pm t/2}$); causal response and Laplace energy.

**Deficit objects.** $D(T)=\int_0^T(e^t-\psi(e^t))dt$; `ccmPrimeDeficitIncoming` $=e^{-T/2}D(T)$;
critical deficit energy; `weilLagFunctionReal`.

**Probes.** Dilates, tuned probes, boosts; universal probe (`SeesAllZeros`); explicit `splineProbe`
(boosted cubic spline, $(\sin z/z)^4$ transform).

**Nyquist order objects.** Cell masses $\alpha_k(\beta,m)$ of the Taylor-order-$m$ jet against the
weight of exponent $\beta$; at the critical exponent $\beta=m+1$ they diverge like $c_m\log M$; the
**critical finite part** $\mathcal B_m=\sum_k(\alpha_k-c_m\delta_k)$ (`nyquistCriticalFinitePart`) and the
residual of stretched sources (`nyquistCriticalSourceResidual`).

**Observation objects.** Closed correlation products $\prod h(x_i)/h(0)$ over lag lists summing to
zero (pairs $[x,-x]$, spokes); measured arrays and fitting residuals; finite nets; detection order.

**Integer-window objects.** On $[1,N]$: `integerWindowVariance`, `additiveStepEnergy`, doubling edges
$n\to2n$, `WindowCoercivityBound`, binary-parent paths, the dyadic mantissa tent
(`dyadicMantissaTent`, doubling-null), exact and soft doubling incidence on perturbed positions.

**Discrete side.** Coprime shear; divisor-sieve signals on period $N!$ (Selberg coordinates,
Ramanujan lag weight $c_e(h)$); every finite window vector is a sieve signal (`exists_finite_sieveSeq_realization`).

---

## 4. Mechanisms

1. **Krein geometry.** $\sqrt{h(0)-h}$ subadditive ⇒ doubling/dyadic cascades. Derivative-free;
   the only way information moves between lags.
2. **Bessel spheres and origin leverage.** Clique ⇒ orthogonal translates; origin weight from
   $w_{\rm arch}\sim1/y$ transfers collar weight into $\mathcal J$. Unconditional multi-node Gram
   identities keep the off-diagonal terms; on dyadic cosets they reduce to powers of 2.
3. **Nyquist absorption.** $\int_0^{\delta_n}(h(0)-h)\le\frac1n\int_0^{\log2}(h(0)-h)w_{\rm arch}$; one
   canonical origin shared across scales (shares $\sim n^{-3/2}$ summable exactly at ½).
4. **Nyquist critical order.** At $\beta=m+1$, $|\alpha_k-c_m\delta_k|\le D_m/(k+1)^2$, so a finite
   part exists. A stretched compact source has residual
   $=c_m\frac{(\int f)^2}{2\int f^2}L+\mathcal B_m+o(1)$ while its normalized archimedean energy $\to0$:
   the **ordinary mean**, not the energy, decides escape.
5. **Gaps against density.** Distant pairs in far gaps carry every pole mass at vanishing cost ⇒
   zero-pole slack = blind slack there. Square-root node density is critical for pole visibility.
6. **Linear Krein smoothing.** $\log\frac1{|x-y|}|h(x)-h(y)|\le32\sqrt e\,\mathcal J+2h(0)$, sharp.
7. **Folded symbol and circle moments.** Blindness at all $q^j$ makes the phase measure uniform ⇒
   bathtub $A\ge m_q\,\mathrm{mass}$; signed bathtub without blindness. Every power slack is
   $-V_q(J)$. An extra node helps iff multiplicatively independent of $q$ (incidence, not spacing).
8. **Hyperbolic multipliers.** $C_\alpha,S_\alpha$, Casimir identity, light cone; source blindness
   does not transfer to multipliers; the odd pole term vanishes on the odd polar hyperplane.
9. **Signed prime–polar transport.** Annulus averaging + Stieltjes against $\psi(e^x)$ turns prime
   sums into Chebyshev work paid by Krein and the reciprocal weight.
10. **Hyperbolic gauge.** All arithmetic of $P_f$ sits in $\tilde E$; the Laplace energy (not a sharp
    window) is the band-limited object.
11. **Band = width.** Width $\le\alpha$ ⇔ $\int_0^L\tilde E^2=O(e^{2\beta L})$ $\forall\beta>\alpha$;
    subexponential ⇒ linear; band slope $\ge\sum n_k^2/|\rho_k|^2$, never sublinear.
12. **Packets as filters.** Beyond the support $\sum m_\rho e^{i\gamma\tau}\hat f=A_f-P_f$;
    $P_f=O(e^{\sigma\tau})$ iff $f$ blind beyond depth $\sigma$; one side suffices; packets oscillate.
13. **Second-order pole operator.** Packets are local integrals of the deficit against $f''-f/4$, with
    no $\log2\pi$ term.
14. **Hardy deficit inequality.** $2E(T)+\int_0^TE\le4\int_0^T\tilde E^2$.
15. **Zero-density filtering.** Cosine modulation at $\gamma\in[\Gamma,2\Gamma]$ localises the deficit
    to $|\Im\rho|\asymp\Gamma$; hybrid Ingham/Guth–Maynard/DH gives cancellation up to aperture
    $\alpha\log\Gamma$, $\alpha<\tfrac23$.
16. **Producers.** Chebyshev bi-null stencils, factorial lifts, Müntz completion, Nyquist/Taylor
    polar producers, compensated physical producers (truncation + zero-integral compensation + box
    smoothing, converging in $L^2$ and in every compact source/jump form).
17. **Closed-cycle observation.** Pair products give $|h|$; continuity fixes the sign near 0; long
    cycles of small increments recover signed $h$ everywhere. Finite order fails exactly: separated
    copies at gap $T$ differ only by packet parity, detected iff order $n>T$. With a Lévy-energy
    ceiling, explicit radius/mesh/order/noise threshold give $\varepsilon$-recovery from a measured
    array on any finite net; plain $L^2$ suffices; derivative energy gives linear conditioning.
18. **Integer-window coercivity.** Variance $\le C\cdot$(additive + doubling energy): binary-parent
    paths with geometric depth weights give $C=O(N)$, the dyadic mantissa tent gives $C=\Omega(N)$;
    additive edges alone need $C\asymp N^2$ (linear signal). Exact doubling incidence is destroyed
    by arbitrarily small node perturbations; soft triangular weights restore it with factor $1-6\delta$.
19. **Coprime shear / Sobolev side.** Multiplicative energy = additive energy × scale; coprime trace
    coercivity is sharp.
20. **Observation theory of sieves.** Period covariance diagonal in Selberg coordinates with
    eigenvalue $c_e(h)$; 5th/6th moments recover up to one canonical translation.
21. **Node criticality.** Farkas + pole-weight rigidity + Weil-cone uniqueness: any certificate has
    $w=\Lambda$; a node is indispensable iff prime power; deletion prices are local Euler factors.
22. **Window spectra.** Window ceiling/floor $\sim\pm e^{L/2}$; every unimodular multiplicative twist
    has the same extremes: phases are read by summed damped receivers, not suprema.

---

## 5. Pillar theorems

1. **Krein geometry and logarithmic modulus** (`autocorr_krein_increment_sq_le`, `autocorr_zero_sub_progressionSmoothed_le`).
2. **Gaps against density**: zero-pole slack = blind slack on gapped / sub-$\sqrt{}$ sets
   (`not_zeroPoleBlindPositiveOn_of_gapped`, `zeroPoleBlindSymbolValue_eq_of_density`).
3. **Power-grid moment theorem**: $V_q(\mathbb N)=m_q$, $V_q(\mathbb N\setminus\{d\})=m_q-|\varphi_d|$;
   independence law (`powerMomentValue_univ`, `exists_lt_blindSymbolSlackOn_insert_of_not_mem`).
4. **Band law**: RH ⇔ linear band ⇔ linear Laplace energy; rate = 2·width
   (`riemannHypothesis_iff_meanSquare_band`, `riemannHypothesis_iff_forall_meanSquareBandRate`).
5. **Packets**: growth exponent = deepest seen zero; one side suffices; $W\le E$ with equality iff
   simple (`packet_lower_iff`, `riemannHypothesis_iff_forall_packet_bddAbove`, `packet_weil_law`).
6. **Explicit universal probe**: RH ⇔ one spline-weighted prime sum below its polar prediction for
   $\tau>4$ (`riemannHypothesis_iff_spline_prime_sum_le_of_gt_four`).
7. **Deficit energy = width**, self-improving at the endpoint
   (`zetaZeroWidth_le_iff_forall_criticalDeficitEnergyRate`, `riemannHypothesis_iff_linear_criticalDeficitEnergy`).
8. **High zeros carry a bounded deficit** for $\alpha<\tfrac23$ (`exists_abs_incoming_sub_lowZeroDeficitSum_le`).
9. **Node criticality**: zero-pole positivity on $\mathcal N$ ⇔ RH ∧ $\mathcal N\supseteq$ prime powers
   (`zeroPoleBlindPositiveOn_iff`, `not_zeroPoleBlindPositiveOn_diff_four`, `zeroPoleBlindPositiveOn_diff_six_iff`).
10. **Critical Nyquist classification**: finite limit iff zero mean; nonzero mean escapes linearly
    with slope $\propto(\int f)^2$ at vanishing archimedean energy
    (`tendsto_nyquistCriticalSourceResidual_iff_mean_zero`, `tendsto_nyquistCriticalSourceResidual_atTop_of_mean_ne_zero`).
11. **Closed-cycle recovery and its sharp failure**: detection iff order $>T$; explicit finite-net
    recovery for Lévy-bounded and $L^2$ sources (`controlledSource_detects_iff`, `grid_recovery_automatic`,
    `L2Cycle.global_recovery_norm`).
12. **Integer-window best constant is linear with doubling, quadratic without**
    (`dyadicWindowBestConstant_bounds`, `additive_coercivity_constant_linear_lower_bound`,
    `exactDoubling_quadratic_coercivity_lower`, `softDoubling_window_coercivity`).

---

## 6. Traps

| Trap | Correct statement |
|---|---|
| Bound by $-h''(0)$ or $\Omega(0)$ alone | Discards $\mathcal J$; use Krein |
| Translation-invariant mean field | Cannot see node positions |
| $f\to|f|$ on sign-changing states | Drops the cross collar; keep the nodal loss |
| One zero bounds an interior increment | Only the reflected pair; fold the interval |
| Finite vs infinite grid decides pole visibility | Gaps vs density decides it |
| Second node gain depends on spacing | Zero iff multiplicatively dependent |
| Source blindness ⇒ multiplier blindness | False (odd six-packet train) |
| Working only on the blind subspace | Kills $\Lambda(n)/\sqrt n$; cannot see off-line countermodels |
| Receiver-only reformulations | Need producers with unconditional errors |
| Windowed Chebyshev energy is band-limited | Sharp window creates a jump; use Laplace energy |
| Growth between linear and exponential | Impossible; subexponential ⇒ linear |
| Barrier might be $o(L)$ | Slope $\ge1/|\rho|^2$ |
| Packet energy = Weil energy | $W\le E$, equality iff simple |
| Window extremes read phases | Twist-invariant; use summed damped receivers |
| Bounding high zeros bounds the deficit | The low-zero finite sum remains unbounded by these tools |
| Small archimedean energy controls the Nyquist residual | Mean decides; energy → 0 while residual → ∞ |
| Finite-order closed products recover polar balance | Separated copies agree through order $T$ |
| Exact doubling incidence is stable | Arbitrarily small perturbations kill it; use soft incidence |
| Additive edges alone give linear coercivity | Linear signal forces the quadratic ratio |
| Rebuilding horizon moment transfer here | Owned by BezoutValuationIncidence |

---

## 7. Open problems

1. **The band.** A source-derived $\int_0^L\tilde E^2=O(L)$ (equivalently spline packet, critical
   deficit energy, Weil-lag energy). Short of it, any explicit strip: unconditional rate is VK.
2. **Low-zero deficit sum.** Bound the sum over zeros below $x^{1/(2\alpha)}$ without RH, or extend
   filtering beyond $\alpha<\tfrac23$; turn frequency-averaged cancellation into a one-sided bound.
3. **Blind cone.** Exact two-tower value; prime-power-blind slack versus window length.
4. **Odd sector.** Source-derived bound on the folded-sinh cell variance at growing aperture.
5. **Multiplicity.** Unconditional tail bound making `finitePrimeMultiplicityDefect` a certified
   simplicity test.
6. **Observation.** Optimal ambiguity-decay rate in cycle order; transfer from finite-moment or
   closed-cycle stability to receiver-energy stability.
7. **Producers.** A multi-scale producer with completion cost and receiver readout controlled
   together; sign of prime-clock kernels $\sum\frac N{pq}(\text{edge}-\text{mass})$.
8. **Selectivity → bound.** Convert node criticality, twist blindness and damped receivers into an
   exponent improvement on the band or packet.

## 8. Tools to build

Source-derived band bound; low-zero deficit control; exact two-tower slack; certified finite-prime
simplicity test; producer with joint completion/receiver control; quantitative bridge from
closed-cycle/integer-window coercivity to packet or band energy.

## 9. Conventions

- Never differentiate a correlation: Krein or its linear smoothing, paid by $\mathcal J$.
- Keep signs (node values, packets, Gram entries); state blindness on a named node set.
- State the regime: grid finite/infinite, regularity class, period vs horizon, polar or not, parity.
- Right coordinates: phase measure for power sets; linear packet for zeros; gauge for packet energy.
- Even polar tests are nested subtypes: `linarith only [...]`; inside the namespace write
  `_root_.RHTower.…`.
- Search sieve, Fermi–Nyman, source-graph and zero-configuration modules before building.
