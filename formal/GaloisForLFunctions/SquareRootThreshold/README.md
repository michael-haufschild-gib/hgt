# Square-Root Threshold (SRT)

**One question.** At height $T$, which information in the explicit formula makes an off-line zero
visible, and which unconditional mechanisms can reach that information?

SRT is a theory of **visibility**. It fixes a height, a resolution and a zero configuration, and
asks whether Weil positivity at that resolution can tell the configuration from one with all zeros
on the line. Every invisibility statement is paired with a visibility witness. SRT also supplies
the **common units** in which every positivity route reports progress: zero width, aperture,
visibility lag, excluded depth below a height.

Namespace `GaloisForLFunctions.SquareRootThreshold`; umbrella `SquareRootThreshold.lean`. Objects
come from `Zeta23` and `RHTower` — do not redefine them.

---

## 1. Place in the research

Foundational chain: **aperture → accessible lags → Toeplitz or exponential-sum data → visibility
→ zero width**. On periodic configurations this is finite matrix algebra; on tempered
configurations it uses two-bump tests, Laplace transforms, Landau's theorem and record estimates.
Arithmetic enters when the explicit formula identifies the readings with the prime source.

SRT owns the **lag face** of the shared target: one window inequality $P_v\ge0$ per scale for the
difference tests of one width. It is a live route: RH ⇔ the prime–archimedean sign on
$\kappa_w(t+v/2)-\kappa_w(t-v/2)$ for all $v\ge V$; the open estimate is that sign at every positive
exponential slack.

| Programme | Connection |
|---|---|
| [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md) | Complete test families; tent detection goes through SRT visibility |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Packet envelopes, blind directions, observation vs receiver |
| [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md) | Möbius receiver damping = zero width |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Arithmetic inside windows, source-specific Gram estimates |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md) | Ground energy $\mu(A)$; Rayleigh bridge to lag floors |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Allocation losses graded by width; odd window to $181/500$ |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | $\mu$ strictly decreasing; unique contact aperture |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Hodge-type sign; prime-tower negative squares; all-parity Sobolev floors |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Open problem 1: prime pairs beyond $X=T$ |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | `widthDictionary_tfae`; Nyquist rank bound |
| [ArithmeticLocalDivisorGeometry](../ArithmeticLocalDivisorGeometry/README.md) | Detector costs vs local zero movement |
| Others (SSIC, ACT-comp, SAEI) | Bounded certificates, flux/forcing, source signs before receivers |

---

## 2. Why

**Weil positivity sees zeros through tests.** On-line zeros contribute $|h_f(\gamma)|^2\ge0$; a
reflected off-line pair contributes an indefinite rank-two term. The question is always: which
tests expose the indefinite terms?

**A test has a resolution and a prime length.** Aperture $a$ (support $[-a,a]$): reads primes up
to $X=e^{2a}$, resolves ordinates to $\pi/a$. Zero spacing at height $T$ is $2\pi/L$, $L=\log(T/2\pi)$.

**The threshold.** An off-line lattice $\{\tfrac12\pm\delta+2\pi ik/L\}$ at zero density is
indistinguishable from an on-line lattice for every $a\le L/2$, whatever $\delta$, and visible
beyond (`RHTower.offLineLattice_weil_positive_iff`). At $a=L/2$ the test reads primes up to
$X\asymp T$: the **square-root threshold** — also the diagonal threshold of the Dirichlet-polynomial
mean value theorem and the density-hypothesis threshold. Below it: which configurations hide, and
what makes them visible early? Beyond it: which unconditional prime information reaches $a>L/2$?

---

## 3. Objects and language

| Object | Lean |
|---|---|
| $h_f(z)=\int f e^{izu}$; $\gamma_\rho=(\rho-\frac12)/i$ | `Zeta23.paperFT`, `Zeta23.gammaOf` |
| Zero configuration (reflection-invariant multiset); Weil form | `Zeta23.ZeroConfig`, `ZeroConfig.W` |
| Zeros of $\zeta$, explicit formula | `Zeta23.zetaZeroConfig`, `WeilEF.EF_lit_zetaZeroConfig` |
| Hodge index at level $a$ (pole-killed tests) | `RHTower.HodgeIndexAtLevel` |
| Lattices, periodic profiles/patterns, runs, clusters, jitter, dilution | `onLineLatticeConfig`, `offLineLatticeConfig`, `profileConfig`, `patternConfig`, `runConfig`, `clusterConfig`, `jitterConfig`, `dilutedLatticeConfig` |
| Lag symbol $D(m)$, Toeplitz form | `depthSymbol`, `patternSymbol`, `toeplitzForm` |
| Height shift, window slice, windowed form | `heightShift`, `windowSlice`, `windowedW` |
| Tempered configuration | `TemperedConfig` |
| Prime polynomial $\Pi_f$ (odd/even, smooth/rough), archimedean–pole part $A_f$, diagonal energy | `primePolynomial`, `archPart`, `primeVariance` |
| Two-bump test $\beta(t+v/2)+\tau\beta(t-v/2)$; lag structure $S(v)$; minor deficit | `twoBump`, `lagStructure`, `minorDeficit` |
| Prime window functional $P_v$ on $|\log n-v|\le2w$ | `lagPrimeWindow`, `lagPrimePowWindow`, `lagPrimeWindowRHS` |
| Depth deficit/excess transforms, level weight, off-line moment | `depthDeficit`, `depthExcess`, `levelWeight`, `offLineMoment` |
| Laplace/Fejér/grid lag windows | `lapWin`, `fejerWin`, `geomWin` |
| Visibility lags, horizons, excluded depths | `oneParamLag`, `nearTopLag`, `recordLag`, `boxHorizon`, `clusterHorizonHeight`, `zetaClusterHorizonHeight`, `nearTopExcludedDepth` |
| Window prime polynomial, off-line correction, $S(T)$ | `windowPrime`, `offLineCorrection`, `rvmRemainder` |
| Zero width $\sup|\Re\rho-\frac12|$ | `zetaZeroWidth` |

**Words.** *Visible at aperture $a$*: some $C^2$ test on $[-a,a]$ has $\Re W<0$. *Isolated / dense /
cluster / crystal* (periodic uniform-depth arithmetic progression of ordinates). *Shadow*: on-line
configuration with the same Weil form at that aperture. *Level*, *top level*, *attained*.
*Minor*: $|S(v)+\overline{S(-v)}|\le2\Re S(0)$. *Nyquist aperture* $P\ell/2$. *Near-top zero*
(within $1/V$ of the supremum; exists at every lag off RH). *Loud/quiet record*, *twin*, *collapsed
cluster*.

---

## 4. Mechanisms

### Zero side
1. **Lag representation.** Aperture-$a$ tests see the configuration only through lags $|v|\le2a$;
   depth enters as $e^{\pm\delta v}$, a pair as $2\cosh(\delta v)$.
2. **Poisson on lattices.** Below $L/2$ only the lag-zero atom survives.
3. **Toeplitz law.** If $W=\ell\sum_mk(m\ell)D(m)$, hiding at $a$ ⇔ Toeplitz section of size
   $\lceil2a/\ell\rceil$ is PSD.
4. **Hiding is mimicry.** PSD section = moments of on-line translates (Carathéodory–Fejér).
5. **Position resolved at the same aperture**; an off-line configuration is read completely by
   $|m|\le2P$ modes.
6. **Ground state** = $\ell\cdot$ lowest Toeplitz eigenvalue; off-lattice: $L(n-U_{n-1}(\cosh\delta L))$,
   decay exponent exactly $2d_{\max}$.
7. **cosh amplification of modes**; exact cancellation is crystalline (Newton identities).
8. **Edges and variation.** Below threshold a test reads depth *variation*: a run edge is seen at
   aperture $O(1/\delta)$ independent of run length and density.
9. **Two-point minors for any tempered configuration.** Two-bump tests; isolated pairs seen once
   $e^{\delta v}$ exceeds local on-line mass; finite sets seen at $(1/2g)\log M+O(1)$; level
   conservation $G+L+E$ across levels; Laplace + analytic continuation: every off-line zero is
   eventually seen. Only $\tau=\pm1$ needed; for $\zeta$ one sign (Landau + no real zeros in the
   strip); the height can be dropped. Rate: least $\Re W$ at lag $v$ is $\ge-Ce^{Dv}$ and not
   $O(e^{\sigma v})$ below the deepest depth.
10. **Faithfulness.** The lag family determines the configuration (up to $m(\rho)+m(\bar\rho)$ and the
    point $\tfrac12$); Ingham resolves $g$-separated on-line sets at $a>\pi/(2g)$, sharp.
11. **Rank-two pair estimate**: $\ge(2a-\sinh(2\delta a)/\delta)\|F\|^2$, extremal $\sinh(\delta\cdot)$.
12. **The pole is a depth-½ pair** at height 0: the whole infinite prime tail.
13. **Polar blindness.** On lag lattices the Hodge index = full Weil positivity; it is blind exactly
    to the points $s=0,1$.

### Windows and heights
14–17. **Slice factorization, height averaging, windowed Gram identity, minimum-aperture
    resolution.** Windowed forms are height averages of localized forms. Threshold-localized
    variance: sub-threshold core silent; even ($2$-adic) sector diagonal at every bandwidth; odd
    sector diagonal through the doubled threshold $rX\le1$; trans-threshold neighbour counts cancel
    the degree weight.

### Prime side
18. **Height phase** $(m/n)^{iT}$ of prime pairs changes sign (upper-bound sieves lose it).
19. **Windowed mean zero.** For $2r\le\log2$ the windowed mean of $\Pi_f$ is exactly 0.
20. **Kronecker alignment costs height**: coherent prime excursion $B$ ⇒ negative form or
    $\log(1+2\pi|\xi|)\gtrsim(B-C_f)/\|f\|^2$.
21. **One parameter decides the line.** RH ⇔ $\Re P\ge0$ on difference tests at all lags $v\ge V$
    (any $V$), each lag reading one dyadic prime window. With box-spline bumps
    $B_w=U_{w/4}^{\star4}$ **every** width decides (transform $(\sin z/z)^4$ vanishes only on the real
    axis); smooth bumps decide for all but countably many widths. Same for every primitive
    $L(s,\chi)$. The family measures $\Theta$: $\Re\rho\le\tfrac12+\sigma$ ⇔ $P_v\ge-Ce^{\sigma v}$. Geometric
    grids decide up to chains; prime-logarithm grids separate finitely many right zeros. On the
    off-line lattice the family is a comb meeting the crystal at the threshold.

### Finite lag ranges
22. **Record-potential law** (effective Landau): positivity on $[0,V]$ bounds every exponent's
    coefficient by archimedean/pole terms + the potential of the others; Fejér windows raise decay;
    grid aliasing explains chains.
23. **For $\zeta$: hiding needs twins, twins need triples, clusters collapse.** Local zero count ⇒
    every loud near-top record has a companion within $O(\log\log\gamma/V)$; isolated twins add
    coherently; hiding clusters have exponentially small geometric-mean radius.
24. **Explicit lags.** Near-top zeros seen at $V_w\asymp(\log\gamma_0)^2\log\log\gamma_0/\delta_0$
    (modulated) or $V_0(w,\eta,\delta_0)$ (unmodulated); every finite right set gives $P_v<0$ at some
    $v\le V_0$.
25. **Horizon law.** $P_v\ge0$ on $[0,V]$ forces depth gaps and escape to larger height and smaller
    amplitude beyond `boxHorizon`.
38. **Companion law** for the unmodulated family from the local zero count alone (Legendre records).
    *Smooth detection:* every off-line zero has a $C^\infty$ negative witness at aperture
    $\le C(4+|\Im\rho|)^2/|\Re\rho-\frac12|^2$.

### The lag face and its neighbours
26. **Unconditional envelopes.** $P_v\ge-|\varphi(0)|-(W+S_2)e^{v/2-\sqrt v/10}$ (dlVP); VK gives
    $e^{v/2-v^{ex}}$, $ex<3/5$. Rate stays ½.
27. **Rayleigh bridge.** $2\|\kappa_w\|^2\mu(v/2+w)\le\Re P_v$; $\mu\ge-Ce^{2\sigma A}$ ⇒ width $\le\sigma$. Odd
    windows transfer directly: $\Re P_{w,v}\ge\frac1{500}\|\kappa_w\|^2$ for $v/2+w\le181/500$ — the first
    prime atom is paid on the family; the second prime window $\log3/2$ is beyond reach.
28. **The window prime polynomial reads $S(T)$**; $S(T)$ is unbounded unconditionally ⇒ no
    finite-rank bounded-spectral-shift models.
29. **Width = lag rate = heat time.** `zetaZeroWidth` $\le\sigma$ ⇔ $P_v\ge-Ce^{\sigma v}$; de Bruijn–Newman
    $H_t$ real-rooted for $t\ge$ width$^2/2$.
30. **Near-top zeros and contact.** Negative $P_v$ ⇒ $\mu(v/2+w)<0$; visibility lags decompose as
    numerator$/\delta_0$ + drift and invert to excluded depths; cluster-robust exclusion of depth
    $\ge1/R$ below `zetaClusterHorizonHeight` $=\exp(R/(10^5A_0\log^2R))-306$ under window positivity.
31. **Width bounds the energy-normalised floor** (Stieltjes against the Chebyshev error; $H^1$ datum).
32. **Graded incidence ledger.** Allocation failing by $Ce^{2\sigma r}$ still certifies $\tfrac12+\sigma$; rate
    0 is RH; polynomial/log losses free; bounded-aperture windows report nothing.
33–35. **Sampling.** $\sum_q|\Phi(z_q)|^2\le M(2a+2\pi)e^{2\pi}e^{2\sigma a}\int|f|^2$ on locally bounded
    points (depth cost $e^{2\sigma a}$ vs density cost); unconditional floor in the archimedean
    normalisation $\Re W\ge-C(a)\int|\mathcal Ff|^2\log(|y|+3)$: the Weil form is never unbounded below
    in its own normalisation.
36. **Width = ground-energy rate unless off-line zeros cluster.** Under `OffLineCopiesLocallyBounded M`,
    $\mu(A)\ge-M(2A+2\pi)e^{2\pi}e^{2\sigma A}$; dichotomy: exponent = width, or unbounded clustering at
    exponential heights; one-aperture unsigned sampling bound ⇔ all apertures.
37. **Prime tail coupling.** RH ⇔ $\Re\Pi_f\le\Re A_f$ at every aperture/profile/height ⇔ $2\times2$
    pole compression; freezing the archimedean–pole side at height 0 fails, so under RH the finite
    primes must cancel the pole; Bagchi strong recurrence ⇔ the criterion; density-zero bad heights.
39. **One aperture.** RW, ACT, OWU, EWU, AIP, APT and the SRT window measure one number — window
    positivity of $\hat Z$ — with explicit one-way and two-way arrows (parity split; odd window = OWU
    capacity; even blind minimum = even polar ground energy below $\log2$).
40. **One zero width.** PBM, WL, TT, HCF, SZ, TH, RW/HF, FU/MC, PA, LA readings all equal
    `zetaZeroWidth`; none bounds it.

### Arithmetic inside one lag window
For $2w<\log2$: only prime powers contribute; each prime has $\le2$ consecutive powers ($p\ge5$: one);
divisor height $\le1$; same-side atoms are doublings/triplings only; crossing pairs unique per
$p\in\{2,3\}$ and paid with lag discount $e^{-(v-2w)}$; low-order multiplicative relations trivial up
to order $\sim2(v-2w)/\log3$ (sharp).

### Single heights and calibrations
41. **A radius-$R$ certificate reads only primes $<e^{2R}$**: the $3/10$ certificate holds for every
    prime weight; the $181/500$ odd window reads exactly the prime 2.
42. **Phase-selective single-height law.** Retaining the signed prime polynomial at one height removes
    the prime cost where phases are favourable; height-uniform coefficient 4 is optimal.
43. **Function-field calibration.** Weil positivity at $a$ ⇔ zero negative index of the span Gram;
    purity ⇔ lag positivity at the teeth; golden fake curve positive exactly to $\log5/2$.
44. **Every height.** Head-conditioned decoupling: rough mean square unchanged under head return
    kernels; strip points damp rough variance by $y^{-2\delta}$.

---

## 5. Pillar theorems

1. Square-root threshold (`RHTower.offLineLattice_weil_positive_iff`).
2. Toeplitz law and mimicry (`profileConfig_weil_nonneg_iff`).
3. Faithfulness (`lag_weil_eq_iff_symmMult_eq`, `eq_zetaZeroConfig_of_lag_weil_eq`).
4. One parameter decides and measures (`zeta_onLine_iff_lag_primeWindow_nonneg`,
   `zeta_re_le_iff_lag_primeWindow_ge_neg_exp`, `riemannHypothesis_iff_lag_splinePrimeWindow_nonneg`).
5. Finite-range visibility (`zeta_near_top_visible_at_polylog_lag`, `one_param_horizon_law`,
   `zeta_companion_law`, `exists_smooth_weil_negative_quadratic_aperture`).
6. Rayleigh bridge (`two_mul_ccmRestrictedWeilGroundEnergy_le_re_lagPrimeWindowRHS`,
   `ccmRestrictedWeilGroundEnergy_neg_of_near_top_zero`).
7. Width dictionaries (`zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp`,
   `riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le`; modules `TheRoutesMeasureOneZeroWidth`,
   `TheRoutesMeasureOneAperture`).
8. Width bounds the floor; archimedean floor; clustering dichotomy
   (`exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt`, `neg_clusterFloorConst_le_ccmRestrictedWeilGroundEnergy`,
   `polarGroundEnergyRate_eq_zetaZeroWidth_or_offLineCopies_cluster`).
9. Graded ledger (`zetaZeroWidth_le_of_gradedIncidenceAllocation`).
10. Prime tail coupling (`riemannHypothesis_iff_primePolynomial_le_archPart`,
    `primePolynomial_le_archPart_iff_poleCompression`, `exists_archPart_zero_lt_primePolynomial`).
11. Excluded depth below a height (`zeta_abs_re_sub_half_lt_of_hodgeIndex`, `zetaContactAperture_le_of_offLine_zero`).
12. Function-field calibration (`curveConfig_weil_nonneg_iff_unitary_of_card_le`, `curveConfig_lagTest_nonneg_iff_unitary`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Aperture is a height cutoff | It is a frequency resolution |
| Thresholds for finite configurations | Finite off-line sets are visible at every aperture |
| Some configuration hides from all apertures | None does; hiding is about bounded apertures |
| Tests see depth | Below threshold they see depth *variation* |
| The off-line lattice is typical | Its invisibility is crystalline; other patterns are seen earlier |
| Polar constraint helps vs dense configurations | Hodge index = full positivity on lag lattices |
| Hodge index = all zeros on the line | Blind to $s=0,1$ |
| More off-line zeros = more visible | Not monotone; positivity is collective |
| Window averages reach depth | They are aperture-$r$ forms |
| Prime side keeps a sign on short windows | Windowed mean is exactly 0 |
| Small primes carry the criterion | Any tail $v\ge V$ decides |
| The one-parameter criterion is a local detector | Weight decays in height; Landau is ineffective; use records |
| Only generic widths decide | Box splines make every width decide |
| Upper-bound sieve beyond $X=T$ | Loses the height phase |
| A single lag grid decides | Chains can hide from grids |
| Landau gives a visibility lag | Ineffective; lags need the record's loudness |
| A twin hides a record | Twins add coherently; hiding needs collapsed clusters |
| Ground-energy and lag floors are different | Rayleigh bridge makes them one |
| The sign is what must be proved | A sub-exponential loss suffices; rate = width |
| Bounded-aperture windows bound the width | Report nothing in the width unit |
| Energy-normalised floor = $L^2$ floor | $L^2$ needs local off-line density |
| The Weil form is unbounded below | Not in its archimedean normalisation |
| Depth cost and density cost are one factor | $e^{2\sigma a}$ vs $M(2a+2\pi)e^{2\pi}$ |
| One route's positivity is independent evidence | One aperture, one width |
| Finite primes bounded by archimedean part alone | They must cancel the pole |

---

## 7. Open problems

1. **Beyond the square-root threshold.** Bound off-diagonal prime pairs at $\lambda=\log X/\log T>1$.
   Size-only bounds attain their excess; sieves lose the phase (parity problem); zero side needs
   $N(\tfrac12+\delta,T)\ll T^{1-2\lambda\delta}$ (DH gives $\lambda\le1$). What remains is the odd
   trans-threshold regime: signed correlation of odd prime pairs $(m,m+2h)$, $h\ll m/T$ (→ TTPC).
2. **Beyond every finite horizon.** Bound the depth of zeros above every finite height cutoff;
   excluding the escape is RH.
3. **All-profile window to $\frac12\log2$.** Even pole direction between $3/10$ and $\frac12\log2$ unpaid;
   windows become selective only by reading more primes.
4. **$L^2$-normalised width arrow.** Rule out the clustering branch or prove the exponent identity
   without a local count. Known: polar and full $L^2$ rates are equal unconditionally, and in the
   CCM form-domain (log-weighted) normalisation the rate equals the width unconditionally
   (ACCE: `groundEnergyRate_eq_polarGroundEnergyRate`, `formGroundEnergyRate_eq_zetaZeroWidth`).
5. **$P_v\ge0$ beyond an explicit lag**; any envelope $-Ce^{\sigma v}$ with $\sigma<\tfrac12$ (current: rate ½).
6. **Visibility tradeoff.** Optimal $(\delta(n,R),T(n,R))$; polynomial height cutoff in $e^R$.
7. **Window incidence into pair payment.** Turn the growing independence order into control of the
   signed prime–polar pairing at the needed lag and height.
8. **Every height.** Control $\log\zeta(s)-\sum_{p\le y}p^{-s}$ at a fixed $s$ conditioned on head returns.

Topics: report lag $V$ or rate $\sigma$; calibration transfer from function fields; phase-selective
heights ($c<4$) vs bad-height density; record which weights each window certificate holds for.

---

## 8. Tools

Built: lag representation, Poisson on lattices, Toeplitz/Carathéodory–Fejér; two-point minors,
Ingham windows; one-parameter lag family (smooth and box-spline); record-potential law, explicit
lags, horizon and companion laws; Rayleigh bridge; width and aperture dictionaries; graded ledger;
sampling on locally bounded points; excluded-depth inversions; threshold-localized variance;
window incidence laws; function-field calibration.

To build: a single-height prime estimate using height phases beyond $X=T$; control of zeros beyond
every finite horizon; the $L^2$ width arrow without local sampling.

---

## 9. Principles

- Search the corpus first; lattice, tilt, `paperFT`, explicit formula and Hodge tools exist in Zeta23/RHTower.
- Pair every invisibility theorem with a visibility witness.
- Every statement names height, aperture/resolution and the strongest unconditional value.
- Honest classes: $C^2$ compact tests; configurations finite/lattice/periodic/tempered or `zetaZeroConfig`.
- Periodic ⇒ Toeplitz in $D(m)$; aperiodic ⇒ lag structure $S(v)$ with Laplace, Landau, Ingham.
