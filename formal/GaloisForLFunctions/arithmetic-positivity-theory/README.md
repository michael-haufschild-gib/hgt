# Arithmetic Positivity Theory (APT)

APT asks which independently checkable features of an exact arithmetic source control the sign,
the mixed couplings and the stability of the complete Weil form of $\zeta$. Sources keep their
literal $\Lambda$-weights, divisor identities and Bernoulli sawtooth remainders, together with
endpoint jumps, collar shifts, Gamma factors and poles. Positivity is always proved on a stated
family at a stated scale. Every theorem is unconditional. The RH receivers are destinations and
circularity checks, never premises.

Namespace `GaloisForLFunctions.ArithmeticPositivityTheory`; umbrella `ArithmeticPositivityTheory.lean`.

---

## 1. Place in the research

APT is the **source theory of the complete Weil form**. The other coordinates of the same form
are pairwise incidence, lag and aperture. APT supplies literal sources, complete-form
approximation and receiver transfer. Its central finding is that positive families exist at
every support length, but each positivity is paid for by an archimedean gain $\log M$. The gap to
RH is to remove that subsidy.

| Programme | Interface |
|---|---|
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Factorial Müntz sources, signed prime–polar domain, increment energy, selectivity countermodels |
| [SquareRootThreshold](../SquareRootThreshold/README.md) | Zero configurations, visibility lags, width–floor dictionary, single-height aperture |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md) | Ground-energy path, Markov/pole split, small-aperture gauges |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Pair conductances, pole-plane balance $\sum\Lambda h-\int(e^s+1)h$, odd strip surplus |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md), [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md) | Finite arithmetic and sign-sensitive receiver estimates beyond size-only bounds |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Transport in damping/aperture/cutoff with the full signed derivative |
| [ScaleSignedIncidenceCriticality](../ScaleSignedIncidenceCriticality/README.md) | Whether the data a proof reads can separate target from countermodels |
| [ArithmeticCompensationTheory](../ArithmeticCompensationTheory/README.md) | Same-source compensation; why adapted norms restate the target |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Effectivity producing a definite form; polar box DoF minus prime node count $=E(s)$ |
| [SignedArithmeticEnergyIncidence](../SignedArithmeticEnergyIncidence/README.md) | Signed source → energy + cross terms; which estimates survive growing aperture |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Mean-square counterpart of the single-height prime saving (§7.3) |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Width dictionary, selectivity battery; the factorial family is a calibration library |
| `RHTower` (`Suzuki/`, CCM) | Explicit formula, zero divisor, counts, Suzuki source, Sonin/CCM operators |

Consumers: the linear-window negativity of the critical prime channel feeds the signed prime
scheduling route (FU); window/lacunary positivity and receiver transfer feed the even pole-weight
route (EWU); the critical family is the test class of the Suzuki route (SZ).

**Three transfer criteria.**

- *Selectivity:* a law also satisfied by $\zeta(s-a)\zeta(s+a)$, Beurling off-line systems or
  Liouville-twisted weights is infrastructure only.
- *No archimedean subsidy:* a $\log M$ or $\log(1/w)$ gain against bounded prime cost is
  nonselective. A frequency-growing subsidy admits the all-ones weight. Constant or linear
  aperture losses are harmless.
- *Grading:* a floor losing $C_\sigma e^{2\sigma r}$ at aperture $r$ gives width $\le\sigma$; an
  aperture-uniform loss gives RH. Conversely width $<\beta$ gives the rate-$2\beta$ floor
  (`exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt`, SquareRootThreshold).

---

## 2. Why

Exact identities never supply a sign. Self-adjoint realisations, Krein involutions and ground
states have eigenvalues of both signs; positivity of one piece (archimedean jump integral,
Markov part) says nothing about the whole; Cauchy–Schwarz on $\mathcal W$ needs $\mathcal W\ge0$
first. The arithmetic has to pay for the sign, and APT's first discovery is that it can pay on
explicit families through quantities measurable without zero locations: physical square mass,
translation energy at the arithmetic scale, an independent zero-sampling form, harmonic
separation of collar frequencies, and oscillatory cancellation under prime dilation.

**The two receivers (RH-equivalent).**

1. *Critical-scale cancellation.* With $D(T)=\int_0^T(e^t-\psi(e^t))dt$, a one-sided bound
   $D(T)\le B(1+T)e^{T/2}$ (or $\ge-B(1+T)e^{T/2}$) for all $T$ is RH.
2. *Capacity inequality.* For real compact $C^2$ tests and prime apertures $N$ beyond the
   support, $\mathcal W(g)=\mathcal M_N(g)+\tfrac12C(g)^2-\tfrac12S(g)^2$ with
   $\mathcal M_N=V_N\|g\|^2+J_{\text{Lévy}}+J_{\text{prime},N}$, $V_N=\Omega(0)-2\sum_{m\le N}\Lambda(m)/\sqrt m$,
   $C=\int2\cosh(u/2)g$, $S=\int2\sinh(u/2)g$. RH iff $S^2\le2\mathcal M_N+C^2$ for all tests.

**They are one functional.** Abel summation against the pole density $e^s+1$ gives, for $C^1$
lag weights $h$ vanishing beyond the horizon,
$\sum\Lambda(n)h(\log n)-\int_0^\infty(e^s+1)h=-\int_0^\infty(D(s)+s^2/2-s)h''$. On a test of
aperture $r$, prime channel minus pole plane equals $\int_0^{2r}E(s)w_F(s)ds$ with the
**two-pole Chebyshev defect** $E(s)=e^s+s-1-\psi(e^s)$ and lag weight
$w_F(s)=2e^{-s/2}(\int FF'(\cdot+s)-\tfrac12a_F(s))$. The reflected pole makes the Weil-natural
defect $\psi(x)-x-\log x+1$, and is the source of $(1+T)$ in receiver 1. Read as a count, $E(s)$
is polar-box degrees of freedom minus weighted prime nodes
(`polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect`, ArithmeticCastelnuovoSeveri).

**One exact laboratory.** Abstract principles are calibrated on the *factorial correction tail*:
noncompact, with an endpoint jump, a shrinking irrational collar, and readouts holomorphic only on
$\Re s>-1$. Each mechanism must reproduce a known positive case and fail honestly on a known
obstruction.

---

## 3. Objects and language

### 3.1 Zero side

Readout $F_f(s)=\int f(x)e^{(s-1/2)x}dx$ (`paperFT f (gammaOf s)`). Over zeros $\rho$ with
multiplicity $m_\rho$ (only $0<\Re\rho<1$ used):

$$
\mathcal Z(f)=\sum m_\rho|F_f(\rho)|^2,\quad
\mathcal W(f,g)=\sum m_\rho F_f(\rho)\overline{F_g(1-\bar\rho)},\quad
\mathcal R(f)=\sum\tfrac{m_\rho}2|F_f(\rho)-F_f(1-\bar\rho)|^2 .
$$

**Universal reflection identity:** $\mathcal Z-\Re\mathcal W=\mathcal R$ for every zero
configuration and square-summable source. $\mathcal Z\ge0$ is trivial; $\mathcal W\ge0$ is never
assumed; $|\mathcal W(f,g)|\le\sqrt{\mathcal Z(f)\mathcal Z(g)}$ always.
Lean: `zetaZeroSquareMass`, `zetaZeroConfig.W`, `configurationReflectionDefect`.

### 3.2 Physical side

$Q(g)=\frac1{2\pi}\int|\hat g|^2\Omega+2\Re(\hat g(i/2)\overline{\hat g(-i/2)})-T_\Lambda(g\star\tilde g)$:
Gamma bracket, two polar readouts, von Mangoldt atoms (the Weil form *subtracts* primes).
**Gamma–Lévy form:** archimedean channel $\Omega(0)a_g(0)+\int_0^\infty(a_g(0)-a_g(x))\omega(x)dx$,
$\omega(x)=e^{x/2}/\sinh x$; prime channel $2\sum\Lambda(r)r^{-1/2}a_g(\log r)$. Taken in `EReal`,
so divergent archimedean energy is $+\infty$; arithmetic channels are proved finite separately.

**Five names, one form.** On continuous compact real sources `compactFullWeilEnergy` = `fullZeroForm`
(ArithmeticCriticalityTheory) = $\Re$ `weilFullFunctional` (RHTower); on $C^2_c$ also
$\Re\mathcal W=\mathcal Z-\mathcal R$ for `zetaZeroConfig`. A fact about one is a fact about all.

### 3.3 The factorial family

| Object | Definition | Lean |
|---|---|---|
| Clamped kernel | $C(u)=\{u\}(1-\{u\})/2$, mean $1/12$ | `clampedLatticeRemainder` |
| Dyadic filter | $P=\tfrac14C(4u)-2C(2u)+4C(u)$; $P-\tfrac3{16}=-\tfrac2{\pi^2}\sum\chi(k)k^{-2}\cos2\pi ku$, $\chi=1,-1,0$ for $k$ odd, $\equiv2$, $\equiv0\ (4)$ | `dyadicBernoulliFilter`, `dyadicHarmonicChi` |
| Harmonic weight | $w_k=\chi(k)/k^2$, $w_1=1$, $\sum_{k\ge2}|w_k|\le3/4$ (first-harmonic dominance) | `dyadicHarmonicWeight` |
| Collar | $(1+\varepsilon_N)^3=1+\tfrac1{4N}$; $\lambda_N=N(1+\varepsilon_N)$, $4\lambda_N^3=N^2(4N+1)$; $\delta_N=\lambda_N-N\in[\tfrac1{15},\tfrac1{12}]$ | `sourceFactorialCollar`, `factorialShiftedFreq` |
| Affine clock | $12N+1$; defect $e_N=N+\tfrac1{12}-\lambda_N$, $Ne_N\to1/144$ | `factorialAffineDefect` |
| Phase profile | $\Phi_N(v)=P(\lambda_Nv)-P(Nv)$ | `factorialPhaseProfile` |
| Correction tail | $T_n(x)=a_ne^{3x/2}\Phi_N(e^{-x})\mathbf1_{x\le0}$, $a_n\asymp N^{-1/2}$ | `factorialMuntzCorrectedTail` |
| Corrected source | $H_n=r_n+T_n$ ($r_n$ compact ramp), readout $c_n/\rho$, $c_n=1/(2\sqrt N)$ | `factorialMuntzBoundaryCorrected` |
| Span test | $f_b=e^{3x/2}B_b(e^{-x})\mathbf1_{x\le0}$, $B_b=\sum b_N\Phi_N$ | `factorialSpanTest` |
| Envelope $\beta$ | $e^{\beta x}B(e^{-x})$; clock $v=e^{-x}$ turns $L^2$ into $\int_1^\infty v^{-(2\beta+1)}|B|^2$ | — |
| Critical source | $\beta=\tfrac12$: $g_b=\mathbf1_{x\le0}e^{x/2}F_b(e^{-x})$ | `criticalFactorialSource` |
| Collared / truncated | $g^c_b=\sigma(e^{-x}-1)g_b$; $g^V=\chi(e^{-x}/V)g^c_b$ compact in $[-\log2V,0]$ | `criticalCollaredSource`, `criticalTruncatedSource` |
| Dyadic block / window | $M\le n+1\le2M$; $[M,LM]$ | `DyadicScaleBlock`, `ScaleWindow` |
| Tent / grid pattern | causal hat of width $d_n=w_{n+1}$ times $e^{3x/2}$; grid pattern = $e^{3x/2}\times$ PL interpolant of nodal data | `factorialSourceRight`, `gridTentPattern` |

**Envelope table.** $\beta>\tfrac12$: prime majorant $\Lambda(r)r^{-\beta-1/2}$ summable; $\beta\le1$
needs rank-one pole cancellation; $\beta=\tfrac12$ (critical): absolute bound diverges but the
oscillatory majorant $\Lambda(r)/(r^{\beta+1/2}(r-1))$ converges for all $\beta>-\tfrac12$. The
critical line is a failure of the absolute bound, not of the prime channel.

### 3.4 Critical-scale objects

| Object | Definition |
|---|---|
| Harmonic defect | $J_m=\int_1^\infty v^{-2}(1-\cos(2\pi mv/12))dv\in[0,2]$ |
| Pattern density / mass | $Q_b(t)=|\sum b_je^{2\pi ijt}|^2$; $J_m(b)$ with $Q_b(mv)$ inserted, $E_b/48\le J_m(b)\le4E_b$ |
| Divisor charge | $A(m)=\chi(m)\sum_{d\mid m}d\Lambda(d)\chi(m/d)$: $A(2)=-2\log2$ unique negative, $A=0$ iff $m=1$ or $4\mid m$ |
| Cumulative charge | $H_N=\sum_{m\le N}A(m)/m^3$: negative exactly for $2\le N\le4$ |
| Band weight | $\gamma(u)=2\sin^2(\pi u/12)/u^2$, Fourier support $[-\tfrac1{12},\tfrac1{12}]$; $\sum_z\gamma(t+z)=\pi^2/6$ |
| Cell kernel | $R(t)=\tfrac12(K(t)+K(1-t))$, $K(t)=\sum_jH_j\gamma(j+t)$ |
| Coupling | $\kappa(k)=\int_0^1R\cos2\pi kt$; $P_\infty(b)=\frac4{\pi^4}\sum b_ib_j\kappa(|i-j|)$ |
| Limiting prime form | $P_\infty(b)=\lim_n$ prime channel of the pattern translated to scale $n$ |

Lean prefix: `factorialCritical*`, `criticalBand*`, `criticalPrimeEnergy`, `criticalCompleteEnergy`.

---

## 4. Mechanisms

1. **Exact compression first.** $\sum_{d\mid k}\Lambda(d)=\log k$ collapses prime rectangles;
   Bernoulli stencils cancel the constant mode in every collar difference. Drift-free stencils are
   classified: on $\{1,q,q^2\}$ sign-flip $(c,-2c/q^2,c/q^4)$, drift-free $(c,-(q+1)c/q^2,c/q^3)$.
   The dyadic choice kills the quadratic drift; its linear drift (=1) is the ramp.
2. **Regularity through the clock.** The tail is not differentiable at integer joins; regularity is
   read in $v=e^{-x}$. Translation energy $D(h)\le C\min(N^{-1},h)$, so
   $\int_0^1D(h)dh/h\le C(1+\log N)/N$. The logarithm is the price of the jump; an $H^1$ bound
   uniform in smoothing is false.
3. **Gamma–Lévy transport.** Gamma excess $=\int\omega(h)D(h)dh$. Lévy symbol
   $\ge e^{-1/2}(\log|t|-3)$: small low-band spectrum + nonzero mass ⇒ Lévy energy grows like
   the log of the band edge (**admissible-source law**).
4. **Zero-divisor sampling without zero locations.** Half-plane subharmonicity on disks of radius
   $\tfrac14$ (readout holomorphic only on $\Re s>-1$), multiplicity-exact overlap $O(\log|\Im s|)$,
   strip energy ⇒ $\mathcal Z(T_n)\le C(1+\log N)/N$, sharp; $\mathcal Z(H_{n,k})\le C/N$.
5. **Independent comparison form.** Transfer across $r=h-u$ through $\mathcal Z$, never through
   $\mathcal W$: factor $\delta-\varepsilon-2\sqrt\varepsilon$, positive iff
   $\varepsilon<(\sqrt{1+\delta}-1)^2$ (sharp Krein radius). Binary Schur law
   $Q\ge0\iff M^2\le4AD$ with explicit negative direction.
6. **Rank-one pole readout.** $F_{\sum a_nH_{n,k}}=F_{\eta_k}\Lambda_{\text{pole}}/\rho$: corrected
   sources span one zero-side dimension; cross-scale positivity is decided on the pole-free
   hyperplane by the tail Gram matrix.
7. **Harmonic layers + Montgomery–Vaughan.** Branches separated by $k/15$; Bohr and window
   coercivity uniform in number/size/spacing; physical Riesz bounds. Physical coercivity is not
   spectral coercivity.
8. **Nonstationary Mellin exclusion.** No stationary point for $|t|\le|\omega|/2$ ⇒ readout
   $\le D\sum|b_N|/N$ on the band $|t|\le\pi M$; the archimedean weight outside is $\ge\log M$.
   Gives **high-scale span coercivity** $\Re\mathcal W(f_b)\ge(\tfrac A2\log M-C)\sum|b_N|^2$.
9. **Parity decoupling of the pole plane.** $C$ vanishes on odd, $S$ on even tests: even tests are
   stabilised, odd tests carry the whole anti-Markovian risk. Creation potential is antitone in
   the aperture.
10. **Collar arithmetic.** $|a\lambda_N-b\lambda_M|<\tfrac1{15}\iff a(12N+1)=b(12M+1)$; the
    prime-thirteen family $N=13M+1$ has gaps $\to0$, so uniform cross-scale oscillatory gain is
    false. Sharp affine constant $N\int v^{-2}|\Phi_N-\Psi_N|^2\to7\zeta(3)/(256\pi^2)$. Baker
    separates the collar spectrum (algebraic degree 3) from prime logarithms.
11. **Critical kernel calculus.** Cosine decay keeps only dilation resonances $k=rl$: rational
    spectrum (atoms at $\log(p/q)$; primes see only $\log r$). Poisson closure of the band weight
    makes $R$ a near-constant: $R(t)\le-1/7000$, quadratic shape with minimum at $\tfrac12$,
    $\kappa(k)\sim I_0/(4\pi^2k^2)>0$, exact Rayleigh range $[\frac4{\pi^4}R(\tfrac12),\frac4{\pi^4}R(0)]$.
12. **Linear-window limit comparison.** Uniform prime/harmonic tails, cardinality-free affine clock
    comparison and resonance-exact affine heads (parameters chosen in order $R,K,\delta,N_0$)
    compare the actual form with its limit on supports of dimension $\delta N$.
13. **Commensurable scale-ratio law.** At scales $aN,cN$ the cross-correlation tends to a
    slow-phase polarisation series over $ak=crl$. At ratio $2{:}1$ the first harmonic of the
    $r=2$ cross term is $+(\log2/\pi^4)J_2$, cancelling the unique negative harmonic exactly.
14. **Dilation calculus for $\ell^2$-uniformity.** Schur test on the cross-scale kernel gives the
    dyadic dilation inequality for weights with $1/f^2$ cosine decay; the endpoint jump kernel
    $-\sin2\pi f/(2\pi f)$ is paid by Montgomery–Vaughan. Window cost: ring majorant
    $\mathcal M_{\text{win}}(L)=\sum\frac{\Lambda(r)}r\min(1,\sqrt{L/r})=\log L+O(1)$ (sharp).
    Cross-block: downward decay $\tau(m,n)$ and a log-ratio coupling depending only on $M/M'$.
15. **Scale-free Schur complement.** Clock-Lipschitz interpolation gives a $V$- and
    $M$-independent Lévy ceiling on low windows; shift-adapted Young weights give
    $Q(g_{\text{low}}+g_{\text{high}})\ge Q(g_{\text{low}})+Q(g_{\text{high}})-2C\sqrt{E_{\text{low}}E_{\text{high}}}$.
16. **Full-form stability.** $R_f-R_g=\int(f-g)[f(\cdot+t)+g(\cdot-t)]$ controls every channel in
    $L^1$ distance with explicit value/slope moments: one accuracy index pays for arbitrary tents.
17. **Receiver transfer.** Channel-by-channel parity split on $C_c$; $(\alpha,\beta)$-norm-controlled
    subfamilies transfer a floor $-Ce^{2\sigma r}$ to width $\le\sigma+\beta$; grid tents are
    $(1,0)$-controlled.
18. **Period difference detector.** $f-f(\cdot-L)$ multiplies the Weil summand at a lattice point
    $\tfrac12+\delta+2\pi ik/L$ by $-2(\cosh\delta L-1)$: annihilates on-line points, makes every
    off-line depth negative, reduces clusters to finite sums.
19. **Syndetic Bohr–Kronecker alignment.** Kronecker density + Bohr almost-periodicity: every
    prime-phase pattern is approximated on a height set with bounded gaps.

---

## 5. Pillar theorems

1. **Reflection identity** $\mathcal Z-\Re\mathcal W=\mathcal R$ (`configurationSquareMass_sub_re_W_eq_reflectionDefect`).
2. **Logarithmic sampling**, sharp; corrected source one log cheaper
   (`exists_factorialTail_raw_and_smoothed_zeroSquare_bound`, `factorialCorrected_zeroSquare_le`).
3. **Sharp Krein stability radius** (`relative_stability_factor_pos_iff`, `schur_binary_quadratic_nonneg_iff`).
4. **High-scale span coercivity** (`factorialTailSpan_re_W_coercivity`).
5. **Critical prime kernel negative definite**: $P_\infty(b)\le-\frac4{7000\pi^4}\sum b_j^2$ with exact
   Rayleigh range; actual prime form negative definite on linear windows $[N,(1+\delta)N]$
   (`factorialCriticalTranslatedPrimeLimit_le_neg_energy`, `isGLB_factorialCriticalPrimeRayleighSet_exact`,
   `exists_fullLinearWindowSupport_criticalPrimeEnergy_neg_definite`).
6. **…and not beyond.** The dyadic pair $\{M-1,2M-1\}$ has prime limit $\ge\tfrac18\log2/\pi^4>0$, so
   negative semidefiniteness fails on dyadic blocks, windows with $L\ge2$, linear windows with
   $\delta\ge1$, polynomial windows and all scales (`tendsto_criticalPrimeEnergy_dyadicPair`,
   `not_criticalPrimeEnergy_nonpos_of_dyadicBlock`, `not_criticalPrimeEnergy_nonpos_all_scales`).
7. **Archimedean domination**: critical energy of translates $\to+\infty$, uniformly in coefficients
   on fixed support (`tendsto_criticalTranslatedCompleteEnergy_top`).
8. **$\ell^2$-uniform prime channel** on dyadic blocks, uncollared (`abs_criticalPrimeEnergy_le_of_dyadic`,
   `abs_integral_weight_realPhaseCombination_dilate_le`, `windowRingMajorant_bounds`).
9. **Positivity at every support length**: high blocks, polynomial windows, compact truncations
   uniformly in $V$, lacunary unions of windows, dense two-band windows, coupled low–high families,
   all five names, down to the zeta divisor $\mathcal R(F)+\tfrac{s_T}8\log M\sum b^2\le\mathcal Z(F)$
   (`exists_criticalCompleteEnergy_pos`, `exists_lacunaryPolynomialWindows_all_five_forms_pos`,
   `coupled_low_high_pos_for_unrestricted_low_modes`, `exists_smooth_actual_zeta_reflection_coercivity_of_compact_window`).
10. **Scale-free Schur complement** (`compactFullWeilEnergy_criticalTruncatedTest_schur_sqrt`,
    `compactFullWeilEnergy_pos_of_lowMode_certificate_and_schur_complement`).
11. **Tent completeness**: RH ⇔ all finite tent patterns ≥ 0 ⇔ grid patterns eventually ≥ 0 ⇔
    bounded-below odd grid floor; finite-scale error $O(d_{n+1})$ in all five names
    (`riemannHypothesis_iff_factorialTentPattern_nonneg`, `riemannHypothesis_iff_bddBelow_gridTentPattern_odd_floor`,
    `abs_zeta_W_re_sub_gridTentPattern_re_add_im_le`).
12. **Receiver ledger, rate ½**: odd $Q(F)$ = archimedean budget $-\int_0^{2r}Ew_F$; elementary, PNT
    and de la Vallée Poussin bounds give floors $-78e^r$, $-(8+\varepsilon)e^r$, $-Ke^{r-c\sqrt r}$,
    all rate ½ (`compactFullWeilEnergy_eq_reflectedPrimePolar_and_chebyshev_ledgers`,
    `compactFullWeilEnergy_and_gridTent_ge_neg_seventy_eight_mul_exp`).
13. **Detection**: every off-line zero, finite cluster, depth-gap zero and attained top is seen by
    grid tents at explicit aperture; eventual grid-tent nonnegativity on $[-R,R]$ excludes depth
    $\ge1/R$ below an explicit cluster horizon (`zeta_excluded_depth_below_clusterHorizon_of_gridTentPattern_nonneg`).
14. **Selectivity boundary**: wide shift pairs refute $\zeta(s-a)\zeta(s+a)$ for every $a\ne0$;
    every tempered weight $|w|\le C\Lambda$ (Liouville twist, node deletions) is uniformly positive
    on the critical family; at fixed truncation every weight is (`exists_wide_shiftPair_shiftedPairVonMangoldt_neg`,
    `exists_temperedWeight_polynomial_window_weilFullFunctional_pos`, `exists_fixedV_polynomial_window_pos_for_any_weight`).
15. **Admissible weights**: all mechanisms hold for `AdmissibleHarmonicWeight` ($|w_k|\le C/k^2$,
    $\sum_{k\ge2}|w_k|\le\tau<1$); cell-kernel sign trichotomy: $\chi\ge0$ ⇒ $R_\chi>0$, dyadic-type
    sign flips ⇒ $R_\chi<0$ (`exists_generalTruncatedCompleteEnergy_and_receiver_pos`,
    `generalCriticalPrimeContinuousRealKernel_pos_of_nonneg_charge`, `exists_nonDyadic_stencil_negative_definite_cellKernel`).
16. **No height-eventual power saving**: syndetic prime-phase realisation forbids
    $P_X(\tau)\ge-(c\sqrt X+C)$ with $c<2$ and any $X^{\theta/2}$, $\theta<1$, saving eventually in
    height, even after smooth $C^2$ convolution; a power saving at the single height of a zero
    forces an off-line companion (`not_exists_eventually_atTop_PX_power_saving`,
    `not_exists_eventually_atTop_endpointPair_power_saving`, `zeta_single_height_power_saving_forces_offLine_companion`).
17. **Sonin cutoff dichotomy**: at $\Lambda=1$ trace domination fails on odd mean-zero pole-free
    tests with infinite negative index, unrepairable by finitely many moments; at each $\Lambda>1$
    separated packets satisfy it uniformly in coefficients (`ccmSonin_cutoff_one_vs_gt_one_dichotomy`).
18. **Suzuki common shift**: a source-independent first-variation envelope gives one smoothing
    index and one shift interval for whole blocks; graded odd small-shift deficits ⇔ width bounds
    (`abs_suzukiCriticalSourcePairing_firstVariation_sub_le`, `riemannHypothesis_iff_suzuki_small_shift_non_overshoot`).

---

## 6. Traps

| Trap | Why it fails |
|---|---|
| Cauchy–Schwarz on $\mathcal W$ | Needs $\mathcal W\ge0$; use $\sqrt{\mathcal Z(f)\mathcal Z(g)}$ |
| Sign from self-adjointness, ground states, finite index | None excludes negative ground energy |
| $g\to|g|$ keeps the Markov gain | It changes the pole plane |
| $H^1$ bounds uniform in smoothing; $O(1/N)$ tail sampling | Endpoint jump: only $\int D(h)dh/h$ is uniform; $\mathcal Z\asymp\log N/N$ |
| Physical Riesz bounds = spectral coercivity | Missing $\log N$ and low-band exclusion |
| Bohr orthogonality ⇒ uniform decoupling | Prime-thirteen family: gaps → 0, correlation → 1 |
| Divergent $\sum\Lambda(r)/r$ at $\beta=\tfrac12$ ⇒ negative energy | Only the absolute majorant fails |
| Harmonic signs decide the total | Masses $J_m(b)$ are coupled; the Poisson-closed kernel decides |
| Negative prime channel = negative form | The form subtracts primes: it is a subsidy |
| Linear-window negativity extends to blocks/windows | False: the dyadic pair resonance makes it positive at ratio 2 |
| Fixed-support "eventually in $n$" is uniform | Threshold depends on $S$; use dyadic blocks/linear windows |
| $\ell^1$ admission bound transfers to $\ell^2$ | Needs dilation inequality + Montgomery–Vaughan for the jump |
| Compact support of any length is the receiver regime | Margin is still $\log M$; long support removes the short-support objection only |
| Coupled low–high positivity settles low scales | The isolated low window is not proved positive |
| Fixed-$V$ window positivity is selective | Every weight passes at fixed $V$; selectivity is uniformity in $V$ |
| Window through $3/10$ is about $\zeta$ | No prime power enters ($\log2>3/5$) |
| A better constant in the rate-½ floor | $78$, $8+\varepsilon$, dlVP all keep rate ½; progress is an exponent |
| Archimedean boost of exponent $\theta>1/4$ | The all-ones weight then passes; the criterion is destroyed |
| Larger aperture is free | $\ell^1$ cost $e^a$ vs depth amplification $e^{2\delta a}$: floors at width ½ |
| Uniform-in-height prime saving | Syndetic Kronecker alignment forbids it, even eventually in height |
| Model detection = zeta sign | Lattice-plus-pair model has no Euler product; it calibrates |
| Common Suzuki shift = Suzuki sign | Paid by $\log M$; needs a graded odd receiver deficit |
| Zero-density bounds exclude a zero | They are counts; one fixed off-line zero survives |
| Renaming an RH-equivalent cone/metric as a hypothesis | Arithmetic work unchanged |

---

## 7. Open problems

1. **Isolated low window.** Prove $Q(g^V_{\text{low}})\ge\mu E_{\text{low}}$, $\mu>0$, on
   $[1,L_{\text{low}}]$ without high-scale coupling. By the Schur complement this is all that
   separates the critical family from positivity on the full product space. The archimedean gain
   is bounded there, so the certificate must come from arithmetic channels.
2. **Receiver without subsidy: beat rate ½.** Prove a floor $-Ce^{2\sigma r}$ with $\sigma<\tfrac12$
   on odd receiver tests, i.e. cancellation inside $\int_0^{2r}E(s)w_F(s)ds$ between the prime
   measure and the polar density $2\cosh(t/2)$. A margin growing with test frequency is not a
   weaker version: the all-ones weight satisfies it.
3. **Single-height phase-selective saving.** Height-uniform and height-eventual power savings are
   impossible (pillar 16). What survives: a saving at the specific height of a hypothetical zero,
   or in measure (bad heights carry weight $O(X^{-\theta}(\log X)^2)$). Which arithmetic input
   uses the actual height-dependent phases? Mean-square counterpart: TransThresholdPairCorrelation.
4. **Quantitative detection horizon.** Replace $\exp(R/(10^5A_0\log^2R))$ by a doubly exponential
   horizon unconditionally (currently needs `OffLineCopiesLocallyBounded`).
5. **Critical prime channel across scales.** Negativity holds on linear windows and fails at ratio
   2. Open: lacunary unions of narrow windows (needs polynomial uncollared cross-block decay
   despite the $1/f$ jump transform), and the exact sign structure of commensurable ratio pairs.
6. **Beyond admissible stencils.** Can a multi-scale stencil with $\chi(2)<0$ make $R_\chi<0$ and
   cancel the low-scale polar pair without archimedean subsidy?
7. **Selectivity that controls the form.** Which source mechanism separates $\Lambda$ from tempered
   perturbations while controlling the complete form at arbitrary aperture? Node-deletion and
   narrow-pair diagnostics identify, but do not sign.
8. **Positive spectral realisation.** A source space and topology carrying a positive realisation
   strong enough for receiver transfer; the $\Lambda>1$ packet theorem still lacks receiver
   transfer; real-rooted ground states need cofinal Gaussian growth or Poisson balance bounds.
9. **From identification to sign.** For the identified source, prove one additional estimate:
   aperture-uniform odd floor, a subexponential one, or prime-power deletion slack.
10. **Suzuki at the critical boundary.** Control critical-decay families without the $\beta>\tfrac12$
    margin; get a graded odd-receiver deficit with exponent below ½.

---

## 8. Tools

Built: clock calculus; zero-divisor sampling; independent comparison form + Krein radius;
nonstationary Mellin exclusion and admissible-source law; dilation calculus (dyadic dilation
inequality, MV jump bound, ring majorant, cross-block couplings); critical kernel calculus
(divisor charge, Poisson closure, Toeplitz symbol, curvature constant); linear-window limit
comparison; commensurable scale-ratio correlation limits; full-form stability; parity split and
norm-controlled receiver transfer; quantitative grid-tent detection; scale-free Schur complement;
`AdmissibleHarmonicWeight` calculus; `TemperedPrimeWeight` transfer; syndetic Bohr–Kronecker
height sets; Suzuki first-variation envelope.

To build: a low-window certificate from arithmetic channels; a norm-controlled transfer that does
not consume $\log M$; a prime–polar cancellation estimate for $\int Ew_F$ below rate ½; an
uncollared cross-block decay law strong enough for multi-window negativity.

---

## 9. Working conventions

- Readouts are `paperFT f (gammaOf s)`; zero divisor `zetaZeroConfig.carrier`/`.mult`; only the strip.
- Prove summability before `tsum`; state nested eventual quantifiers explicitly (`∃ M₀ ∀ V` vs `∀ V ∃ M₀`).
- Divergent energies live in `EReal`; arithmetic-channel finiteness is separate.
- Use offsets `n+1`, `DyadicScaleBlock S M`, `ScaleWindow S M L`. Name constants.
- Capstones take data only; RH appears in conclusions or equivalences.
- Search all five names before proving a new identity. Report partial results as rates or strips.
