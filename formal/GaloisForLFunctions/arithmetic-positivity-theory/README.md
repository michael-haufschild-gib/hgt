# Arithmetic Positivity Theory (APT)

Namespace `GaloisForLFunctions.ArithmeticPositivityTheory`; umbrella `ArithmeticPositivityTheory.lean`;
sources in `arithmetic-positivity-theory/`.

**Question.** Which independently checkable features of an exact arithmetic source control the
sign, the mixed couplings and the stability of the complete Weil form of $\zeta$? Sources keep
literal $\Lambda$-weights, divisor identities, Bernoulli sawtooth remainders, endpoint jumps,
collar shifts, Gamma factors and poles. Positivity is proved on a stated family at a stated scale.
RH appears only in conclusions and equivalences.

**Central finding.** Positive families exist at every support length, but every positivity is paid
for by an archimedean gain $\log M$. The gap to RH is removing that subsidy.

---

## 1. Place in the research

APT is the **source theory of the complete Weil form**: it supplies literal sources, complete-form
approximation and receiver transfer. The other coordinates of the same form (pair incidence, lag,
aperture) live elsewhere.

| Programme | Interface |
|---|---|
| BiScaleUncertainty | Factorial Müntz sources, signed prime–polar domain, selectivity countermodels |
| SquareRootThreshold | Zero configurations, width–floor dictionary, single-height aperture |
| ArithmeticCriticalityTheory | Ground-energy path, Markov/pole split, small-aperture gauges |
| ArithmeticIncidencePositivity | Pair conductances, pole-plane balance $\sum\Lambda h-\int(e^s+1)h$ |
| ArithmeticCastelnuovoSeveri | Polar-box DoF minus prime node count $=E(s)$ |
| ArithmeticCompensationTheory | Why adapted norms restate the target |
| ScaleSignedIncidenceCriticality | Whether the data a proof reads separate target from countermodels |
| TransThresholdPairCorrelation | Mean-square counterpart of the single-height prime saving |
| ArithmeticOrientationTheory | Width dictionary; the factorial family as calibration library |
| `RHTower` (`Suzuki/`, CCM) | Explicit formula, zero divisor, Suzuki source, Sonin/CCM operators |

Consumers: linear-window negativity of the critical prime channel feeds signed prime scheduling;
window/lacunary positivity and receiver transfer feed the even pole-weight route; the critical
family is the Suzuki test class.

**Transfer criteria** (apply to every new law):

- *Selectivity:* a law also satisfied by $\zeta(s-a)\zeta(s+a)$, Beurling off-line systems or
  Liouville-twisted weights is infrastructure only.
- *No archimedean subsidy:* a $\log M$ or $\log(1/w)$ gain against bounded prime cost is
  nonselective; a frequency-growing subsidy admits the all-ones weight. Constant or linear
  aperture losses are harmless.
- *Grading:* a floor $-C_\sigma e^{2\sigma r}$ at aperture $r$ gives zero width $\le\sigma$; an
  aperture-uniform floor gives RH; width $<\beta$ gives the rate-$2\beta$ floor
  (`exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt`, SquareRootThreshold).

---

## 2. Why: the receivers

Exact identities never supply a sign. Self-adjoint realisations, Krein involutions and ground
states have eigenvalues of both signs; positivity of one piece (archimedean jump integral, Markov
part) says nothing about the whole; Cauchy–Schwarz on $\mathcal W$ needs $\mathcal W\ge0$ first.
The arithmetic must pay, and on explicit families it can, through quantities measurable without
zero locations: physical square mass, translation energy, an independent zero-sampling form,
harmonic separation of collar frequencies, oscillatory cancellation under prime dilation.

**Two RH-equivalent receivers.**

1. *Critical-scale cancellation.* $D(T)=\int_0^T(e^t-\psi(e^t))dt$; a one-sided bound
   $D(T)\le B(1+T)e^{T/2}$ for all $T$ is RH.
2. *Capacity inequality.* For real compact $C^2$ tests and prime aperture $N$ beyond the support,
   $\mathcal W(g)=\mathcal M_N(g)+\tfrac12C(g)^2-\tfrac12S(g)^2$, $\mathcal M_N=V_N\|g\|^2+J_{\rm L\acute evy}+J_{{\rm prime},N}$,
   $V_N=\Omega(0)-2\sum_{m\le N}\Lambda(m)/\sqrt m$, $C=\int2\cosh(u/2)g$, $S=\int2\sinh(u/2)g$.
   RH iff $S^2\le2\mathcal M_N+C^2$ for all tests.

**One functional.** Abel summation against the pole density $e^s+1$: for $C^1$ lag weights $h$
vanishing beyond the horizon, $\sum\Lambda(n)h(\log n)-\int_0^\infty(e^s+1)h=-\int_0^\infty(D(s)+s^2/2-s)h''$.
On a test of aperture $r$, prime channel minus pole plane $=\int_0^{2r}E(s)w_F(s)ds$ with the
**two-pole Chebyshev defect** $E(s)=e^s+s-1-\psi(e^s)$ and lag weight
$w_F(s)=2e^{-s/2}(\int FF'(\cdot+s)-\tfrac12a_F(s))$. The reflected pole is the source of $(1+T)$.

**One laboratory.** Principles are calibrated on the *factorial correction tail*: noncompact, an
endpoint jump, a shrinking irrational collar, readouts holomorphic only on $\Re s>-1$. A mechanism
must reproduce a known positive case and fail honestly on a known obstruction.

---

## 3. Objects and language

### Zero side
Readout $F_f(s)=\int f(x)e^{(s-1/2)x}dx$ (`paperFT f (gammaOf s)`); zeros $\rho$ with multiplicity
$m_\rho$, strip only:
$\mathcal Z(f)=\sum m_\rho|F_f(\rho)|^2$, $\mathcal W(f,g)=\sum m_\rho F_f(\rho)\overline{F_g(1-\bar\rho)}$,
$\mathcal R(f)=\sum\tfrac{m_\rho}2|F_f(\rho)-F_f(1-\bar\rho)|^2$.
**Reflection identity** $\mathcal Z-\Re\mathcal W=\mathcal R$ for every configuration;
$|\mathcal W(f,g)|\le\sqrt{\mathcal Z(f)\mathcal Z(g)}$. Lean: `zetaZeroSquareMass`, `zetaZeroConfig.W`,
`configurationReflectionDefect`.

### Physical side
$Q(g)=\frac1{2\pi}\int|\hat g|^2\Omega+2\Re(\hat g(i/2)\overline{\hat g(-i/2)})-T_\Lambda(g\star\tilde g)$
(the form *subtracts* primes). Gamma–Lévy channel $\Omega(0)a_g(0)+\int_0^\infty(a_g(0)-a_g(x))\omega(x)dx$,
$\omega(x)=e^{x/2}/\sinh x$; prime channel $2\sum\Lambda(r)r^{-1/2}a_g(\log r)$. Taken in `EReal`
(divergent archimedean energy $=+\infty$); arithmetic channels are proved finite separately.

**Five names, one form.** On continuous compact real sources `compactFullWeilEnergy` =
`fullZeroForm` (ArithmeticCriticalityTheory) = $\Re$ `weilFullFunctional` (RHTower); on $C^2_c$ also
$\Re\mathcal W=\mathcal Z-\mathcal R$ for `zetaZeroConfig`. Search all five before proving an identity.

### Factorial family
| Object | Definition | Lean |
|---|---|---|
| Clamped kernel | $C(u)=\{u\}(1-\{u\})/2$ | `clampedLatticeRemainder` |
| Dyadic filter | $P=\tfrac14C(4u)-2C(2u)+4C(u)$; $P-\tfrac3{16}=-\tfrac2{\pi^2}\sum\chi(k)k^{-2}\cos2\pi ku$, $\chi=1,-1,0$ for $k$ odd, $\equiv2$, $\equiv0\ (4)$ | `dyadicBernoulliFilter`, `dyadicHarmonicChi` |
| Harmonic weight | $w_k=\chi(k)/k^2$; $\sum_{k\ge2}|w_k|\le3/4$ (first-harmonic dominance) | `dyadicHarmonicWeight` |
| Collar | $(1+\varepsilon_N)^3=1+\tfrac1{4N}$, $\lambda_N=N(1+\varepsilon_N)$, $\delta_N=\lambda_N-N\in[\tfrac1{15},\tfrac1{12}]$ | `sourceFactorialCollar`, `factorialShiftedFreq` |
| Affine clock | $12N+1$; $e_N=N+\tfrac1{12}-\lambda_N$, $Ne_N\to1/144$ | `factorialAffineDefect` |
| Phase profile | $\Phi_N(v)=P(\lambda_Nv)-P(Nv)$ | `factorialPhaseProfile` |
| Correction tail / source | $T_n=a_ne^{3x/2}\Phi_N(e^{-x})\mathbf1_{x\le0}$; $H_n=r_n+T_n$, readout $c_n/\rho$ | `factorialMuntzCorrectedTail`, `factorialMuntzBoundaryCorrected` |
| Span test | $f_b=e^{3x/2}\sum b_N\Phi_N(e^{-x})\mathbf1_{x\le0}$ | `factorialSpanTest` |
| Critical source | envelope $\beta=\tfrac12$: $g_b=\mathbf1_{x\le0}e^{x/2}F_b(e^{-x})$; collared $g^c_b$; truncated $g^V$ compact in $[-\log2V,0]$ | `criticalFactorialSource`, `criticalCollaredSource`, `criticalTruncatedSource` |
| Scale sets | $M\le n+1\le2M$; window $[M,LM]$ | `DyadicScaleBlock`, `ScaleWindow` |
| Tents | causal hat of width $w_{n+1}$ times $e^{3x/2}$; grid pattern = PL interpolant of nodal data | `factorialSourceRight`, `gridTentPattern` |

**Envelope table.** $\beta>\tfrac12$: prime majorant summable; $\beta=\tfrac12$: absolute bound
diverges but the oscillatory majorant $\Lambda(r)/(r^{\beta+1/2}(r-1))$ converges for $\beta>-\tfrac12$.
The critical line is a failure of the absolute bound, not of the prime channel.

### Critical-scale kernel
| Object | Definition |
|---|---|
| Divisor charge | $A(m)=\chi(m)\sum_{d\mid m}d\Lambda(d)\chi(m/d)$; $A(2)=-2\log2$ is the unique negative value |
| Cumulative charge | $H_N=\sum_{m\le N}A(m)/m^3$, negative exactly for $2\le N\le4$ |
| Band weight | $\gamma(u)=2\sin^2(\pi u/12)/u^2$, $\sum_z\gamma(t+z)=\pi^2/6$ |
| Cell kernel / coupling | $R(t)=\tfrac12(K(t)+K(1-t))$, $K=\sum_jH_j\gamma(j+\cdot)$; $\kappa(k)=\int_0^1R\cos2\pi kt$ |
| Limiting prime form | $P_\infty(b)=\frac4{\pi^4}\sum b_ib_j\kappa(|i-j|)$ |

Lean prefixes: `factorialCritical*`, `criticalBand*`, `criticalPrimeEnergy`, `criticalCompleteEnergy`.
General stencils: `AdmissibleHarmonicWeight` ($|w_k|\le C/k^2$, $\sum_{k\ge2}|w_k|\le\tau<1$).

---

## 4. Mechanisms

1. **Exact compression.** $\sum_{d\mid k}\Lambda(d)=\log k$ collapses prime rectangles; Bernoulli
   stencils cancel the constant mode. Drift-free stencils on $\{1,q,q^2\}$ are classified.
2. **Regularity through the clock** $v=e^{-x}$. Translation energy $D(h)\le C\min(N^{-1},h)$, so
   $\int_0^1D(h)dh/h\le C(1+\log N)/N$; the log is the price of the endpoint jump.
3. **Gamma–Lévy transport.** Lévy symbol $\ge e^{-1/2}(\log|t|-3)$: small low-band spectrum plus
   nonzero mass forces log-growth of Lévy energy (admissible-source law).
4. **Zero-divisor sampling without zero locations.** Half-plane subharmonicity on radius-$\tfrac14$
   disks + multiplicity-exact overlap $O(\log|\Im s|)$ ⇒ $\mathcal Z(T_n)\le C(1+\log N)/N$, sharp.
5. **Independent comparison form.** Transfer through $\mathcal Z$, never $\mathcal W$; positive iff
   $\varepsilon<(\sqrt{1+\delta}-1)^2$ (sharp Krein radius); binary Schur law $M^2\le4AD$.
6. **Rank-one pole readout.** Corrected sources span one zero-side dimension; cross-scale
   positivity is decided on the pole-free hyperplane.
7. **Nonstationary Mellin exclusion.** Readout $\le D\sum|b_N|/N$ on $|t|\le\pi M$; archimedean
   weight outside is $\ge\log M$ ⇒ span coercivity $\Re\mathcal W(f_b)\ge(\tfrac A2\log M-C)\sum|b_N|^2$.
8. **Parity decoupling.** $C$ vanishes on odd, $S$ on even tests: odd tests carry the whole
   anti-Markovian risk.
9. **Collar arithmetic.** $|a\lambda_N-b\lambda_M|<\tfrac1{15}\iff a(12N+1)=b(12M+1)$; family
   $N=13M+1$ has gaps $\to0$, so uniform cross-scale oscillatory gain is false. Baker separates
   the cubic collar spectrum from prime logarithms.
10. **Critical kernel calculus.** Only dilation resonances $k=rl$ survive (atoms at $\log(p/q)$).
    Poisson closure makes $R$ near-constant: $R\le-1/7000$, $\kappa(k)\sim I_0/(4\pi^2k^2)>0$, exact
    Rayleigh range.
11. **Commensurable scale-ratio law.** At ratio $2{:}1$ the first harmonic of the $r=2$ cross term
    is $+(\log2/\pi^4)J_2$, cancelling the unique negative harmonic exactly.
12. **Dilation calculus.** Schur test gives the dyadic dilation inequality; the jump kernel is paid
    by Montgomery–Vaughan; window ring majorant $\sum\frac{\Lambda(r)}r\min(1,\sqrt{L/r})=\log L+O(1)$.
13. **Scale-free Schur complement.** $Q(g_{\rm low}+g_{\rm high})\ge Q(g_{\rm low})+Q(g_{\rm high})-2C\sqrt{E_{\rm low}E_{\rm high}}$
    with $V$- and $M$-independent $C$.
14. **Full-form stability.** $R_f-R_g=\int(f-g)[f(\cdot+t)+g(\cdot-t)]$ controls every channel in
    $L^1$; one accuracy index pays for arbitrary tents.
15. **Receiver transfer.** $(\alpha,\beta)$-norm-controlled subfamilies transfer a floor
    $-Ce^{2\sigma r}$ to width $\le\sigma+\beta$; grid tents are $(1,0)$-controlled.
16. **Period difference detector.** $f-f(\cdot-L)$ multiplies the Weil summand at
    $\tfrac12+\delta+2\pi ik/L$ by $-2(\cosh\delta L-1)$: kills on-line points, makes off-line depth negative.
17. **Syndetic Bohr–Kronecker alignment.** Every prime-phase pattern is approximated on a height
    set with bounded gaps.

---

## 5. Pillar theorems

1. **Logarithmic sampling, sharp** (`exists_factorialTail_raw_and_smoothed_zeroSquare_bound`).
2. **High-scale span coercivity** (`factorialTailSpan_re_W_coercivity`).
3. **Critical prime kernel**: negative definite on linear windows $[N,(1+\delta)N]$, not on dyadic
   blocks or any wider family (dyadic pair limit $\ge\tfrac18\log2/\pi^4$)
   (`exists_fullLinearWindowSupport_criticalPrimeEnergy_neg_definite`, `not_criticalPrimeEnergy_nonpos_of_dyadicBlock`).
4. **Positivity at every support length**, in all five names, paid by $\log M$
   (`exists_lacunaryPolynomialWindows_all_five_forms_pos`, `coupled_low_high_pos_for_unrestricted_low_modes`).
5. **Tent completeness**: RH ⇔ all finite tent patterns $\ge0$ ⇔ bounded-below odd grid floor
   (`riemannHypothesis_iff_factorialTentPattern_nonneg`, `riemannHypothesis_iff_bddBelow_gridTentPattern_odd_floor`).
6. **Receiver ledger is rate ½**: odd $Q(F)=-\int_0^{2r}Ew_F$; elementary, PNT and dlVP inputs all
   give floors $\asymp-e^r$ (`compactFullWeilEnergy_eq_reflectedPrimePolar_and_chebyshev_ledgers`).
7. **Selectivity boundary**: wide shift pairs refute $\zeta(s-a)\zeta(s+a)$; every tempered weight
   $|w|\le C\Lambda$ is positive on the critical family; at fixed truncation every weight is
   (`exists_wide_shiftPair_shiftedPairVonMangoldt_neg`, `exists_fixedV_polynomial_window_pos_for_any_weight`).
8. **No height-eventual power saving** of the prime polynomial; a saving at the single height of a
   zero forces an off-line companion (`not_exists_eventually_atTop_PX_power_saving`,
   `zeta_single_height_power_saving_forces_offLine_companion`).
9. **Sonin cutoff dichotomy**: at $\Lambda=1$ infinite negative index; each $\Lambda>1$ separated
   packets satisfy trace domination (`ccmSonin_cutoff_one_vs_gt_one_dichotomy`).

---

## 6. Traps

| Trap | Why it fails |
|---|---|
| Cauchy–Schwarz on $\mathcal W$ | Needs $\mathcal W\ge0$; use $\sqrt{\mathcal Z(f)\mathcal Z(g)}$ |
| Sign from self-adjointness / ground states / finite index | None excludes negative ground energy |
| $g\to|g|$ keeps the Markov gain | It changes the pole plane |
| $H^1$ bounds uniform in smoothing; $O(1/N)$ tail sampling | Endpoint jump: $\mathcal Z\asymp\log N/N$ |
| Physical Riesz bounds = spectral coercivity | Missing $\log N$ and low-band exclusion |
| Bohr orthogonality ⇒ uniform decoupling | Prime-thirteen family: gaps → 0 |
| Divergent $\sum\Lambda(r)/r$ at $\beta=\tfrac12$ ⇒ negative energy | Only the absolute majorant fails |
| Harmonic signs decide the total | Masses are coupled; the Poisson-closed kernel decides |
| Negative prime channel = negative form | The form subtracts primes: a subsidy |
| Linear-window negativity extends | Dyadic-pair resonance makes it positive at ratio 2 |
| Fixed-support "eventually in $n$" is uniform | Threshold depends on $S$ |
| Compact support of any length is the receiver regime | Margin is still $\log M$ |
| Coupled low–high positivity settles low scales | The isolated low window is unproved |
| Fixed-$V$ positivity is selective | Every weight passes; selectivity is uniformity in $V$ |
| A better constant in the rate-½ floor | Progress is an exponent, not a constant |
| Archimedean boost of exponent $\theta>1/4$ | The all-ones weight passes |
| Larger aperture is free | $\ell^1$ cost $e^a$ vs depth amplification $e^{2\delta a}$ |
| Uniform-in-height prime saving | Syndetic Kronecker alignment forbids it |
| Model detection = zeta sign | Lattice-plus-pair model has no Euler product |
| Zero-density bounds exclude a zero | They count; one fixed off-line zero survives |
| Renaming an RH-equivalent cone/metric as a hypothesis | Arithmetic work unchanged |

---

## 7. Open problems

1. **Isolated low window.** $Q(g^V_{\rm low})\ge\mu E_{\rm low}$ on $[1,L_{\rm low}]$ without
   high-scale coupling. By the Schur complement this is all that separates the critical family
   from positivity on the full product space; the certificate must be arithmetic (archimedean gain
   is bounded there).
2. **Beat rate ½ without subsidy.** A floor $-Ce^{2\sigma r}$, $\sigma<\tfrac12$, on odd receiver
   tests: cancellation in $\int_0^{2r}Ew_F$ between the prime measure and $2\cosh(t/2)$.
3. **Single-height phase-selective saving.** Which arithmetic input uses the actual
   height-dependent phases at the height of a hypothetical zero (or in measure)? Mean-square
   counterpart: TransThresholdPairCorrelation.
4. **Quantitative detection horizon.** Doubly exponential horizon unconditionally (currently needs
   `OffLineCopiesLocallyBounded`).
5. **Critical prime channel across scales.** Lacunary unions of narrow windows (polynomial
   uncollared cross-block decay despite the $1/f$ jump); sign structure of commensurable ratios.
6. **Beyond admissible stencils.** Can $\chi(2)<0$ stencils make $R_\chi<0$ and cancel the low
   polar pair without subsidy?
7. **Selectivity that controls the form** at arbitrary aperture (node-deletion and narrow-pair
   diagnostics identify, but do not sign).
8. **Positive spectral realisation** strong enough for receiver transfer; the $\Lambda>1$ packet
   theorem lacks it.
9. **Suzuki at the critical boundary**: graded odd-receiver deficit with exponent below ½ without
   the $\beta>\tfrac12$ margin.

## 8. Tools to build

Low-window certificate from arithmetic channels; norm-controlled transfer not consuming $\log M$;
prime–polar cancellation for $\int Ew_F$ below rate ½; uncollared cross-block decay strong enough
for multi-window negativity.

## 9. Conventions

- Readouts `paperFT f (gammaOf s)`; zero divisor `zetaZeroConfig.carrier`/`.mult`; strip only.
- Summability before `tsum`; state nested eventual quantifiers explicitly (`∃ M₀ ∀ V` vs `∀ V ∃ M₀`).
- Divergent energies in `EReal`; offsets `n+1`, `DyadicScaleBlock S M`, `ScaleWindow S M L`; name constants.
- Report partial results as rates or strips.
