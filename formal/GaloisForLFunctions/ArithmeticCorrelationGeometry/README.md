# Arithmetic Correlation Geometry (ACG)

Namespace `GaloisForLFunctions.ArithmeticCorrelationGeometry`; umbrella `ArithmeticCorrelationGeometry.lean`; 27
modules. All results unconditional; RH appears only inside proved equivalences.

## 1. Motivation

Multiplicative observation of a source has a symmetry group: the **gauge torus** $G=(\mathbb R/\mathbb Z)^{\text{primes}}$ of
completely multiplicative unimodular twists. Every statistic built from product coincidences is constant on gauge orbits;
every additive relation (successor, $ab-cd=h\neq0$, affine maps with $b\ne0$) has gauge mean zero. ACG makes this the
organising fact: square-root laws (RH, Chowla) hold at Haar-almost every gauge point, fail at explicit twins, and at the
point $0$ (the actual source) are the conjectures. It asks where a sign specific to $\zeta$ can come from once
multiplicative information is exhausted.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Gauge torus, Haar | `GaugeTorus`, `gaugeHaar` | one phase per prime |
| Twist | `twist`, `twisted` | $\chi_x(n)=\prod_pe(x_pv_p(n))$; $(\chi_xa)(n)$ |
| Archimedean point | `archPoint` | $\chi(n)=n^{2\pi i\xi}$: the height line in $G$ |
| Dirichlet gauge point | `dirichletGauge` | $\chi\bmod q$ as a gauge point (values at $p\mid q$ reset) |
| Sign twist | `primeSignTwist` | 2-torsion of $G$ on a finite prime set |
| Pair form | `pairForm` | $\sum w(m,n)\chi(m)\bar\chi(n)$ |
| Successor correlation | `succCorr` | $C_h(a)=\sum a_n\bar a_{n+h}$ |
| Near-incidence form | `nearIncidence` | off-diagonal of a windowed mean square, kernel $k_\eta(\log j-\log k)$ |
| Fourfold incidence | `fourfoldIncidence` | $\sum_{ab=cd+h}\alpha_a\alpha_b\overline{\alpha_c\alpha_d}$ |
| Twisted coalescent sum | `twistedPrimeCoalSum` | coalescent prime pair form; $x=0$ is `primeCoalSum` |
| Escaped pairing / mass | `escapedPairing`, `escapedMass` | pairing on cells absorbed by an affine map on $\{0..N\}$ |
| Charged boundary | `chargedBoundary` | escaped tail of a gauge-charged source at weight σ |
| Asymptotic kernel | `asymKernel` | $\inf_d$ of dilated critical Grams $\sqrt{jk}K(dj,dk)$ |
| Gauge mass | `gaugeMass` | $\tilde K_\infty(1,1)=\inf_dd\,K(d,d)$ |
| Zero term | `zeroTerm` | $Z(\tau)=\int g\,e^{\delta x}\cos((\tau-\gamma)x)$ |
| Twin tail | `twinTail` | keep $x_0$ on finite $I$, phase ½ on all other primes |
| Twisted Mertens / Chebyshev | `moebiusGaugeSum`, `twistedPsi` | $\sum\mu\chi_x$, $\sum\Lambda\chi_x$ |

## 3. Language

- **Gauge invariant / gauge charged**: monomial $\prod a(m_i)\prod\bar a(n_j)$ is invariant iff $\prod m_i=\prod n_j$, else mean 0.
- **Gauge point of a source**: the actual source is $x=0$; its twists share all multiplicative data.
- **Stabilizer** of a pair: subgroup fixing it; at level $q$ successor pair $(n,n+h)$ is fixed iff $q\mid h$.
- **Coalescent**: pair not resolved by the archimedean line at the given height.
- **Typical**: outside a Haar-null exceptional set. **Twin**: an explicit atypical orbit point (Liouville, twin tails).
- **Loss law**: growth $b_k$ of an order-$k$ multiplicative bound; sublinear is what amplification needs.
- **Escape state**: common cofactor Gram limit of the damped Möbius receiver (ADR); a measure on $G$, not a point.

## 4. Mechanisms

**A. Gauge orthogonality**
1. Unique factorization: $\int\chi_x(m)\bar\chi_x(n)=[m=n]$ ⇒ gauge projection onto product coincidences; Parseval and
   $2k$-th moments are multiplicative diagonals at every length.
2. Ratio energy: gauge mean square of a pair form groups pairs by ratio $m/n$; distinct successor pairs and distinct prime
   pairs have distinct ratios.
3. Expectation pigeonhole: some twist is at least the mean square, some has $\Re\le0$.
4. Phase reconstruction: $\mathbb R/\mathbb Z$ divisible ⇒ injective; phases respecting all multiplicative relations extend
   to a twist (Baer).

**B. Line versus torus**
5. Windowed Gram = $\|\eta\|^2\cdot$gauge moment + near-incidence, at every product order; below $2rX^k\le1$ near-incidence
   vanishes. Near-incidence has gauge mean zero; nonnegative sources are the worst case of their orbit.
6. Finite gauge subgroups (Dirichlet characters mod $q$) project onto congruence classes; the singular series is the
   stabilizer average.
7. Sign gauge: mean sees square pairs $j(j+h)=\square$ (finitely many, $2j+h\le h^2$, none for $h=1$); second moment pairs
   $j,j'$ with equal squarefree kernel — Pell orbits, infinite.

**C. Boundaries**
8. Escaped pairing = defect of the affine map, a cocycle. Harmonic asymptotics: escaped mass of a dilation → $\log a$ at
   σ = ½, 0 above, ∞ below; successor → 0. Gauge-charged sources: gauge mean square at σ = escaped mass at 2σ ⇒ critical ¼.
9. Abel transfer: partial sums $O(n^\alpha)$ ⇒ tails $O(M^{\alpha-s})$ uniformly in $N$.

**D. Almost-sure cancellation and exceptional sets**
10. Rademacher–Menshov on orthonormal systems: dyadic maximal inequality + Markov + Borel–Cantelli ⇒
    $|S_N|\le C_\omega\sqrt{N+1}(1+\log(N+1))^2$ a.s. Applies to twists, successor monomials $\chi(n)\bar\chi(n+h)$ and
    product monomials $\chi(n(n+h))$.
11. Twin tails: on squarefree $n$, $\mu\chi=\psi(\gcd(n,Q))$ ⇒ $S_N=\sum_{d\mid Q}\psi(d)\#\{m\le N/d\text{ sqfree},(m,Q)=1\}$
    ⇒ linear growth $S_N/N\to\delta_Q\prod_{p\mid Q}(1-e(x_p)/p)\ne0$. Dense in the product topology ⇒ residual.

**E. Spectral reading of escape states**
12. Critical normalisation makes dilation contractive; dilated forms decrease along divisibility; infimum is exactly
    dilation invariant, a positive definite function of $j/k$ on $\mathbb Q_{>0}$ ⇒ finite measure on $G$
    (Herglotz–Bochner, APD).
13. Fibre sandwich $(1/j)E(M-1)\le\|D_jv\|^2\le(1/j)E(M)$ ⇒ gauge mass squeezed by energy ratios
    $E(\lfloor(T+2)/d\rfloor)/E(T+1)$; record horizons of unbounded $E/T^\kappa$ give $d\,K(d,d)\le(2/d)^\kappa$.
14. Mellin translation: energy $O(T^\kappa)$ ⇒ Mellin pairing holomorphic on $\Re s>(1+\kappa)/2$; cleared function
    vanishes on $(1-\varepsilon,1)$ ⇒ identically ⇒ zeros translate $\rho\mapsto\rho-\varepsilon$; a whole interval of
    dampings makes them accumulate.

**F. Amplification and localization**
15. Gauge Jensen $(\sum|a|^2)^k\le\int|D|^{2k}$ ⇒ multiplicative loss at least linear; relative $k$-th power of
    $\chi_x$ is $\chi_{kx}$, $\zeta$ is the fixed point.
16. Persistence: $Z(\tau)\ge(1-A|\tau-\gamma|)Z(\gamma)$ at every depth δ; a witness excludes a zero only on an interval of
    length $\asymp(1-r/Z(\gamma))/A$.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Gauge projection: twisted monomial mean = monomial iff products coincide | `integral_monomial_twist` | proved |
| Multiplicative data agree ⇔ sources differ by a twist | `agreeMultiplicatively_iff_exists_twist` | proved |
| Successor correlations: gauge mean 0, mean square $\sum|a_n|^2|a_{n+h}|^2$; twist with $\Re C_h\le0$ | `integral_normSq_succCorr_twisted`, `exists_twist_re_succCorr_nonpos` | proved |
| Windowed moment = gauge moment + near-incidence; equal below threshold | `windowed_pow_eq_gauge_add_nearIncidence`, `windowed_pow_eq_gauge_of_threshold` | proved |
| Coalescent surplus at 4/3 is $o(N^2)$ in gauge mean square; large twists Haar → 0 | `twistedPrimeCoalescentSurplus_meanSquare_isLittleO`, `tendsto_gaugeHaar_large_twistedSurplus` | proved |
| Surplus = congruent (stabilizer) part + discrepancy | `primeCoalSum_eq_stabilizer_add_discrepancy` | proved |
| Sub-progression window: surplus = −Σ over nontrivial characters | `primeCoalSum_eq_neg_sum_nontriv`, `eventually_bandwidth43_subProgression_window` | proved |
| Dilation boundary finite nonzero iff σ = ½ (limit $\log a$); charged: iff σ = ¼ | `exists_pos_tendsto_escapedMass_iff`, `exists_pos_tendsto_twistedFlatBoundary_iff` | proved |
| Möbius boundary → 0, Liouville twin ≥ 1/100 | `moebius_boundary_separates_twin` | proved |
| Every mixed Gram of one source is PSD | `gram_affine_nonneg` | proved |
| Möbius half-power law: a.e. / fails at twin / at 0 ⇔ RH | `moebius_gauge_trichotomy` | proved |
| Möbius boundary law: same trichotomy | `moebius_boundary_trichotomy` | proved |
| A.e. twist of μ has square-root two-point Chowla, all shifts | `ae_moebius_chowla` | proved |
| Exceptional set of the half-power law is comeager and Haar-null; 0 in its closure | `moebius_exceptional_residual_and_null`, `zero_mem_closure_exceptional` | proved |
| A.e. twist of Λ has no pole; at 0 $\psi(N)/N\to1$ | `ae_norm_twistedPsi_le`, `tendsto_twistedPsi_zero_div` | proved |
| Sign-gauge second moment = diagonal + Pell part, Pell classes infinite | `sum_sq_signTwistedSuccCorr_eq`, `exists_large_pellClass` | proved |
| Escape states are finite measures on $G$ | `exists_spectralMeasure`, `exists_actualCofactorLimit_spectralMeasure` | proved |
| Admission ⇒ gauge mass 1; power growth ⇒ gauge mass 0 | `gaugeMass_eq_one_of_admits`, `gaugeMass_eq_zero_of_powerGrowth` | proved |
| Subpower energy at every damping ⇒ RH | `riemannHypothesis_of_subpower_energy` | proved |
| RH ⇔ every escape state at every damping has positive gauge mass | `riemannHypothesis_iff_forall_gaugeMass_pos` | proved (equivalence) |
| Sublinear loss ⇒ no zero; golden datum has no fixed budget | `nonpos_of_sublinear_loss`, `goldenDatum_no_fixed_budget` | proved |
| Zero term persists over $1/A$ | `zeroTerm_ge`, `false_of_volume_lt` | proved |
| Charged cells ≥ $(X/162)^{1/4}-1$ for every real sign gauge flipping 2 | `sqrt_sqrt_div_sub_one_le_card_chargedCells` | proved |

## 6. Tools

**Developed**
- Gauge integrals: `integral_twist_mul_conj`, `integral_pairForm_mul_conj`, `integral_normSq_twistSum_pow`.
- Finite gauge: `sum_twist_dirichletGauge_mul_conj`, `sum_twistedPrimeCoalSum_dirichletGauge`, `dirichletGauge_one_eq_zero`.
- Sign gauge: `sum_primeSignTwist_mul`, `sum_signTwisted_succCorr`, `pell_step`.
- Boundary calculus: `escapedPairing_eq_defect`, `escapedPairing_comp`, `norm_sum_Ioc_mul_rpow_neg_le` (Abel transfer).
- Orthonormal a.s. engine: `sq_norm_orthoSum_le`, `ae_exists_norm_orthoSum_le`, `ae_exists_norm_gaugePartialSum_le`.
- Twin-tail calculus: `moebius_mul_twist_twinTail`, `moebiusGaugeSum_twinTail`, `card_gcd_eq`.
- Spectral escape states: `asymKernel_mul_mul`, `isPosDefOnGroup_ratioFunction`, `gaugeMass_eq_iInf`, `exists_record_horizons`.
- Mellin energy bridge: `summable_abs_mul_rpow_of_energy_growth`, `differentiableOn_complexMellinPairing_of_energy_growth`,
  `riemannZeta_sub_eq_zero_of_energy_growth`.
- Amplification: `pow_sum_normSq_le_gauge_moment`, `twist_nsmul`, `twisted_dirichletConv`, `relProd_twisted`.

**To build**
- Residue-class discrepancy calculus for actual primes with singular-series weights, uniform over levels $q<T^{1-\eta}$.
- A gauge-charged (non-finite-precision) property placing $0$ outside the exceptional set.
- Order-$k$ signed near-incidence beyond the threshold.
- Lower bounds on gauge mass of escape states at some damping below ½.
- Gauge-charged correspondence with a fixed budget (sublinear loss law).

## 7. Open questions

1. Stabilizer discrepancy of the actual primes at bandwidth 4/3 below the TTPC budget, uniformly in admissible $q$.
2. Square-root boundary law for μ at gauge point 0, any power saving θ > 0 (gives a zero-free strip).
3. Which gauge-charged property separates $0$ from twin tails? Finite-precision prime-phase data cannot.
4. Positive gauge mass of some escape state at some damping: any scale-invariant part of escaping energy.
5. Exact Pell-class sums of successor correlations for μ, λ; sign-gauge vs phase-gauge variance.
6. Localized averaged positivity: subpower averaged floors combined with the $1/A$ persistence scale.
7. Two-dimensional horizons: boundary of $ab-cd=h$; $\mathbb F_q[t]$ gauge calibration.
8. Additive divisor problem as fourfold incidence at one gauge point: what structure beyond the orbit bounds it?

## 8. Traps

| Trap | Fact |
|---|---|
| Multiplicative mean values see near-coincidences | They see the gauge projection only |
| Threshold is a weakness of mean-value theorems | It is the resolution of one line in $G$ |
| A bound from multiplicative data bounds $\zeta$ | It bounds the whole orbit, Haar-a.e. of which already satisfies it |
| Square-root cancellation is atypical | It holds Haar-a.e.; the question is whether 0 is typical |
| A generic/finite-precision property of prime phases decides RH | Exceptional set is comeager and accumulates at 0 |
| Positive-kernel bounds certify the coalescent budget | They bound the worst (nonnegative) orbit point, blind to repulsion |
| Sign twists kill every successor pair | Square pairs survive in the mean; Pell classes in the second moment |
| A PSD mixed Gram is arithmetic | Every mixed Gram of one source is PSD |
| Boundary terms are negligible | Dilation boundary → $\log a$ at σ = ½ |
| Relative tensor powers amplify $\zeta$ | $\zeta$ is the gauge fixed point; relative squares see only original counts |
| Positive Künneth counts give a budget | Golden datum: positive counts, no fixed budget |
| Averaged estimates localize | Only below persistence scale $1/A$ |
| Escape energy is always gauge-visible | Power-type growth has gauge mass 0 |
| The prime source is typical | It is atypical by exactly the pole; RH says only by the pole |

## 9. Context

| Uses | Modules |
|---|---|
| RHTower | 10 (PNT/ψ, von Koch, Littlewood, Nyman–Beurling, receiver dampings, admission, Weil–Kloosterman) |
| HTGeometry | 5 (infinite torus characters, squarefree density, real Dirichlet series) |
| BezoutValuationIncidence | 3 · ArithmeticDefectRigidity 3 |
| THIM, TTPC, SSA, RBG, BiarithmeticGeometry, APD, AKT, ACCE, ACS | 1 each |

| Used by | Modules |
|---|---|
| ArithmeticCorrespondencePositivity | 4 (golden datum, subpower translation) |
| SelectivePositivityAndThresholdLaws | 3 (Möbius boundary, stabilizers, escape visibility) |
| ArithmeticGaugeTheory | 2 · ArithmeticHarmonicAnalysis 2 |
| MainTheorems | umbrella |

| Neighbour | Relation |
|---|---|
| TransThresholdPairCorrelation | coalescent surplus at 4/3 is pure gauge charge; budget holds a.e.; open problem is the point 0 |
| SquareRootThreshold, ArithmeticKunnethTheory | archimedean family = one line in $G$; below threshold it computes gauge moments |
| SignedSuccessorArithmetic | dilation cocycle = gauge covariance of multiplicative signs |
| BiarithmeticGeometry, RBG | finite horizon presentation, escaped cells, cell holonomy |
| ArithmeticDefectRigidity | escape states supplied; here read as spectral measures |
| ArithmeticPositiveDuality | Herglotz–Bochner on $\mathbb Q_{>0}$ |
| MultiplicativePositivityGeometry, BiScaleUncertainty | their blindness theorems are gauge projection |
| ArithmeticCastelnuovoSeveri | golden datum and fake curves: fixed budget needs a correspondence |

## 10. Big picture

ACG names the reason so many routes stall: everything provable from multiplicative structure holds for the whole gauge
orbit of the source, and almost every point of that orbit already satisfies RH-type and Chowla-type cancellation. The
actual source is one point of a full-measure set that is also meagre, with atypical twins arbitrarily close in every
finite resolution. Any argument that does not use something specific to the point 0 — additive structure, the
archimedean pole, an explicit correspondence — proves a statement about the orbit, not about $\zeta$.

The positive message is a precise address for the missing input. The prime source is atypical exactly by its pole; the
critical line is the unique weight where dilation boundaries carry finite multiplicative mass; an off-line zero would show
up as escaping energy with no gauge spectrum. RH is thus a visibility statement — every escape state is seen by the
gauge torus — and a proof must supply gauge-charged information (singular series, correspondences with a fixed budget,
boundary structure) rather than sharper multiplicative estimates.
