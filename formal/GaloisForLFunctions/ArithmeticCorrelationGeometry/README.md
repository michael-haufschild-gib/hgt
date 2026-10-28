# Arithmetic Correlation Geometry (ACG)

Namespace `GaloisForLFunctions.ArithmeticCorrelationGeometry`; umbrella `ArithmeticCorrelationGeometry.lean`.

**Question.** How do additive relations among integers constrain signed multiplicative correlations, and how can
those constraints become global spectral bounds without losing their boundary information?

**Organizing fact: multiplicative observation has a symmetry group.** The **gauge torus** $G=(\mathbb R/\mathbb Z)^{\text{primes}}$
acts on sources by unimodular completely multiplicative twists $\chi_x(n)=\prod_pe(x_pv_p(n))$. Every correlation built
from product coincidences is constant on gauge orbits; every additive relation ($ab-cd=h\ne0$, $n\mapsto an+b$ with
$b\ne0$, the successor) is **gauge charged** (mean zero). Multiplicative data determine a source exactly up to its
gauge orbit. The arithmetic content of a signed additive–multiplicative statement is a property of **one gauge point**,
the actual source ($x=0$).

**Central picture.** The square-root laws RH and Chowla ask for hold at **Haar-almost every** gauge point, fail at
the Liouville twin, and at the point $0$ are the conjectures themselves; the exceptional set is **null but comeager**.
RH asks whether $0$ is typical — and no finite-precision information about prime phases can decide it.

---

## 1. Place in the research

Walls: a signed estimate at an RH scale (W1), its survival through apertures/damping/assembly (W3), a source-defined
carrier with an independent sign (W14). ACG says where a sign can come from once multiplicative information is
exhausted: whatever multiplicative information proves holds on the whole orbit, so a sign specific to $\zeta$ must be
gauge charged.

| Programme | Interface |
|---|---|
| TransThresholdPairCorrelation | Coalescent surplus at $4/3$ is pure gauge charge; budget holds for a.e. twist; open problem = gauge point 0 |
| SquareRootThreshold, ArithmeticKunnethTheory | Archimedean family = one line in $G$; below threshold it computes gauge moments exactly |
| SignedSuccessorArithmetic | Dilation cocycle = gauge covariance of CM signs; sign gauge sees square and Pell pairs |
| BiarithmeticGeometry, BiarithmeticGaugeGeometry | Finite horizon, affine action, escaped cells; cell holonomy |
| ArithmeticDefectRigidity | Escape states = spectral measures on $G$; gauge mass = energy ratio |
| ArithmeticPositiveDuality | Affine positivity induced from dilations; Herglotz–Bochner on $\mathbb Q_{>0}$ |
| MultiplicativePositivityGeometry | Gauge-invariant positivity forces only $\Re s=1$ |
| `RHTower` | PNT, squarefree density, Littlewood/von Koch criteria |

---

## 2. Why

**Blindness theorems are gauge theorems.** Coefficient-blind correlation moduli, twist-invariant window extremes
(BSU), boundary-only multiplicative forcing (MPG), free affine extensions (APD) are one statement: by unique
factorization a twisted monomial averages to itself iff its products coincide, else to zero.

**Additive relations are gauge charged.** Distinct successor pairs have distinct ratios, so a successor correlation
has gauge mean 0 and gauge variance $\sum|a_n|^2|a_{n+h}|^2$: its *energy* is multiplicative information, its value and
sign are not.

**The threshold is the price of one line.** Heights $t\mapsto n^{it}$ trace one line in $G$; a window average equals the
torus average exactly while the window separates the products that occur; beyond it the excess is the
**near-incidence form** (gauge mean zero at every order). Montgomery–Vaughan and the square-root threshold are this fact.

**Boundaries carry the archimedean place.** In a finite presentation with absorbing boundary, the escaped mass of a
dilation at weight $n^{-\sigma}$ tends to $\log a$ exactly at $\sigma=\tfrac12$ (0 above, ∞ below); for gauge-charged sources
the critical weight halves to $\tfrac14$. The boundary separates gauge-equivalent sources: $\mu$ and its twin $\mu^2$ share
all multiplicative data; their boundaries are $\to0$ (PNT) and $\ge1/100$.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Gauge torus, Haar | one phase per prime | `GaugeTorus`, `gaugeHaar` |
| Twist, twisted source | $\chi_x(n)$; $(\chi_xa)(n)$ | `twist`, `twisted` |
| Archimedean point | $\chi(n)=n^{2\pi i\xi}$ | `archPoint` |
| Dirichlet gauge point | $\chi\bmod q$ with $p\mid q$ values reset to 1 | `dirichletGauge` |
| Sign twist | 2-torsion of $G$ | `primeSignTwist` |
| Pair form, ratio energy | $\sum w(m,n)\chi(m)\bar\chi(n)$ | `pairForm` |
| Successor correlation | $C_h(a)=\sum a_n\bar a_{n+h}$ | `succCorr` |
| Near-incidence form | off-diagonal of a windowed mean square | `nearIncidence` |
| Finite presentation, escaped pairing | horizon $\{0..N\}$, absorbing boundary; exact defect | `escapedPairing`, `escapedMass` |
| Mixed Gram | $\langle A_{a,b}v,A_{c,d}w\rangle$ | `horizonPairing_affine_affine` |
| Twisted coalescent statistic | `primeCoalSum` with pair characters | `twistedPrimeCoalSum` |
| Escape-state spectral measure | measure $\nu_L$ on $G$ of a cofactor Gram limit; mass `gaugeMass` | `asymKernel`, `exists_spectralMeasure` |
| Zero term at aperture $A$ | $Z(\tau)=\int g\,e^{\delta x}\cos((\tau-\gamma)x)$ | `zeroTerm` |

**Words.** *Gauge invariant / gauge charged*; *gauge point of a source*; *stabilizer* of a pair (subgroups fixing it);
*coalescent* (unresolved by the line at that height); *loss law* (growth of an order-$k$ bound with $k$); *typical*
(outside a Haar-null exceptional set). Parameters: height, level $q$, shift $h$, horizon $N$, multiplier $a$, weight $\sigma$,
aperture $A$, order $k$ — state which are fixed and which grow.

---

## 4. Mechanisms

1. **Character orthogonality on $G$** (injectivity of exponent vectors) ⇒ gauge projection onto product coincidences.
2. **Ratio energy**: gauge mean square of a pair form groups pairs by ratio.
3. **Expectation pigeonhole**: some twist is at least the mean (square-root size, nonpositive real part).
4. **Line vs torus**: windowed Gram = $\|\eta\|^2\cdot$gauge moment + near-incidence.
5. **Finite resolution**: Dirichlet orthogonality projects onto congruence; a successor pair survives at level $q$ iff $q\mid h$.
6. **Sign orthogonality**: square pairs $j(j+h)=\square$ (finitely many); sign-gauge second moments pair $j,j'$ with equal
   squarefree kernel — **Pell orbits**, infinite.
7. **Boundary telescoping**: escaped pairing = defect, a cocycle; harmonic asymptotics at the three weight regimes.
8. **Rademacher–Menshov on $G$**: twists form an orthonormal system; dyadic maximal inequality + Borel–Cantelli ⇒
   almost-sure square-root cancellation $|S_N(x)|\le C_x\sqrt N(1+\log N)^2$ (also for successor patterns).
9. **Twin tails**: phase ½ on all but finitely many primes turns $\mu\chi_x$ into a squarefree count with a pole ⇒ the
   exceptional set is residual in every open set.
10. **Spectral reading of escape states**: critical normalisation $\tilde K=\sqrt{jk}K$ makes dilation contractive; the
    asymptotic kernel is dilation invariant, PD on $\mathbb Q_{>0}$, hence a measure on $G$ (Herglotz–Bochner); its mass is
    $\inf_dd\,K(d,d)$ = asymptotic energy ratio $E(T/d)/E(T)$ (fibre sandwich).
11. **Mellin translation**: polynomial receiver energy $O(T^\kappa)$ makes the Mellin pairing holomorphic on $\Re s>(1+\kappa)/2$
    and translates zeros $\rho\mapsto\rho-\varepsilon$.
12. **Character extension** ($\mathbb R/\mathbb Z$ divisible) ⇒ phase reconstruction; **Jensen on $G$** ⇒ linear loss.
13. **Persistence**: $Z(\tau)\ge(1-A|\tau-\gamma|)Z(\gamma)$ at every depth.

---

## 5. Pillar theorems

1. **Gauge invariance of multiplicative observation; reconstruction up to gauge** (`integral_monomial_twist`,
   `agreeMultiplicatively_iff_exists_twist`).
2. **Successor correlations are pure gauge charge** (`integral_normSq_succCorr_twisted`, `exists_twist_re_succCorr_nonpos`).
3. **The threshold is the price of the archimedean line** (`windowed_pow_eq_gauge_add_nearIncidence`).
4. **Coalescent surplus is pure gauge charge and splits over its stabilizers**; in the intermediate window it is minus
   the sum over nontrivial characters (`tendsto_gaugeHaar_large_twistedSurplus`, `primeCoalSum_eq_stabilizer_add_discrepancy`,
   `primeCoalSum_eq_neg_sum_nontriv`).
5. **Boundary of a dilation is the archimedean place** (σ = ½); charged boundaries are critical at ¼
   (`exists_pos_tendsto_escapedMass_iff`, `exists_pos_tendsto_twistedFlatBoundary_iff`).
6. **Möbius boundary separates gauge twins** (`moebius_boundary_separates_twin`).
7. **Gauge trichotomies**: half-power law and square-root boundary law hold a.e., fail at the twin, are RH at 0; a.e.
   square-root Chowla at every shift (`moebius_gauge_trichotomy`, `moebius_boundary_trichotomy`, `ae_moebius_chowla`).
8. **The exceptional set is comeager and null** (`moebius_exceptional_residual_and_null`, `zero_mem_closure_exceptional`).
9. **Prime source is typical except for its pole**; RH ⇔ typicality modulo the pole (`riemannHypothesis_iff_twistedPsi_zero_sub`).
10. **Escape states are spectral measures on $G$; RH ⇔ every escape state has positive gauge mass**; power-type energy
    growth is invisible (`exists_actualCofactorLimit_spectralMeasure`, `riemannHypothesis_iff_forall_gaugeMass_pos`,
    `gaugeMass_eq_zero_of_powerGrowth`, `riemannHypothesis_of_subpower_energy`).
11. **Linear loss of multiplicative amplification; golden datum has no fixed budget** (`nonpos_of_sublinear_loss`,
    `goldenDatum_no_fixed_budget`).
12. **Persistence and localization threshold** $\asymp1/A$ (`zeroTerm_ge`, `false_of_volume_lt`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Multiplicative mean values see near-coincidences | They see the gauge projection only |
| The threshold is a limitation of mean-value theorems | It is the resolution of one line in $G$ |
| A bound from multiplicative data is a bound for $\zeta$ | It is a bound for the whole orbit, most of which already satisfies it |
| Square-root cancellation is atypical | It holds Haar-a.e.; the question is whether 0 is typical |
| A generic property of prime phases decides RH | The exceptional set is comeager; finite-precision data cannot separate 0 from twin tails |
| Positive kernels certify the coalescent budget | For nonnegative sources they bound the worst twist |
| Sign twists kill every successor pair | Square pairs survive in the mean; Pell classes in the second moment |
| A positive mixed Gram is arithmetic information | Every mixed Gram of one source is PSD |
| Boundary terms are negligible | Dilation boundaries tend to $\log a$ at σ = ½ |
| Relative tensor powers amplify $\zeta$ | $\zeta$ is the gauge fixed point |
| An averaged estimate localizes | Only below the persistence scale $\asymp1/A$ |
| Escape energy is always visible in gauge coordinates | Power-type escape has zero gauge mass |

---

## 7. Open problems

1. **Residue-class discrepancy at 4/3**: bound the stabilizer discrepancy of the actual primes in the normalisation
   $N(T,2T)$, uniformly over admissible levels (budget $<5/36$ beats 2/3; $<1/18$ gives 3/4).
2. **Square-root boundary law** for $\mu$ at gauge point 0 (any $\theta>0$ gives a zero-free strip), keeping the affine
   structure.
3. **Typicality of 0 from non-multiplicative input**: a gauge-charged property, not finite-precision in prime phases,
   that places 0 outside the exceptional set.
4. **Gauge mass of escape states**: show escape states have positive gauge mass at some damping below ½ (any scale-invariant
   part of escaping energy).
5. **Gauge-charged correspondence with a fixed budget** (sublinear loss law), calibrated against eventual Hasse–Weil.
6. **Sign-gauge variance**: exact Pell-class sums of successor correlations vs phase-gauge variance.
7. **Localized averaged positivity**: combine subpower averaged Weil floors with the persistence threshold.
8. **Higher presentations** (two-dimensional horizons, boundary of $ab-cd=h$); **$\mathbb F_q[t]$ gauge calibration**.

## 8. Tools to build

Residue-class discrepancy calculus with singular-series weights; boundary laws at square-root scale; order-$k$ signed
near-incidence beyond the threshold; gauge-charged correspondences; witness profiles with explicit $r/Z(\gamma)$.

## 9. Contribution standard

Unconditional; say whether each controlled quantity is gauge invariant or charged and at which resolution; keep the
boundary (escaped terms and weight σ); for a bound on a charged quantity, say what distinguishes the actual source
from its twists (a bound on the whole orbit is about the orbit); state loss laws and persistence scales; calibrate on
Dirichlet twists, Liouville and sign twins, the gauge-random twist, $\mathbb F_q$ curves and the golden datum.
