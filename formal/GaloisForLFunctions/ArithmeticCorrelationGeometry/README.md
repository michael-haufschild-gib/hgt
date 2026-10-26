# Arithmetic Correlation Geometry (ACG)

**One question.** How do additive relations among integers constrain signed multiplicative
correlations, and how can those constraints become global spectral bounds without losing their
boundary information?

**The organizing fact.** Multiplicative observation has a symmetry group. The **gauge torus**
`G = (ℝ/ℤ)^{primes}` acts on arithmetic sources by the unimodular completely multiplicative twists
`χ_x(n) = ∏_p e(x_p v_p(n))`. Every correlation built from coincidences of products is constant on
gauge orbits. Every additive relation — `ab − cd = h ≠ 0`, the affine maps `n ↦ an + b` with
`b ≠ 0`, the successor — is *gauge charged*: its gauge mean is zero. Multiplicative data determine a
source exactly up to its gauge orbit, and no further. The arithmetic content of a signed
additive–multiplicative statement is therefore a property of **one gauge point**, the actual
source. ACG is the geometry of that point: how the archimedean line, the finite (Dirichlet)
subgroups and the boundary of finite presentations locate it, and what each of them can and cannot
see.

Namespace `GaloisForLFunctions.ArithmeticCorrelationGeometry`; umbrella
`ArithmeticCorrelationGeometry.lean`. Everything is unconditional. Hypotheses of the form
"`CoalescentSurplusAtMost β`" or RH appear only inside equivalences owned by other programmes.

---

## 1. Place in the research

The frontier has three walls: a signed arithmetic estimate in an RH-relevant scale (W1), its
survival through apertures, origins, damping and assembly (W3), and a source-defined carrier with an
independently proved sign (W14). The corpus has separated identifying the source, detecting its
off-line divisor, producing a sign, and transferring it; the third task is the missing one. ACG
asks where that sign can come from once multiplicative information is exhausted, and answers with
a symmetry: whatever multiplicative information proves holds on a whole gauge orbit, so a sign
that is specific to `ζ` must be gauge charged.

| Programme | Interface |
|---|---|
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | The coalescent prime-pair surplus at bandwidth `4/3` is pure gauge charge: mean zero, variance `o(N(T,2T)²)`; every budget holds for Haar-almost every twist of the primes. The open problem is a statement about the gauge point `0`. |
| [SquareRootThreshold](../SquareRootThreshold/README.md), [ArithmeticKunnethTheory](../ArithmeticKunnethTheory/README.md) | Windowed mean values and product moments. The archimedean family is a line in `G`; below the threshold it computes the gauge moments exactly, beyond it the excess is the near-incidence form. Gauge Jensen turns the AKT homogeneity into a linear loss law. |
| [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md) | The dilation cocycle is the gauge-covariance law of completely multiplicative signs. The sign gauge (`2`-torsion of `G`) sees a successor pair only when `j(j+h)` is a square. |
| [BiarithmeticGeometry](../BiarithmeticGeometry/README.md) | The finite horizon, its affine action and escaped cells. ACG adds the boundary cocycle, the incidence formula for mixed Grams, and the critical weight at which dilation boundaries are horizon uniform. |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md) | Escape states, origin traces, moving successors. ACG fixes the normalisation (`σ = ½`) at which the boundary of a dilation is a finite nonzero invariant, `log a`. |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Twist invariance of window extremes (`PrimeWindowTwistInvariance`) is a case of gauge invariance. |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | Affine positivity is induced from the dilations: free successor coordinates impose nothing. ACG explains why: free successor coordinates range over gauge-charged data; prescribed ones are a gauge point. |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | The `𝔽_q` calibration and the one known sublinear loss law: eventual Hasse–Weil is Hasse–Weil (a correspondence with a fixed budget). Golden datum. |
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | Boundary forcing by positivity of a multiplicative (gauge-invariant) divisor; it reaches `Re s = 1` and stops — gauge-invariant positivity is blind in the strip. |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Signed continuation. The Möbius boundary is the model of a signed horizon-uniform law whose positive part diverges. |
| RHTower | Prime number theorem (`tendsto_sum_range_succ_moebius_div`), squarefree density (`card_filter_squarefree_Ioc_ge`), Gram and certificate infrastructure. |

---

## 2. Why

**Blindness theorems are gauge theorems.** The corpus keeps rediscovering invariants that see the
primes only through their sizes: the correlation modulus of a completely multiplicative sequence is
coefficient blind (`RHTower.Sieve` primitive-ratio decomposition), window extremes are twist
invariant (BSU), multiplicative positivity forces only the boundary (MPG), and a free affine
extension adds nothing (APD). These are one statement. Characters of the compact torus `G` are
orthonormal, and unique factorization says that distinct positive integers have distinct exponent
vectors; so a monomial `a(m₁)⋯a(m_k) ā(n₁)⋯ā(n_l)` of a twisted source has gauge mean equal to
itself when `m₁⋯m_k = n₁⋯n_l` and zero otherwise. Multiplicative observation is the gauge
projection.

**Additive relations are gauge charged.** A pair `(n, n+h)` has ratio `(n+h)/n ≠ 1`, so every
successor correlation has gauge mean zero, and distinct successor pairs have distinct ratios, so
its gauge variance is `Σ |a_n|² |a_{n+h}|²` — the square-root size, a gauge-invariant number. The
energy of a successor correlation is multiplicative information; its value and its sign are not.

**The threshold is the price of one line.** Heights `t ↦ n^{it}` are the points of a single line in
`G` (the Kronecker line with frequencies `log p`). Averaging over a window of the line equals
averaging over all of `G` exactly as long as the window separates the products that occur; beyond
that, the excess is the **near-incidence form** `Σ_{j≠k} c_j c̄_k k_η(log j − log k)`, which has gauge
mean zero at every order. Montgomery–Vaughan, the square-root threshold and AKT's free region are
this one fact.

**Boundaries carry the archimedean place.** A finite presentation `{0,…,N}` with `n ↦ an + b`
absorbs the cells pushed past `N`. At the weight `n^{−σ}` the absorbed mass of a dilation tends to
`log a` at `σ = ½`, to `0` above, to `∞` below, while the successor leaves no boundary at all. The
critical line is the unique normalisation at which multiplicative structure is visible at the
boundary at a fixed, nonzero cost. A presentation that discards its escaped cells discards the
archimedean place, and the boundary is where a mixed law can distinguish gauge-equivalent sources:
the Möbius source and its Liouville twin `μ²` have the same multiplicative data, and their
boundaries are `→ 0` (the prime number theorem) and `≥ 1/100`.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Gauge torus, Haar measure | `UnitAddTorus ℕ`, one phase per prime (other coordinates unread) | `GaugeTorus`, `gaugeHaar` |
| Exponent vector | `v(n) = (v_p(n))_p ∈ ℤ^{(ℕ)}` | `expVec` |
| Twist, twisted source | `χ_x(n) = ∏_p e(x_p v_p(n))`; `(χ_x a)(n) = χ_x(n) a_n` | `twist`, `twisted` |
| Archimedean point | `χ(n) = n^{2πiξ}`, the phase flow with frequencies `log p` | `archPoint`, `twist_clockPhasePoint` |
| Dirichlet gauge point | `χ mod q` with its values at `p ∣ q` reset to one | `dirichletGauge` |
| Sign twist | `ε_s(n) = ∏_{p∈S} s_p^{v_p(n)}`, the `2`-torsion of `G` | `primeSignTwist` |
| Twisted polynomial | `Σ a_n χ_x(n)` | `twistSum` |
| Correlation monomial | `a(m₁)⋯a(m_k) ā(n₁)⋯ā(n_l)`; *coincident* if `∏m = ∏n` | `monomial` |
| Pair form | `Σ_{(m,n)} w(m,n) χ(m) χ̄(n)`; **ratio energy**: `Σ` over pairs of pairs with equal ratio | `pairForm` |
| Successor correlation | `C_h(a) = Σ a_n ā_{n+h}` | `succCorr`, `signTwistedSuccCorr` |
| Near-incidence form | off-diagonal of a windowed mean square | `nearIncidence` |
| Square pair | `(j, j+h)` with `j(j+h)` a perfect square | `SquarePair` |
| Finite presentation | horizon `{0,…,N}`, maps `j ↦ aj + b`, absorbing boundary | `HorizonSpace`, `horizonAffine` (BiarithmeticGeometry) |
| Escaped pairing | the pairing on absorbed cells = exact defect of the map | `escapedPairing` |
| Weighted source, escaped mass | `j ↦ j^{−σ}`; `Σ_{(N−b)/a<j≤N} j^{−2σ}` | `critSource`, `escapedMass` |
| Cell source | `j ↦ f(j)` on `j ≥ 1`; Möbius and flat critical sources | `cellSource`, `moebiusSource`, `flatSource` |
| Mixed Gram | `⟨A_{a,b}v, A_{c,d}w⟩`; faces: successor, dilation, affine | `horizonPairing_affine_affine` |
| Multiplicative agreement | equal moduli and equal ratios along every relation `∏ n^{k_n} = 1` | `AgreeMultiplicatively`, `relVec` |
| Zero term at aperture `A` | `Z(τ) = ∫ g(x) e^{δx} cos((τ − γ)x) dx`, `g ≥ 0` on `[−A, A]` | `zeroTerm` |
| Twisted coalescent statistic | `primeCoalSum` with pair characters | `twistedPrimeCoalSum`, `twistedPrimeCoalescentSurplus` |

**Words.** *Gauge invariant*: constant on gauge orbits; *gauge charged*: gauge mean zero.
*Multiplicative data*: the moduli and all coincident monomials, equivalently the gauge orbit.
*Gauge point of a source*: the source itself among its twists. *Stabilizer* of a pair: the
subgroups of `G` under which the pair is invariant. *Coalescent*: unresolved by the archimedean
line at the height in question. *Boundary correction*: the escaped pairing of a finite
presentation. *Loss law*: how the arithmetic bound of an order-`k` observable grows with `k`.

The numerical parameters are **height** (archimedean resolution), **level** `q` (finite
resolution), **shift** `h`, **horizon** `N`, **multiplier** `a`, **weight** `σ`, **aperture** `A`
and **order** `k`. Every theorem states which are fixed and which grow.

---

## 4. Mechanisms

1. **Character orthogonality on `G`.** `∫ χ_x(m) χ̄_x(n) dx = [m = n]` for positive integers, by
   injectivity of exponent vectors (`integral_twist_mul_conj`).
2. **Gauge projection.** Twisted monomials average to themselves or to zero according to product
   coincidence (`integral_monomial_twist`); gauge invariance is product coincidence
   (`monomial_twist_eq_iff`).
3. **Ratio energy.** The gauge mean square of a pair form groups pairs by ratio
   (`integral_pairForm_mul_conj`); distinct successor pairs and distinct prime pairs have distinct
   ratios (`eq_of_prime_cross_mul_eq`).
4. **Expectation pigeonhole.** On a probability space some point is at least the mean
   (`exists_twist_succCorr_large`, `exists_twist_re_succCorr_nonpos`).
5. **Line versus torus.** `n^{2πiξ}` is the twist at `archPoint ξ`; the windowed Gram identity splits
   into `‖η‖²` times the gauge moment plus the near-incidence form
   (`windowed_eq_gauge_add_nearIncidence`).
6. **Finite resolution.** Dirichlet orthogonality `Σ_χ χ(m) χ̄(n) = φ(q)[m ≡ n]` on the gauge points of
   level `q` (`sum_twist_dirichletGauge_mul_conj`).
7. **Sign orthogonality.** `Σ_s ε_s(m)ε_s(n) = ∏_p 2·[v_p(m) + v_p(n) even]`
   (`sum_primeSignTwist_mul`); square pairs satisfy `(2j+h−2y)(2j+h+2y) = h²`.
8. **Boundary telescoping.** The escaped pairing is the defect `⟨v,w⟩ − ⟨A v, A w⟩`, hence a cocycle
   under composition (`escapedPairing_comp`).
9. **Harmonic asymptotics.** `H_N − H_{(N−b)/a} → log a` by `H_n − log n → γ`; `p`-series tails above
   `½`; a counting lower bound below `½` (`tendsto_escapedMass_half`).
10. **Character extension.** `ℝ/ℤ` is divisible, hence an injective `ℤ`-module; a character of the
    relation-free quotient of `ℤ^S` extends to the exponent lattice (`exists_twist_of_relations`).
11. **Jensen on `G`.** `(∫|D|²)^k ≤ ∫|D|^{2k}` (`pow_sum_normSq_le_gauge_moment`).
12. **Persistence.** `1 − cos y ≤ |y|` makes the zero term `(1 − A|τ − γ|)`-persistent
    (`zeroTerm_ge`).

---

## 5. Pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| **P1 Gauge invariance of multiplicative observation** | Twists are exactly the unimodular completely multiplicative functions; orthogonality on `G`; twisted monomials project onto coincidences; gauge invariance ⇔ coincidence. | `exists_twist_eq`, `integral_twist_mul_conj`, `integral_monomial_twist`, `monomial_twist_eq_iff` |
| **P2 Gauge moments have no threshold** | `∫ |Σ a_n χ_x(n)|^{2k} = Σ_N |a^{*k}(N)|²` for every order and length. | `integral_normSq_twistSum`, `integral_normSq_twistSum_pow` |
| **P3 Phase reconstruction** | Multiplicative data of `a, b` agree on `S` iff `b = χ_x a` on `S`. | `agreeMultiplicatively_iff_exists_twist`, `exists_twist_of_relations` |
| **P4 Successor correlations are pure gauge charge** | Mean zero; variance `Σ|a_n|²|a_{n+h}|²`; covariance across shifts along `n h' = n' h`; twists of square-root size and of nonpositive real part with the same multiplicative data. | `integral_succCorr_twisted`, `integral_normSq_succCorr_twisted`, `integral_succCorr_mul_conj_succCorr`, `exists_twist_succCorr_large`, `exists_twist_re_succCorr_nonpos` |
| **P5 Real data see only square pairs** | The sign-gauge mean of a shift-`h` correlation keeps exactly the `j` with `j(j+h)` square, all below `h²/2`; none for `h = 1`. | `sum_signTwisted_succCorr`, `two_mul_add_le_sq_of_squarePair`, `sum_signTwisted_succCorr_one`, `sum_signTwisted_succCorr_eq_zero_of_large` |
| **P6 The threshold is the price of the archimedean line** | Windowed moments = `‖η‖²` gauge moments + near-incidence; equality below `2rX^k ≤ 1`; near-incidence has gauge mean zero at every order; the gauge-orbit mean of every windowed moment is its diagonal; nonnegative sources maximize PD-kernel near-incidence on their orbit. | `windowed_pow_eq_gauge_add_nearIncidence`, `windowed_pow_eq_gauge_of_threshold`, `integral_nearIncidence_pow_twisted`, `integral_windowed_twisted`, `norm_nearIncidence_twisted_le` |
| **P7 Finite subgroups resolve coalescence** | The archimedean line moves a pair by `≤ 2π|ξ||log(m/n)|`; Dirichlet characters are gauge points; level-`q` averaging projects onto congruence, for single pairs and for every pair form; a successor pair survives iff `q ∣ h`. | `norm_archPair_sub_one_le`, `twist_dirichletGauge`, `sum_twist_dirichletGauge_mul_conj`, `sum_pairForm_dirichletGauge`, `sum_twist_dirichletGauge_succ` |
| **P8 The coalescent surplus is pure gauge charge** | The twisted statistic has mean zero and variance `Σ` (pair weights)²; at bandwidth `4/3` the normalised variance is `≤ (1536/π²)(log T)³T^{1+η} = o(N(T,2T)²)`; the measure of twists exceeding `δN(T,2T)` tends to `0`. | `integral_twistedPrimeCoalSum`, `integral_normSq_twistedPrimeCoalSum`, `eventually_integral_normSq_twistedPrimeCoalescentSurplus_le`, `twistedPrimeCoalescentSurplus_meanSquare_isLittleO`, `tendsto_gaugeHaar_large_twistedSurplus` |
| **P9 Boundary calculus** | The escaped pairing is the exact defect; boundary cocycle; `D_aU = U^aD_a` with its boundary. | `escapedPairing_eq_defect`, `escapedPairing_comp`, `escapedPairing_ring_relation` |
| **P10 The boundary of a dilation is the archimedean place** | Escaped mass `→ log a` at `σ = ½`, `→ 0` above, `→ ∞` below (`a ≥ 2`), `→ 0` for the successor at every `σ > 0`; a finite nonzero limit iff `σ = ½`. | `tendsto_escapedMass_half`, `tendsto_escapedMass_of_half_lt`, `tendsto_escapedMass_of_lt_half`, `tendsto_escapedMass_successor`, `exists_pos_tendsto_escapedMass_iff` |
| **P11 Mixed Grams are linear incidences** | `⟨A_{a,b}v, A_{c,d}w⟩ = Σ_{aj+b=ck+d≤N} v_j w_k`; every mixed Gram of one source is PSD; dilation faces are sign-gauge covariant by `f(a)f(c)`, successor faces carry `f(j)f(j+h)`. | `horizonPairing_affine_affine`, `gram_affine_nonneg`, `horizonPairing_dilation_signTwist`, `horizonPairing_successor_signTwist` |
| **P12 The Möbius boundary separates gauge twins** | `Σ_{(N−b)/a<j≤N} μ(j)/j → 0` for every affine map; the Liouville twin `λμ = μ²` has the same multiplicative data and boundary `≥ r/100` when `2^r ≤ a`. | `tendsto_escapedPairing_moebiusSource`, `liouville_mul_moebius`, `escapedPairing_moebiusTwin_ge`, `moebius_boundary_separates_twin` |
| **P13 Persistence and the localization threshold** | Lipschitz persistence (exact, tent); the zero term satisfies `Z(τ) ≥ (1 − A|τ−γ|)Z(γ)` at every depth; a witness `−Z + R`, `|R| ≤ r`, is negative on length `2(1 − r/Z(γ))/A`, so smaller exceptional sets exclude the zero. | `neg_on_Ioo_of_lipschitz`, `tent_neg_iff`, `zeroTerm_ge`, `volume_neg_ge_of_zeroTerm`, `false_of_volume_lt` |
| **P14 Multiplicative amplification loses linearly** | `kδ ≤ b_k` at fixed order, `δ ≤ 0` under a sublinear loss law; gauge Jensen `(Σ|a|²)^k ≤ Σ_N|a^{*k}(N)|²`, sharp on atoms, inherited by windowed moments below the threshold; relative powers move the gauge point (`χ_x^k = χ_{kx}`, `ζ` fixed); external products commute with twists. | `mul_le_of_frequently_of_eventually`, `nonpos_of_sublinear_loss`, `pow_sum_normSq_le_sum_normSq_powCoeff`, `sum_normSq_powCoeff_single`, `windowed_pow_ge_of_threshold`, `twist_nsmul`, `twist_nsmul_zero`, `twisted_dirichletConv` |
| **P15 Near-incidences of products are successor correlations** | `Σ_{ab = cd + h} α_aα_b\overline{α_cα_d}` over a box is the shift-`h` successor correlation of `r = α * α`; multiplicative energy at `h = 0`; gauge mean zero and variance `Σ|r(N)|²|r(N+h)|²` for `h ≠ 0`. | `fourfoldIncidence_eq`, `fourfoldIncidence_zero`, `integral_fourfoldIncidence_twisted`, `integral_normSq_fourfoldIncidence_twisted` |
| **P16 Fixed budgets over `𝔽_q`** | Bounded power sums at every order force a curve datum to be unitary; the golden datum has power sums `≥ φ^j` and no fixed budget. | `unitary_of_bounded_powerSum`, `goldenRatio_pow_le_goldenDatum_trace`, `goldenDatum_no_fixed_budget` |

**Foundations from sibling programmes.**

| Foundation | Statement | Lean |
|---|---|---|
| F1 Coalescent certificate (TTPC) | `N₀*(T,2T) ≥ (29/36 − ε)N(T,2T) − S_{u,η}(T)`; reduction to odd primes at even shifts | `zeta_coalescent_certificate`, `coalescentSurplusAtMost_iff_primeCoalescentSurplusAtMost` |
| F2 Windowed diagonal law (SquareRootThreshold, AKT) | diagonal/off-diagonal split; product moments diagonal below `2rX^k ≤ 1` | `integral_pairTransform_mul_normSq_expSum_eq_diag_add`, `integral_pairTransform_mul_normSq_pow_eq_diag` |
| F3 Horizon boundary (BiarithmeticGeometry) | escaped-cell pairing identity; absorbing successor invariance forces constants | `horizonPairing_affine_add_boundary`, `horizon_successor_invariant_iff` |
| F4 Dilation cocycle (SSA) | completely multiplicative signs ⇔ prime cocycle of successor signs | `exists_cmSign_iff_primeCocycle` |
| F5 Affine induction (APD) | positive definiteness on `Aff(ℚ)` is induced from the dilations | `exists_isPosDefOnGroup_extension_iff` |
| F6 Fixed budget (AOG) | eventual Hasse–Weil with any constant is Hasse–Weil | `hasseWeilAt_of_eventually_bounded` |
| F7 Prime number theorem, squarefree density (RHTower) | `Σ_{n≤N} μ(n)/n → 0`; `#{squarefree in (K,2K]} ≥ K/50` | `tendsto_sum_range_succ_moebius_div`, `card_filter_squarefree_Ioc_ge` |

---

## 6. The questions and their answers

### Q1. Can the actual signed coalescent prime-pair surplus be bounded beyond the diagonal threshold?

*Answer: the surplus is pure gauge charge; any bound must come from information that distinguishes
the primes from their twists.* The statistic is a pair form over distinct primes. Twisted by `χ_x`
it has gauge mean zero and gauge variance equal to the sum of its squared weights, which at
bandwidth `4/3` and aperture `T^{−1+η}` is `o(N(T,2T)²)` for every `η < 1` (P8). So the budget
`β = 0 < 1/18` — strong enough for the `3/4` proportion — holds outside a set of twists whose Haar
measure tends to zero, and all these twists share every multiplicative statistic of the primes
(P1, P3). An argument that uses only multiplicative information proves the same bound for the whole
orbit; it cannot isolate the Hardy–Littlewood main term of the actual primes, which is an atypical
event of the orbit. Positive kernels cannot either: for the nonnegative prime source, the untwisted
near-incidence of a positive-definite kernel dominates every twist (P6), so it bounds the worst
case and cannot see repulsion.

*Where the information is.* The archimedean line freezes coalescent pairs (P7): a pair with
`|log(n/m)| ≤ T^{−1+η}` moves by `≤ 2πT^η` radians over heights up to `T`. The finite Dirichlet
subgroups resolve them: averaging over level `q` keeps exactly the pairs congruent mod `q`, and a
pair at shift `h` survives exactly at the levels `q ∣ h`. The singular series is an average over
these stabilizers. The concrete target is therefore the **discrepancy between the prime pairs and
the stabilizer average**, integrated against the signed coalescent kernel, in the normalisation
`N(T,2T)`, with the profile and aperture fixed before `T → ∞`.

*Localization.* A density or averaged bound becomes an individual-defect theorem only if the
exceptional set is smaller than the persistence scale of the witness. That scale is `≍ 1/A`,
independent of the depth (P13); at the natural aperture `A ≍ log T` the exceptional measure must
beat the mean zero spacing.

### Q2. Can prescribed additive–multiplicative compatibility force a new source inequality?

*Answer: compatibility laws are gauge-covariance laws, and a prescribed mixed law is the choice of a
gauge point; the boundary of a finite presentation is where such a choice becomes measurable.*

* Free mixed data impose nothing: successor coordinates are gauge charged (P4) and positive
  functionals on the affine group are induced from the dilations (F5). Mixed Grams of one source
  are always PSD (P11), so Gram positivity carries no arithmetic.
* The dilation face of a mixed Gram is gauge covariant — one character value per ratio — and the
  successor face is not (P11). For real sources the sign gauge leaves a successor correlation
  invariant only on the finitely many square pairs of its shift (P5). For completely
  multiplicative signs the complete compatibility law is the dilation cocycle (F4).
* **The milestone, realized.** A finite-horizon mixed identity with its complete boundary: the
  escaped pairing is the exact defect of an affine map and a cocycle (P9). A genuine arithmetic
  inequality for the boundary correction that distinguishes data identified by multiplicative
  magnitudes, uniformly in the horizon: the Möbius source has boundary `→ 0` for every affine map,
  its Liouville twin `μ²` — same moduli, same multiplicative monomials — has boundary `≥ r/100`
  (P12). The inequality is the prime number theorem, read at the boundary.
* The normalisation is forced: only at `σ = ½` is the boundary of a dilation a finite nonzero
  horizon-uniform quantity (P10). A mixed law at any other weight either loses the multiplicative
  boundary or is swamped by it.

The open step is a mixed boundary law of the same shape at **square-root scale** in the strip
(§9, topics 1–2).

### Q3. Is there a genuinely relative arithmetic amplification with sublinear loss?

*Answer: not inside multiplicative structure.* The amplification specification reduces to the loss
law `b_k = o(k)`, with the limit `R → ∞` taken at fixed `k` (P14). Every observable whose arithmetic
size is controlled by gauge moments — multiplicative energies, product moments, archimedean moments
below the threshold — has loss at least linear: `(Σ|a|²)^k ≤ Σ_N|a^{*k}(N)|²`, sharp on atoms
(P14). Relative (Euler-factor-wise) powers act on `G` by `x ↦ kx`; the coefficient system of `ζ` is
the fixed point `0`, so relative powers of `ζ` are `ζ`. External products commute with every twist
and keep the gauge class. The two-factor operations therefore split as: external (gauge weight one,
homogeneous: AKT), relative (gauge weight two, idempotent on `ζ`), correspondence (a pair form:
gauge charged off the diagonal, with the near-incidences as its content). Over `𝔽_q` a fixed budget
at every order forces purity, and the one known source of such a budget is a correspondence (F6,
P16); the golden datum, whose Künneth counts are all positive, loses linearly with slope `log φ`
and has no fixed budget (P16). A sublinear loss law over `ℤ` must therefore be
gauge charged: an order-`k` near-incidence estimate beyond the threshold (Q1 at every order) or a
correspondence whose budget is independent of `k`.

### Topics A–G

| Topic | Status in ACG |
|---|---|
| A. Signed near-incidence | `ab − cd = h` is a successor correlation of the product source (P15); near-incidence = archimedean minus gauge (P6); stabilizers of pairs (P7); the coalescent statistic is pure charge (P8). Open: the stabilizer discrepancy estimate. |
| B. Compatibility of mixed moments | Multiplicative data = gauge orbit (P3); successor data are charge (P4); dilation faces covariant (P11); real data see only square pairs (P5). |
| C. Boundary and escape | Boundary cocycle (P9); horizon-uniform only at `σ = ½` with value `log a` (P10); the boundary separates gauge twins (P12). |
| D. Sections with metric and torsion | The critical boundary of `j ↦ aj` is `log a = Σ_p v_p(a) log p`: the metric (archimedean) part of the degree, invisible to integer section counts (`N − ⌊(N−b)/a⌋ ≈ N(1−1/a)` is not horizon uniform). Bézout on the source cone stays with ACS. |
| E. Relative tensor calculus | Gauge weights of external, relative and correspondence products; linear loss (P14). |
| F. Defect-sensitive localization | Persistence scale `≍ 1/A`, independent of depth; exclusion below it (P13). |
| G. Signed continuation | The Möbius boundary is signed and horizon uniform while its positive part (the twin `μ²`) grows with `log a` (P12): positive-part control is strictly stronger than necessary. |

---

## 7. Traps

| Trap | Truth |
|---|---|
| Multiplicative mean values see near-coincidences | They see the gauge projection: product coincidences only, at every order (P2) |
| The threshold is a limitation of mean-value theorems | It is the resolution of one line in `G`; the full torus has none (P6) |
| A bound proved for the primes from multiplicative data is a bound for `ζ` | It is a bound for the whole gauge orbit (P1, P3), most of which has surplus `≈ 0` (P8) |
| Successor correlations are small because multiplicative data say so | Multiplicative data fix only their gauge variance; some twist has square-root size and nonpositive real part (P4) |
| Sign twists kill every successor pair | Not the square pairs `j(j+h) = □`; there are finitely many, below `h²/2` (P5) |
| Positive kernels can certify the coalescent budget | For nonnegative sources they bound the worst twist and cannot see repulsion (P6) |
| The archimedean family is a base for amplification | It is a line in `G`; its moments are gauge moments below the threshold and lose linearly (P14) |
| Relative tensor powers amplify `ζ` | `ζ` is the gauge fixed point: relative powers return `ζ` (P14) |
| A positive mixed Gram is arithmetic information | Every mixed Gram of one source is PSD (P11) |
| Boundary terms are negligible in the limit | Dilation boundaries tend to `log a` at the critical weight and carry the archimedean place (P10) |
| Any weight is a valid normalisation | Only `σ = ½` gives a finite nonzero dilation boundary (P10) |
| Equal magnitudes and equal multiplicative correlations mean equal boundary behaviour | `μ` and `μ²` differ at the boundary (P12) |
| An averaged estimate localizes once it holds on most heights | Only if the exceptional set is below the persistence scale `≍ 1/A` (P13) |
| A depth-`δ` zero is easier to localize because it is larger | Its height derivative grows by the same factor: persistence is depth independent (P13) |

---

## 8. Tools

Built:

- the gauge torus: twists, orthogonality, gauge moments of every order, gauge projection,
  reconstruction by character extension, the archimedean line, Dirichlet and sign subgroups;
- pair forms and ratio energies; successor charge, covariance across shifts;
- near-incidence forms and the archimedean–gauge comparison at every product order;
- the twisted coalescent statistic and its variance at bandwidth `4/3`;
- finite presentations: escaped pairings, cocycle, weighted escaped mass in all three regimes,
  cell sources, mixed-Gram incidence formula, sign covariance of dilation faces;
- the Möbius boundary and its twin;
- persistence of zero terms and the localization threshold;
- the amplification comparison and gauge Jensen.

To build:

- **stabilizer discrepancy calculus**: the coalescent statistic minus its average over the
  stabilizer subgroups, with explicit major-arc/minor-arc decomposition on `G`;
- **boundary laws at square-root scale**: escaped pairings of signed sources at weights `σ < ½ +
  o(1)` and their horizon uniformity;
- **order-`k` near-incidence forms beyond the threshold** with signed kernels;
- **gauge-charged correspondences**: pair forms with a fixed budget independent of the order;
- **witness profiles** with explicit `r/Z(γ)` for the averaged Weil forms of ACS.

---

## 9. Open research topics

1. **Stabilizer discrepancy at `4/3`.** Bound the signed coalescent statistic of the primes minus its
   average over the Dirichlet stabilizers `q ∣ h`, in the normalisation `N(T,2T)`. Any saving that
   lands below `5/36` is a new proportion theorem; below `1/18` it gives `3/4`.
2. **Square-root boundary law.** A signed source whose escaped pairing against the flat critical
   source is `O(N^{−θ})`-small uniformly in the multiplier, for some `θ > 0`. For `μ` this is a
   zero-free strip; the boundary formulation keeps the affine structure that the multiplicative
   formulation discards.
3. **Gauge-charged correspondence with a fixed budget.** A pair form defined from the integers whose
   order-`k` versions have a budget independent of `k`, calibrated against eventual Hasse–Weil.
4. **Sign-gauge variance.** The exact sign-gauge variance of successor correlations, grouped by the
   squarefree kernel of `j(j+h)`, and its comparison with the phase-gauge variance.
5. **Localized averaged positivity.** Combine the subpower averaged Weil floor of ACS with P13: the
   measure of heights with negative full zero form, against the persistence scale `1/A`.
6. **Escape states in gauge coordinates.** Read the cofactor escape limits of ADR as distributions on
   `G`; decide which are gauge invariant.
7. **Boundaries of higher presentations.** Two-dimensional horizons `{(j,k)}` with the maps
   `(j,k) ↦ (aj + b, ck + d)`, their escaped pairings, and the boundary of `ab − cd = h`.
8. **`𝔽_q[t]` gauge calibration.** The gauge torus of `𝔽_q[t]`, its archimedean line (the degree
   character), and the successor charge; where Weil's bound enters.

---

## 10. Success criteria and contribution standard

ACG succeeds when its language produces a new inequality for the actual source that survives to an
existing receiver. The report's tests, with their present status:

| Test | Status |
|---|---|
| A new inequality for the actual source | Boundary of `μ` vs its twin (P12); Haar-almost-every twist meets every coalescent budget (P8). The actual-primes coalescent budget is open (§9.1). |
| Correct Gamma/pole terms and all prime powers | The archimedean place appears as the boundary `log a` (P10); prime powers in the coalescent band are eliminated by TTPC before twisting. |
| Why the golden datum fails | Golden has positive Künneth counts and no fixed budget: its power sums grow like `φ^j` (P16). |
| Phase/parity distinctions | Gauge projection and reconstruction (P1, P3); sign gauge and square pairs (P5); `μ` vs `μ²` (P12). |
| Energy preserved at the horizon limit | Critical boundary `log a`, horizon uniform exactly at `σ = ½` (P10). |
| An intermediate theorem weaker than RH | P8, P10, P12 are unconditional statements about the actual objects. |
| A quantitative path to an individual-defect receiver | Persistence threshold `≍ 1/A` (P13). |

A contribution to ACG must:

1. be an unconditional Lean theorem about a stated object of §3;
2. say whether each quantity it controls is **gauge invariant or gauge charged**, and at which
   resolution (height, level, horizon) it is proved;
3. keep the boundary: state the escaped terms and the weight `σ` of every finite presentation;
4. for a bound on a gauge-charged quantity, say what distinguishes the actual source from its
   twists — a bound valid on the whole orbit is a statement about the orbit;
5. state its loss law if it amplifies, with the order of limits;
6. state its persistence scale if it localizes;
7. calibrate: Dirichlet twists, the Liouville and sign twins, the gauge-random twist, `𝔽_q` curve
   data and the golden datum;
8. record the positive survivor of every no-go.

Principles: multiplicative information is a gauge orbit; arithmetic is a gauge point; the line,
the finite subgroups and the boundary are the three ways to see a point; the critical weight is
the boundary's normalisation; amplification must earn a sublinear loss; localization must beat
`1/A`.

---

## 11. Modules

| Module | Content |
|---|---|
| `MultiplicativeObservationIsGaugeInvariant` | Gauge torus, twists, orthogonality, gauge moments of every order, gauge projection |
| `SuccessorCorrelationsArePureGaugeCharge` | Pair forms, ratio energy, successor mean/variance/covariance, blindness |
| `TheThresholdIsThePriceOfTheArchimedeanLine` | Archimedean line, near-incidence forms, threshold, gauge-orbit diagonal, alignment of nonnegative sources |
| `FiniteGaugeSubgroupsResolveWhatTheArchimedeanLineCannot` | Coalescence on the line, Dirichlet gauge points, congruence projection of pairs and pair forms, stabilizers of successor pairs |
| `TheCoalescentSurplusIsPureGaugeCharge` | Twisted coalescent statistic, variance, bandwidth-`4/3` size, Haar-almost-every budget |
| `MultiplicativeDataDetermineASourceUpToGauge` | Phase reconstruction by character extension |
| `RealMultiplicativeDataSeeOnlySquareSuccessorPairs` | Sign gauge, sign orthogonality, square pairs |
| `TheBoundaryOfADilationIsTheArchimedeanPlace` | Escaped pairings, cocycle, ring relation, the three weight regimes |
| `MixedGramsOfAnAffineOrbitAreLinearIncidences` | Incidence formula, automatic positivity, sign covariance of faces |
| `TheMoebiusBoundarySeparatesGaugeTwins` | Möbius boundary `→ 0`, Liouville twin boundary `≥ r/100` |
| `TheWitnessOfAZeroPersistsForTheReciprocalAperture` | Persistence, zero terms, localization threshold |
| `MultiplicativeAmplificationLosesLinearly` | Amplification comparison, gauge Jensen, relative and external powers |
| `TheGoldenDatumHasNoFixedBudget` | Fixed budget forces purity over `𝔽_q`; the golden datum loses linearly |
| `NearIncidencesOfProductsAreSuccessorCorrelations` | `ab − cd = h` as a successor correlation of the product source; its gauge charge |
