# ArithmeticGaugeTheory

Namespace `GaloisForLFunctions.ArithmeticGaugeTheory`; umbrella `ArithmeticGaugeTheory.lean`; 31 modules.
All results unconditional; RH and GRH appear only inside equivalences.

## 1. Motivation

ℤ has two structures, addition and multiplication. The dual of multiplication is the gauge torus G of
unimodular completely multiplicative functions χ_x. The prime/Möbius source is the trivial point x = 0;
twisting by any other x gives a source on the same footing, and Haar-almost every twist cancels to square
root. RH is therefore the statement that one point, 0, is typical. Over F_q[T] Frobenius couples the two
structures; ℤ has no such endomorphism. The programme asks what singles out 0, which invariants of a gauge
point read the zeros, what multiplicative or finitely determined data can and cannot decide, and where
additive structure (shells, periodicity, the pole) enters.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Gauge torus, twist, Haar | `GaugeTorus`, `twist`, `gaugeHaar` (ACG) | χ_x completely multiplicative, |χ_x| = 1; product Haar measure |
| Special locus | `dirichletGauge χ + verticalShift t` | Dirichlet gauge points and their archimedean lines n^{it} |
| Gauge exponent | `gaugeExponent a x`, `GaugePowerBound` | inf θ with Σ_{n≤N} a(n)χ_x(n) = O(N^θ) |
| Typical exponent | `typicalExponent`, `typicalLevels` | a.e. value of the exponent (= ½ for unimodular-at-primes sources) |
| Sources | `moebiusSource`, `oneSource` | μ and the constant 1 |
| Divisor fibre | `divisorFibre x ℓ` | Σ_{k∣ℓ} Λ(k)χ_x(k); = log ℓ at 0 |
| Prime pair form | `primePairForm`, `ratioPart`, `shellPart`, `truncConv`, `gaugeTransform` | Σ a(k)x(m)x̄(n)G(log n − log m − log k), split at n = km |
| Approximate ring endomorphism | `IsApproxRingEndomorphism`, `AdditiveDefectBounded` | completely multiplicative, bounded additive defect |
| Adams operation | `adams`, `IsAdamsFixed` | ψ^k x = kx; χ ↦ χ^k |
| Coprime sums | `coprimeMoebiusSum`, `coprimeMoebiusSet`, `coprimeTwistSum` | twisted sums over n free of chosen primes |
| Twin tail, Liouville twin, double | `twinTail` (ACG), `twist_liouvilleTwin`, `twist_double` | χ(p) = −1 off a finite set; x + ℓ; 2x |
| Top primes | `topPrimes M`, `gaugeRestrict` | primes in (M, 2M]: independent coordinates of S_{2M} |
| Escape state | `tendsto_escapeCoefficient` | limit of |S_N(x)|² dx / N |
| Prime gauge sum | `primeGaugeSum` | Σ Λ(n)χ_x(n) |
| Factorial-ratio producer | `landauCount`, `ghostWindow`, `ghostConstant` | ∏(a_i n)!/∏(b_j n)!, Σa = Σb |
| F_q[T] Möbius | `polyMoebius`, `monicOfDeg`, `moebiusDegreeSum` | function-field calibration |
| Fourier kernel | `fourierKernel`, `archPhase` | G(u) = Σ g_j e^{it_j u} |
| Affine kernel form | `kernelForm` | kernel invariant under dilations and successor |
| Rough source | `RoughSource R c` | supported on n with all prime factors > R |

External: `RHTower.zetaZeroAbscissa` (Θ), `RHTower.zeroAbscissa` (Θ_χ),
`BezoutValuationIncidence.multiplicative_largeSieve_sharp`, `HTGeometry.measure_infinitePi_eq_zero_or_one_of_invariant`.

## 3. Language

- **Gauge-invariant**: constant on gauge orbits (ratio part, multiplicative data). **Gauge-charged**: Haar
  mean zero (shells, divisor fibres).
- **Typical**: exponent equals the a.e. value. **Special point**: carries additive structure (0, Dirichlet
  points). **Liouville point**: χ(p) = −1 (on all or cofinitely many primes).
- **Coherent**: nonnegative statistic, maximal at 0. **Tail invariant**: exponent ignores finitely many primes.
- **Class of 0**: finite modifications and vertical shifts of 0. **Twin duality**: Dirichlet point ≥ typical,
  its Liouville twin ≤ typical.
- **Precision** of a producer: log size / multiplicity. **Short shell**: |n − km| ≤ 2.

## 4. Mechanisms

**A. Gauge calculus**
1. Twist orthogonality splits statistics into coinciding products (invariant) and charge. Gauge average of the
   prime pair form = ratio part; shells average to 0.
2. Coherence: c ≥ 0 ⇒ |S(x)| ≤ S(0); excess over RMS ≥ √(S(0)/L). For Λ the excess is the pole. Diamagnetism:
   on nonnegative data the form and its shells are maximal at 0.
3. Level-q character averages keep pairs km ≡ n (mod q); shell n = km + j survives iff q ∣ j.
4. Fourier factorization P = Σ_j g_j A_j |X_j|² ⇒ multiplicative large sieve one frequency at a time.

**B. Special-point rigidity**
5. Eventually periodic or convergent nowhere-zero completely multiplicative ⇒ ≡ 1. Bounded additive defect ⇒
   identity or |φ| ≤ 1 (doubling + dyadic powers).
6. Fixed points of ψ^q are twists with values in (q−1)-th roots of unity; ψ² fixes only 0.

**C. Exponent transport**
7. Abel summation through slowly varying weights (|Δn^{it}| ≤ 2|t|/(n+1)) ⇒ exponent constant on archimedean lines.
8. Splitting off one prime: S = A − χ(p)A(·/p), inverted by a geometric series in p^{−θ} ⇒ tail invariance.
9. Descent through the primes of q: character sums bounded by periodicity ((q+1)(log₂N+1)^{ω(q)}); twisted
   Mertens sums governed by zeros of L(s,χ).
10. Twin expansion: at x + ℓ, μ ↦ μ²χ_x = Σ_{d²|n} μ(d)χ_{2x}(d)·(constant source at x); hyperbola split at N^κ.

**D. Measure and category**
11. Zero-one law: tail-invariant sublevel sets have Haar measure 0 or 1.
12. Top-prime block: n ≤ 2M divisible by p ∈ (M,2M] is p; product rigidity on {1} ∪ primes ⇒ fourth moment
    ≤ 2·(second)²; Paley–Zygmund ⇒ |S_{2M}|² > #T/2 with probability ≥ 1/8; PNT makes #T beat N^a, a < 1.

**E. Producers and calibration**
13. Above √length, v_p of a balanced factorial ratio is the Landau count, periodic in n mod p ⇒ multiplicity
    transfers to ghost windows ⇒ log A ≥ (2 log 2 − ε)mn.
14. F_q[T]: pair divisors with multiples by an irreducible; count multiples q^{n−k}; double counting.

**F. Affine kernels**
15. Dilation + successor invariance leaves three constants ⇒ form = c(Σv)² + (D − c)|v|² = c·δ_0 + (D − c)·Haar.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Only 0 is eventually periodic / convergent | `eq_one_of_eventually_periodic`, `twist_eq_one_of_tendsto`, `dirichletCharacter_eq_one_of_periodic_gauge` | proved |
| Frobenius gap: approximate ring endomorphisms = id or unit ball | `approxRingEndomorphism_classification`, `approxRingEndomorphism_unimodular_iff` | proved |
| Adams fixed points = finite-order twists; ψ² fixes only 0 | `isAdamsFixed_iff`, `isAdamsFixed_two_iff` | proved |
| Divisor collapse F_0 = log ℓ, unique maximizer, mean 0 | `divisorFibre_eq_log_forall_iff`, `trivialPoint_coherent` | proved |
| Gauge average of prime pair form = ratio part | `integral_primePairForm_gaugeTransform` | proved |
| θ_μ(0) = Θ; RH ⇔ θ_μ(0) ≤ ½ | `gaugeExponent_moebius_trivial`, `riemannHypothesis_iff_gaugeExponent_moebius_trivial_le_half` | proved |
| Exponent constant on archimedean lines and under finite flips | `gaugeExponent_add_verticalShift`, `gaugeExponent_moebius_eq_of_agree_off_finset` | proved |
| Zero-one law; a.e. exponent = ½ | `gaugeHaar_gaugeExponent_le_eq_zero_or_one'`, `typicalExponent_eq_half`, `ae_gaugeExponent_moebius_eq_half` | proved |
| Θ ≥ ½; RH ⇔ θ_μ(0) = typical | `half_le_gaugeExponent_moebius_trivial`, `riemannHypothesis_iff_trivialPoint_eq_typical` | proved |
| {θ_μ = 1} null and residual; every prescribed sublinear rate exceeded generically | `moebius_exponent_one_residual_and_null`, `residual_moebius_exceeds_sublinear` | proved |
| Gauge-invariant bounds ≥ ¾; finitely determined bounds ≥ 1 | `threeQuarters_le_of_gaugeInvariant_bound`, `one_le_of_cylinder_bound` | proved |
| Twin tails and Liouville point have exponent 1 | `gaugeExponent_moebius_twinTail`, `gaugeExponent_moebius_liouville` | proved |
| Constant source: 0 at nonprincipal Dirichlet lines, 1 at principal/trivial | `gaugeExponent_one_dirichletGauge_verticalShift`, `gaugeExponent_one_special_ne_typical` | proved |
| θ_μ(Dirichlet point) = Θ_χ; typical ⇔ GRH(χ) | `gaugeExponent_moebius_dirichletGauge`, `dirichletGRH_iff_dirichletGauge_typical` | proved |
| Special locus typical on average (≤ 2N^{1−2ε} exceptions) | `card_atypical_dirichletGauge_le_rpow` | proved |
| Antipode: S_N(ℓ) + S_N(0) = 2ψ(√N); pole ±1 | `primeGaugeSum_liouville_add_trivial`, `eventually_re_primeGaugeSum_liouville_neg` | proved |
| Escape state coefficients μ(a)d(a)/a; tilt −(6/π²)/(p+1) | `tendsto_escapeCoefficient`, `eventually_re_escapeCoefficient_prime_neg` | proved |
| Twin inequality; twin duality; floor ½ would force Θ = 1 | `gaugeExponent_moebius_liouvilleTwin_le`, `twin_duality`, `zetaZeroAbscissa_eq_one_of_floor` | proved |
| Factorial ratios: bounded multiplicity, precision ≥ 2 log 2 | `padicValNat_le_of_factorialRatio`, `factorialRatio_precision`, `centralBinom_producer` | proved |
| F_q[T] degree sums 1, −q, 0, …; twin count q^n − q^{n−1} | `sum_monicOfDeg_polyMoebius`, `sum_monicOfDeg_polyMoebius_sq` | proved |
| Shells have level of distribution ½ (large-sieve form) | `largeSieve_shellPart` | proved |
| Positive affine forms = pole + Haar; index ≤ 1 | `affine_nonneg_iff`, `affine_nonneg_on_poleHyperplane_iff` | proved |
| Short shells (overlap ≤ 2) invisible at every level q ≥ 3 | `sum_shellPart_dirichletGauge_eq_zero_of_kernel_short` | proved |
| θ_μ(0) = ½ | — | open (RH) |

## 6. Tools

**Developed**
- Gauge exponent calculus: monotonicity, Abel transfer, prime splitting, descent through moduli, hyperbola bound.
- Zero-one law and top-block Paley–Zygmund for exponents on G.
- Shell calculus: convolved form, ratio/shell split, congruence projection, Fourier factorization, large sieve.
- Producer precision ledger (Landau count, ghost windows).
- Function-field calibration from unique factorization.

**To build**
- Non-periodic producer (valuations not a function of n mod p) with sublinear precision loss.
- Per-point typicality for small conductors (Siegel–Walfisz analogue: zero-free regions at each Dirichlet point).
- Sign of the complete Weil form at overlap ≤ 2, where shells are conductor-free.
- Positivity for successor-breaking (non-invariant) affine forms with the pole as only negative square.
- Index ceiling at 0 (the twin inequality is circular there).

## 7. Open questions

1. Infimum of the Möbius exponent over G: 0, ¼ (twins have series L(s,χ)/L(2s,χ²)), or other?
2. Does a Thue-type bound Θ_χ ≤ 1 − c for each special point follow from gauge data?
3. Is there an integer producer with square-root precision?
4. Which identity carries the zero margin of Weil's form at 0 (RH is extremal: 0 can only err upward)?
5. Can additive structure pay on signed nonpolar directions where coherence fails?

## 8. Traps

| Trap | Fact |
|---|---|
| Multiplicative arguments decide 0 | They give a.e. statements; gauge-invariant bounds are ≥ ¾ |
| Finitely many primes or the archimedean place decide typicality | Exponent invariant under finite flips and vertical shifts; cylinder bounds ≥ 1 |
| ½ is a floor on G | Floor would force Θ = 1; Liouville twins of Dirichlet points sit ≤ ½ |
| Special points are typical | For the constant source they are 0 or 1, never ½; for μ they are ≥ ½ |
| Coherence at 0 is arithmetic | Forced by nonnegativity; the pole is coherence |
| Shells help positivity at 0 on nonnegative data | Diamagnetism: maximal at 0, subtracted in Weil's form |
| Size statements separate 0 from Liouville | Both coherent of size N; only the pole's sign separates them |
| Haar averages see off-line zeros | Escape state is an Euler product, blind to zeros |
| Measure-small = small | Exceptional set is null but residual |
| Higher multiplicity buys precision | Periodic producers pay 2 log 2 × window mass at every multiplicity |
| Level of distribution decides 0 | 0 is one term of the large sieve sum |
| F_q[T] behaviour transfers to 0 | There the trivial point is better than typical; over ℤ never |
| Dirichlet characters are periodic gauge points | Unimodular periodic ⇒ trivial; characters vanish at their modulus |

## 9. Context

**Uses** (import counts): RHTower 11, BezoutValuationIncidence 4, HTGeometry 3, PNTPlus 2,
ArithmeticCorrelationGeometry 2, ArithmeticKreinLangerTheory 1, ArithmeticContinuationAndCriticalEnergy 1.

**Used by**: ArithmeticHarmonicAnalysis (`AdamsFixedLocusResolution`).

| Neighbour | Relation |
|---|---|
| ArithmeticCorrelationGeometry | Supplies gauge torus, twists, orthogonality, twin tails, comeager-null exceptional set |
| RHTower | Littlewood/twisted Littlewood bounds, zero obstructions, M(x) ≠ o(√x), Dirichlet partial sums, PNT-type estimates |
| BezoutValuationIncidence | Multiplicative large sieve, Möbius dilation means, Mertens–abscissa link |
| ArithmeticKreinLangerTheory | Producer ledger (Σ m_p log p ≤ log A) |
| ArithmeticContinuationAndCriticalEnergy | F_q[T] calibration model, here derived |
| ArithmeticHarmonicAnalysis | Builds on Adams fixed loci |

## 10. Big picture

Gauge theory recasts RH as a typicality question for a single point on a compact group whose almost every
point already satisfies the square-root law. The programme establishes the full landscape around that point:
the typical value is exactly ½, the trivial point can only err upward, its whole natural class shares its
exponent, and the special locus reads GRH point by point while being typical on average. Every Haar average,
every gauge-invariant certificate and every finitely determined certificate is provably blind to the
difference between 0 and its atypical neighbours.

The lesson for an RH proof is that the decisive input must be pointwise at 0 and must use additive structure
on signed directions: the pole (coherence) and periodicity (cancellation) are the only additive mechanisms at
special points, and neither produces the typical value. Multiplicity-based producers, conductor averages and
level of distribution all stop exactly one point short. Up to overlap two the Weil form's shells are invisible
to every conductor, so the sign there is a property of 0 alone; this localizes the open problem without
supplying it.
