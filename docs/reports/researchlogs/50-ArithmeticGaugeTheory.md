# 50 ArithmeticGaugeTheory — facts log

Gauge torus = unimodular completely multiplicative functions χ_x = `twist x` (from ArithmeticCorrelationGeometry); x = 0 is the prime source; Haar measure `gaugeHaar`.

## TheAdditivelyInvariantPoint (uses ArithmeticCorrelationGeometry FiniteGaugeSubgroupsResolveWhatTheArchimedeanLineCannot)
- Nowhere-vanishing completely multiplicative f eventually periodic ⇒ f ≡ 1 (f(qk+q) = f(qk) ⇒ f(k+1) = f(k) ⇒ eventually constant c, f(K²) = f(K)² ⇒ c = 1). Convergent to L ≠ 0 ⇒ f ≡ 1. Unimodular + convergent ⇒ f ≡ 1.
- Eventually periodic or convergent twist is trivial. Dirichlet gauge point (agrees with χ off modulus) periodic ⇒ χ = 1. Only x = 0 sees addition; vertical shifts n^{it} are slowly varying but not convergent.

## ApproximateRingEndomorphisms
- Completely multiplicative φ with additive defect ≤ B: φ = id on ℕ_{>0}, or |φ| ≤ 1 (doubling |φ(n)||φ(2)−2| ≤ B; φ(2) = 2 ⇒ 2^k|φ(n)−n| ≤ (n−1)B). Converse: |φ| ≤ 1 ⇒ defect ≤ 3. Approximate ring endomorphisms = identity ∪ completely multiplicative maps in the closed unit ball.
- f(1) = 1, |f(p)| ≥ 1 at primes ⇒ identity or a gauge point. Exact (defect 0): identity or zero. Integer-valued: identity or values in {−1, 0, 1}.
- Contrast: Frobenius on F_p[X] multiplies degree by p. ℤ has no growing Frobenius substitute among its self-maps.

## TheDivisorCollapse
- divisorFibre F_x(ℓ) = Σ_{k∣ℓ} Λ(k)χ_x(k); F_0(ℓ) = log ℓ (Λ * 1 = log). Re F_x(ℓ) ≤ log ℓ, equality iff χ_x(p) = 1 for all p ∣ ℓ; all fibres = log ⇔ x trivial. χ_x(p) = −1 ⇒ F_x(p) = −log p.
- Gauge mean of F_x(ℓ) = 0 (ℓ ≠ 0); gauge mean square = Σ_{k∣ℓ}Λ(k)². Σ Λ² ≤ (log ℓ)² ≤ τ(ℓ)ΣΛ²: trivial point lies between 1 and √τ(ℓ) gauge standard deviations above the mean (coherent atypicality).

## TheShellDecomposition
- primePairForm P(a,x) = Σ_{k≤K}Σ_{m,n≤N} a(k)x(m)x̄(n)G(log n − log m − log k). Grouped by ℓ = km: P = Σ_ℓ Σ_n (a⋆x)(ℓ) x̄(n) G(log n − log ℓ) (truncated Dirichlet convolution; kernel of log(n/ℓ) only).
- P = ratioPart (n = km, kernel G(0)) + shellPart (n ≠ km). Gauge action a ↦ aχ_y, x ↦ xχ_y: convolution covariant ((aχ⋆xχ)(ℓ) = χ(ℓ)(a⋆x)(ℓ)); ratio part invariant; shell part has Haar mean 0; gauge average of P = ratio part.
- Pole vector x ≡ 1: (Λχ_y ⋆ 1)(ℓ) = divisor fibre F_y(ℓ) (ℓ ≤ min(K,N)); at y = 0 equals log ℓ.

## TheGaugeExponent (uses ACG TheMoebiusExceptionalSetIsComeagerAndNull; RHTower MobiusMertensAbscissaLittlewood; BVI TheVaughanEmptyLegReadsTheZeroAbscissa)
- gaugeExponent θ_a(x) = inf{θ ≥ 0 : twisted partial sums O((N+1)^θ)}; ∈ [0,1] for |a| ≤ 1. θ ≤ ½ ⇔ ACG half-power law at x; Haar-a.e. θ ≤ ½.
- Möbius: θ_μ(0) = Θ = sup Re ρ exactly (Littlewood up; power bound on Mertens bounds Θ). RH ⇔ θ_μ(0) ≤ ½ (typicality of the trivial point).
- {θ_μ > ½} is Haar-null and residual; {θ_μ ≥ ¾} residual (strong exceptional set dense G_δ). Liouville point (χ = (−1)^Ω) has θ_μ > ½.

## FactorialRatiosHaveBoundedMultiplicity
- m < p² ⇒ v_p(m!) = ⌊m/p⌋. Σ⌊c_j/p⌋ ≤ ⌊Σc_j/p⌋ ≤ Σ⌊c_j/p⌋ + (#T − 1).
- Balanced factorial ratio A = ∏(a_i n)!/∏(b_j n)! (Σa = Σb): v_p(A) ≤ #T − 1 for all p with p² > a_i n, b_j n (uniform in n). Central binomial: v_p ≤ 1 for p² > 2n. No multiplicity growth above √length (contrast: Stepanov/Frobenius multiplicity ≈ √q).

## TheCoherencePrinciple
- Twisted statistic S(x) = Σ c(n)χ_x(n): gauge mean c(1) (or 0), mean square Σ|c|², S(0) = Σc. c ≥ 0 ⇒ |S(x)| ≤ S(0) (trivial point maximizes). 0 ≤ c ≤ L ⇒ S(0)Σc² ≤ L S(0)² (excess ≥ √(S(0)/L) standard deviations).
- Prime source on [1,N]: mean 0, mean square ΣΛ², value ψ(N); ψ(N)ΣΛ² ≤ log N·ψ(N)² (pole = coherent excess ≥ √(ψ(N)/log N) s.d.).
- Diamagnetism: nonnegative a, x, G ⇒ |P(gauge-transformed)| ≤ P(trivial) and same for shell part. In Weil's form (prime part subtracted) trivial point minimizes energy on nonnegative data; arithmetic content lives on signed nonpolar directions.

## TheArchimedeanLineCarriesTheExponent
- Σ_{i<N}(i+1)^{θ−1} ≤ (1 + 1/θ)(N+1)^θ (θ > 0). Abel transfer: partial sums O((N+1)^θ), weight |w| ≤ 1 with |Δw| ≤ B/(n+1) ⇒ weighted partial sums ≤ C(1 + B(1 + 1/θ))(N+1)^θ.
- verticalShift t: twist n^{it}; |(n+1)^{it} − n^{it}| ≤ 2|t|/(n+1). Gauge exponent invariant under x ↦ x + verticalShift t (for |a| ≤ 1).
- θ_μ(n^{it}) = Θ for every t; RH ⇔ θ_μ(verticalShift t) ≤ ½ for any one t. Archimedean place cannot separate 0 from its vertical shifts.

## TheGaugeExponentIsATailInvariant
- twist reads prime coordinates: χ_y(q) = fourier(y_q); points agreeing on primes dividing n agree at n.
- Split off prime p: S_y(N) = A_y(N) − χ_y(p)A_y(⌊N/p⌋), A = twisted Möbius sum over n coprime to p (μ(pm) = −μ(m) if p∤m). Inversion A_y(N) = Σ_k χ_y(p)^k S_y(⌊N/p^k⌋). A_y independent of χ(p). Bound transfer |A| ≤ C2^θ(1 − p^{−θ})^{−1}(N+1)^θ.
- Changing a gauge point at one prime, or finitely many primes, preserves the Möbius exponent; every finite flip of the trivial point has exponent Θ. With vertical-shift invariance: the class of 0 (finite modifications + vertical shifts) is dense and shares exponent Θ.

## TheAdamsOperations
- adams k x = k·x: χ_{ψ^k x}(n) = χ_x(n)^k = χ_x(n^k); ψ^kψ^l = ψ^{kl}.
- ψ^q fixes x ⇔ χ_x(n)^q = χ_x(n) ⇔ χ_x(n)^{q−1} = 1 (values in (q−1)-th roots of unity); primes suffice. ψ² fixes only the trivial point; every ψ^k fixes 0. Dirichlet gauge point of order dividing d fixed by ψ^{d+1}; Liouville point fixed by ψ³. Frobenius equation x^q = x lives on the gauge torus (characters), not on ℤ.

## TheMajorArcsOfTheShells
- Level-q character average of twist pair χ(km)χ̄(n) (all coprime to q) = φ(q)·[km ≡ n mod q].
- Level-q average of prime pair form (supports coprime to q) = φ(q)·(form restricted to km ≡ n mod q). Shell pair n = km + j survives iff q ∣ j. Ratio part invariant at every level. Finite gauge subgroups keep the major-arc shells (q ∣ shift); Haar keeps none.

## AffineInvariantKernelsAreTrivial
- K invariant under all dilations (K(am,an) = K(m,n)) and successor (K(m+1,n+1) = K(m,n)) takes only three values: K(1,2) above diagonal, K(2,1) below, K(1,1) on it (translate (m,n) to (dm, d(m+1)), dilate, translate). Arithmetic kernels must break one invariance; Weil kernel keeps dilations, breaks successor (shell structure).

## TheExponentIsNotGaugeInvariant
- Some point has θ_μ ≤ ½, some θ_μ ≥ ¾ ⇒ θ_μ not constant. Any gauge-translation-invariant Φ bounding θ_μ everywhere has Φ(0) ≥ ¾ (no multiplicative certificate reaches RH).

## TheLiouvillePointsHaveExponentOne
- Twin tail (finitely many coordinates kept, χ(p) = −1 elsewhere): twisted Möbius sums ~ L·N, L ≠ 0 (pole of ζ(s)/ζ(2s)) ⇒ exponent exactly 1. Liouville point (χ(p) = −1 ∀p) exponent 1.
- Two dense classes: twin tails (exponent 1) and the class of 0 (exponent Θ). Any bound reading only finitely many coordinates is ≥ 1 everywhere.

## TheGaugeExponentZeroOneLaw (uses HTGeometry FiniteModificationZeroOne, TorusConditionalProductL2)
- Sublevel sets of exponent measurable (countable ∩ of countable ∪ of closed sets). IsTailInvariant: exponent ignores finitely many prime coordinates; one-prime invariance suffices; Möbius is tail invariant.
- Haar = infinite product of circle Haar; zero-one law: Haar{θ_a ≤ θ} ∈ {0,1} for bounded tail-invariant a. typicalExponent ≤ ½ and θ_a(x) = typical a.e.

## TheFiniteGaugePointsSampleHaar (uses BVI LargeSieveWithTheMontgomeryVaughanConstant)
- Rough source (prime factors > R): Dirichlet gauge point of conductor ≤ R acts as its character. Large sieve: Σ_{q≤R}(q/φ(q))Σ_{χ primitive}|Σ c_n χ(n)|² ≤ (N + R² − 1)Σ|c_n|² = (N + R² − 1)·Haar mean square. Conductors up to √N sample Haar within factor 2 (gauge form of Bombieri–Vinogradov); controls special points on average, never 0 alone.

## TheDirichletPointsCancelThroughPeriodicity (uses RHTower DirichletCharacterPartialSumBound)
- B_P(N) = Σ_{n≤N, no prime of P divides n} χ_x(n). Descent: B_P(N) = B_{P∪{p}}(N) + χ(p)B_P(⌊N/p⌋); inversion over powers of p; each descent costs factor log₂N + 1.
- At a nonprincipal Dirichlet gauge point: B over primes of q = character sum, ≤ q + 1; full sum |Σ_{n≤N} χ_x(n)| ≤ (q+1)(log₂N + 1)^{ω(q)} = O_δ(N^δ). Constant source: exponent 0 at every nonprincipal Dirichlet point, exponent 1 at trivial point (sum = N+1, the pole). Special points can be better than typical; additive structure at the point itself produces cancellation (periodicity) or coherence (successor invariance).

## TheTypicalExponentIsOneHalf (uses HTGeometry FourthMomentEscape; PNTPlus Consequences)
- Gauge Parseval with repetitions: ∫|Σ d_t χ(m_t)|² = Σ_{m_t = m_u} d_t d̄_u. Product rigidity on {1} ∪ primes ⇒ ∫|Y|⁴ ≤ 2(∫|Y|²)² for sums on {1} ∪ primes. Paley–Zygmund: b + Σ_{p∈P} w_p χ(p) (|w_p| = 1) has |·|² > #P/2 with probability ≥ 1/8.
- Integers n ≤ 2M with prime factor in (M, 2M] are those primes ⇒ translating by y supported on top primes moves only those terms: S_{2M}(x + y) = B(x) + Σ_{top p} a(p)χ_x(p)χ_y(p). Translation averaging lemma: fibrewise lower bound ⇒ Haar lower bound.
- For a unimodular-at-primes source, μ{|S_{2M}|² > #T/2} ≥ 1/8 (T = primes in (M,2M]). PNT: #T eventually exceeds K(2M+1)^a for every a < 1. Hence no level θ < ½ is typical: typicalExponent = ½ for every bounded source with |a(p)| = 1; a.e. exponent exactly ½ for tail-invariant ones (Möbius). RH ⇔ θ_μ(0) ≤ typicalExponent.

## TheSpecialPointsOfTheConstantSourceAreAtypical
- Constant source tail invariant (one-prime change inverted through local factor 1 − χ(p)p^{−s}, geometric series). Typical exponent ½, a.e. exponent ½.
- Special locus: nonprincipal Dirichlet point + vertical shift ⇒ exponent 0; principal Dirichlet point (finite modification of 0) + vertical shift ⇒ exponent 1 (pole). No special point is typical for the constant source. Trivial point atypical (1) for constant source; for Möbius RH ⇔ typical.

## TheTrivialPointIsNeverBetterThanTypical (uses RHTower MertensSquareRootOmega)
- At 0 the twisted Möbius sum is Mertens M(x); M(x) ≠ o(√x) ⇒ θ_μ(0) ≥ ½ = typical ⇒ Θ ≥ ½. RH ⇔ θ_μ(0) = typicalExponent (extremal: trivial point sits at the a.e. floor). Finite flips and vertical shifts of 0 also ≥ typical. Whether ½ is the floor on all of G is open.

## TheSpecialLocusReadsGRH (uses RHTower TwistedMertensLittlewood, TwistedMertensOrderLowerBound, TwistedMobiusZeroObstruction, TwistedOrderLawExact, DirichletLZeroHalfPlane)
- coprimeMoebiusSet C_P(N): Möbius twisted sum over n with no prime of P. Descent C_P = C_{P∪p}(N) − χ(p)C_{P∪p}(N/p); inversion C_{P∪p}(N) = Σ_k χ(p)^k C_P(N/p^k).
- Power bounds (θ > 0) pass through one prime in both directions, hence through any finite prime set. Coprime-to-q sum at Dirichlet gauge point = twisted Mertens Σ χ(n)μ(n).
- Twisted-Mertens power bound α bounds zero abscissa Θ_χ ≤ α (Hermitian square → Laplace decay contradicts zero right of α). Θ_χ ≥ ½. Möbius exponent at primitive nonprincipal Dirichlet point = Θ_χ; never better than typical; typical ⇔ GRH for χ; constant along vertical line.

## TheSpecialLocusIsTypicalOnAverage (uses BVI LargeSieveWithTheMontgomeryVaughanConstant)
- Large sieve: Σ_{q≤R}(q/φ(q))Σ_{χ primitive}|C_q(N)|² ≤ (N + R²)(N+1). Atypical points (|C_q(N)|² > V) number ≤ (N+R²)(N+1)/V; with R² ≤ N+1 and V = (N+1)^{1+2ε}: ≤ 2(N+1)^{1−2ε} of ~N points. Average typicality, unconditional; not an exponent statement for any fixed point (exceptions may move with N).

## TheLiouvillePointIsTheAntipode (uses PNTPlus Consequences)
- Prime gauge sum S_N(y) = Σ Λ(n)χ_y(n); S_N(0) = ψ(N). Liouville point: S_N(ℓ) + S_N(0) = 2ψ(√N) (only even prime powers survive). PNT: S_N(0)/N → 1, S_N(ℓ)/N → −1; eventually Re S_N(ℓ) < 0 < Re S_N(0). Both coherent of size N: no size statement separates them; only the sign of the boundary/pole term does.

## TheEscapeStateLeansToTheLiouvillePoint (uses BVI CoprimeSquarefreeDensityAndMobiusDilationMeans)
- ∫|S_N(x)|²χ_x(a) dx = Σ_{m≤N/a} μ(m)μ(am) (dilation correlation). Divided by N → μ(a)d(a)/a, d(a) = (6/π²)∏_{p|a} p/(p+1). Total mass → 6/π². At prime p: → −(6/π²)/(p+1) < 0 — the escape state (|S_N|²dx/N limit) tilts toward χ(p) = −1 (Liouville point). Escape state is an Euler product: multiplicative, blind to zeros; off-line energy is visible only at the point 0.

## TheLiouvilleTwinInequality (uses RHTower SquarefreeCounting)
- Liouville twin y = x + ℓ: twist gains (−1)^Ω ⇒ Möbius sum at y = Σ μ(n)²χ_x(n). Squarefree expansion μ² = Σ_{d²|n} μ(d): Σ μ²χ_x = Σ_d μ(d)χ_{2x}(d) Σ_{m≤N/d²} χ_x(m).
- Hyperbola bound (split at d ≈ N^κ, κ = (1 + b/2 − a)/3): sums ≤ C(N+1)^{(1+2a+b/2)/3}. Twin inequality: exp_μ(x + ℓ) ≤ (1 + 2·exp_1(x) + exp_μ(2x)/2)/3.
- Nonprincipal Dirichlet point: constant-source exponent 0 ⇒ twin exponent ≤ ½ unconditionally; twin duality: twin ≤ typical ≤ Dirichlet point. Real χ (χ² = 1): double is a finite flip of 0 ⇒ twin exponent ≤ (2 + Θ)/6.
- χ₄ twin has exponent ≤ (2+Θ)/6 (= 5/12 under RH). If every gauge point had exponent ≥ ½ then Θ = 1: the a.e. value ½ is not a floor on G; any zero-free strip produces points strictly better than typical.

## FactorialRatiosHaveChebyshevPrecision (uses ArithmeticKreinLangerTheory IntegralityProducesLinearCounts; RHTower ThetaPrimeScheduleSpectralObservation, XiMassShellPrimeMass)
- Above √: v_p(A_n) = Landau count L(n,p) = Σ⌊a_i n/p⌋ − Σ⌊b_j n/p⌋; balance ⇒ L(n + kp, p) = L(n, p) (periodic). Multiplicity m on every (n', 2n'] forces multiplicity m on ghost windows {p : n/p ∈ [k+½, k+1)} (pairwise disjoint).
- Ghost ledger: m Σ_{k<K} θ(ghost window k) ≤ log A_n (for cK² ≤ n). Ghost constant Σ_{k<K}(2/(2k+1) − 1/(k+1)) = 2(H_{2K} − H_K) → 2 log 2. Hence log A_n ≥ (2 log 2 − ε)mn eventually: precision loss at least (2 log 2 − 1)mn on (n,2n]. C(2n,n) attains 2 log 2 (multiplicity 1, log ≤ 2n log 2). Square-root precision needs valuations non-periodic in n mod p.

## TheFunctionFieldCalibrationIsDerived (uses ArithmeticContinuationAndCriticalEnergy TheFunctionFieldCalibration)
- F[T] Möbius (polyMoebius): divisor sums over monic divisors vanish for positive degree (pair d prime to irreducible P with dP). Monic d of degree k divides q^{n−k} monic polys of degree n. Double counting Σ_{k≤n} M(k)q^{n−k} = [n=0] ⇒ degree sums M = 1, −q, 0, 0, … (derives the corpus calibration fqMobiusDegreeSum).
- Möbius sums up to degree N ≥ 1 = 1 − q (bounded: exponent 0, better than typical; no zeros). Σ_{d²|f} μ(d) = μ(f)²; squarefree monic of degree n ≥ 2: q^n − q^{n−1} (twin μλ = μ² grows like size: exponent 1). Twin duality exact at trivial point over F[T].

## TheShellsHaveLevelOfDistributionOneHalf
- Fourier kernel G(u) = Σ g_j e^{it_j u}: P = Σ_j g_j A_j |X_j|² with A_j = Σ a(k)k^{−it_j}, X_j = Σ x(n)n^{−it_j}. |P| ≤ Σ|g_j|·‖a‖₁·|X_j|².
- Large sieve over primitive Dirichlet points of conductor ≤ Q (x rough to Q): Σ (q/φ(q)) Σ_χ |P(aχ, xχ)| ≤ ‖g‖₁‖a‖₁(N + Q²)‖x‖₂². Same bound for shell + ratio part (ratio invariant): on average over conductors ≤ √N the shells cancel the ratio part to within Haar scale (level ½ in large-sieve form). Trivial point is the single term q = 1; level of distribution says nothing about it (Siegel–Walfisz adds per-point zero-free regions).

## AffinePositivityIsThePoleAndHaar
- Real affine-invariant kernel: values A (above), B (below), D (diagonal); form = c(Σv)² + (D − c)Σv², c = (A+B)/2. Nonnegative on all finite sets ⇔ 0 ≤ c ≤ D. Gauge reading: form = c·|twisted sum at 0|² + (D − c)·Haar mean square — positive affine forms are mixtures cδ_0 + d·Haar of the two ends of the torus.
- On pole hyperplane Σv = 0 form = (D − c)|v|²: nonnegative ⇔ c ≤ D; for c < 0 ≤ D exactly one negative direction (the pole): Krein–Langer index ≤ 1 carried by the pole. Arithmetic positivity must come from successor-breaking (shell) part.

## TheShortShellsHaveNoConductor
- Kernel vanishing for |u| ≥ 2/N (N ≥ 6): nonzero shell coefficients with n ≤ N have |n − km| ≤ 2 (atomic Weil kernel at overlap c ≤ 2). For every level q ≥ 3 the Dirichlet average of such shells is 0 (q would divide a nonzero gap ≤ 2). Up to overlap 2 no finite gauge subgroup sees the shells: no singular series; the sign is a property of the trivial point (pole, archimedean terms, gauge charge of 0).
