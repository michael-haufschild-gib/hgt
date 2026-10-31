# 51 ArithmeticHarmonicAnalysis — facts log

## TorsionFourierResolution
- torsionPhase on (ZMod q)^ι: product of standard additive characters. Orthogonality: Σ_t phase(a)·conj phase(b) = q^{|ι|}[a = b].
- Torsion polynomial Σ c_n·phase(e_n): Fourier inversion recovers residueCoefficient (sum of c_n over the fibre e_n = r), collisions included. Polynomial vanishes on the whole grid ⇔ every residue fibre sum is 0. Parseval: Σ_t |poly|² = q^{|ι|} Σ_r |fibre sum|².

## TorsionArithmeticResolution
- valuationResidue: n ↦ (v_p(n) mod q)_{p∈P}. For 0 < n < 2^q every v_p(n) < q ⇒ residues are injective on (0, 2^q) with P = primes below 2^q (shortPrimes).
- Short Dirichlet polynomials (support in (0, 2^q)): each fibre is a single integer ⇒ exact coefficient recovery; vanishing on the full order-q prime torsion grid ⇔ all coefficients 0.
- Boundary: residue(2^q) = residue(1) on every prime set ⇒ binomial phase(2^q) − phase(1) ≡ 0 (exact support threshold 2^q).

## AdamsFixedLocusResolution (uses ArithmeticGaugeTheory TheAdamsOperations)
- torsionGauge embeds the grid into the gauge torus; q·point = 0 ⇒ fixed by ψ^{q+1}. twist at embedded point = torsion phase of valuation residues (support ⊆ P).
- Auxiliary Σ_{n<2^q} c_n χ(n) vanishing at every ψ^{q+1}-fixed gauge point ⇔ all c_n = 0. Boundary: χ(2^q) − χ(1) = 0 at all ψ^{q+1}-fixed points (nonzero binomial). Sharp threshold 2^q for vanishing on Adams fixed loci.

## ResidueNewtonDetection
- Residue Newton coefficient of array c(r, k): Σ_{v: v.1 = r} c(v)∏C(k_i, a_i) (coefficient of Y^a in Σ c(r,k)∏(1+Y_i)^{k_i}). Triangular in total degree: a maximal-order support point is read unchanged. Newton coefficients of order ≤ degree vanish ⇔ c = 0.

## ArithmeticNewtonResolution
- Encode v_p(n) = residue + q·quotient: injective on (0, 2^{qr}). Quotient total order < r there (2^{q·Σquot} ≤ n). Newton coefficients of order < r determine every coefficient of a polynomial supported below 2^{qr}.
- Each Newton coefficient is Fourier-recoverable from torsion samples weighted by ∏C(quot_p, a_p). Equal low-order samples ⇔ equal arrays. (Algebraic coordinates; identification with analytic torus jets is separate.)

## EulerOperatorsLowerMultiplicity
- Any derivation maps I^{m+1} into I^m (Leibniz). Shifted coordinate Euler operator X_i∂_i − s loses ≤ 1 order of ideal multiplicity; a word of length k loses ≤ k. Euler words are linear over finite sums.

## TorsionEulerJetExtraction (uses HTGeometry BorisovGabberVasiuPolynomialJacobian)
- Euler word acts diagonally on monomials with eigenvalue ∏(e_i − s). newtonEulerWord(b, a): shifts b_i + q·j, j < a_i; length Σa_i. On exponents with residue b: weight = q^{Σa}∏a_i!∏C(e_i/q, a_i) (falling factorial).
- Root-of-unity evaluation reduces exponents mod q. Fourier averaging the Euler word image extracts the residue Newton coefficient with nonzero normalization q^{|ι|}q^{Σa}∏a_i!.

## MixedJetMultiplicity (uses HTGeometry MultivariateMultiIndexJet)
- P ∈ (point ideal of x)^r ⇔ all centered Taylor coefficients of degree < r vanish ⇔ all analytic mixed derivatives of order < r vanish at x. Coordinate relabeling preserves point-ideal powers.

## AdamsMultiplicityResolution (uses ACG MultiplicativeObservationIsGaugeInvariant)
- Arithmetic auxiliary polynomial in prime coordinates (primes below 2^{qr}); evaluation at twist(x) on primes = Σ c_n χ_x(n).
- Full point multiplicity r at every point of the order-q torsion grid ⇔ all coefficients below 2^{qr} vanish (Euler word of length < r keeps multiplicity ≥ 1 ⇒ zero samples ⇒ Newton coefficients 0 ⇒ c = 0). Same with analytic mixed jets of order < r; same on the actual ψ^{q+1}-fixed locus of the gauge torus.

## TorsionMultiplicityBoundary (uses HTGeometry RationalOrderComposition)
- (X^q − 1)^r: integer coefficients, monic, degree qr, top coefficient 1; multiplicity exactly r at every q-th root of unity (X^q − 1 separable). Reading exponent j as integer 2^j, support max = 2^{qr} ⇒ the threshold 2^{qr} is sharp. (X_i^q − 1)^r has full multivariate multiplicity r at every torsion point.

## VerticalJetsMissTransverseDirections
- F(z,w) = log3·(z − 1) − log2·(w − 1) (support at integers 1, 2, 3; real-log coefficients): along the logarithmic line (2^s, 3^s) value and first derivative vanish at s = 0, but ∂_z F = log 3 ≠ 0. Vertical (scalar logarithmic) jets do not control full torus multiplicity for non-algebraic coefficients.

## TwoPrimeHomogeneousLogRigidity (uses RHTower GelfondSchneider; HTGeometry TranscendentalPowerIndependence)
- Transcendental ratio x/y ⇒ {x^j y^{T−j}} linearly independent. For distinct primes p, q: log p/log q transcendental (Gelfond–Schneider) ⇒ fixed-degree homogeneous monomials in log p, log q are independent over ℚ and over algebraic numbers. Mixed-degree relations not covered.

## AlgebraicVerticalFirstJets (uses RHTower LadderNesting; HTGeometry MvPolynomialSmoothEvaluation)
- primeLogTrace: F along s ↦ (x_i p_i^s). Derivative at 0 = Σ x_i ∂_iF(x)·log p_i. Algebraic F and algebraic nonzero x: derivative 0 ⇔ every partial derivative 0 (Baker: prime logs independent over algebraic numbers). Value + first log-jet vanish ⇔ F(x) = 0 and ∇F(x) = 0.

## HigherVerticalJets
- primeLogEuler = Σ log p_i · X_i ∂_i: k-th derivative of trace = trace of (primeLogEuler)^k F. Each application loses ≤ 1 ideal power ⇒ point multiplicity r forces scalar log-jets of order < r to vanish (one direction; converse needs transcendence).

## FiniteScalarJetsDetectArbitraryPrimeSupport (uses RHTower ZeroEstimateOrder)
- Prime-exponent auxiliary P (finite support of exponent vectors): log-frequencies log(primeProduct) are distinct (unique factorization) ⇒ Vandermonde: some derivative of order < |support| is nonzero at every s. Initial jets of order < |support| vanish ⇔ P = 0.

## DyadicSuccessorRigidity (uses ACG MultiplicativeObservationIsGaugeInvariant)
- successorDefect χ(n+1) − χ(n); successorRadius = max over 1 ≤ n < N. |χ(n) − 1| ≤ 2k·radius for n ≤ N, n ≤ 2^k (halving via multiplicativity; one successor step per bit).
- Radius 0 ⇔ χ(n) = 1 for all n ≤ N ⇔ χ(p) = 1 for primes p ≤ N (larger primes free). Distance between two twists: |χ_x(n) − χ_y(n)| ≤ 2k·radius(x − y); zero distance ⇔ agree on primes ≤ N.
