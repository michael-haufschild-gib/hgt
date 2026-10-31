# ArithmeticOfSquareRootPrecision: mathematical facts

Namespace `GaloisForLFunctions.ArithmeticOfSquareRootPrecision`. 24 modules.

## PrecisionClassesAndTheCount (pure Mathlib)
- Weight a : ℕ → ℝ, partial sum A(x) = Σ_{1≤n≤x} a(n). Count: A(x) − x = O(√x log²x) (for Λ: RH by von Koch). Upper/lower count: one-sided versions; count ⇔ both.
- Precision class of a scale φ: perturbations δ with partial sums O(φ); square-root class 𝒬 for √x log²x. Linear subspace, monotone in φ.
- Stabilizer law: if a satisfies the count, a + δ does ⇔ δ ∈ 𝒬. Two counting weights differ by an element of 𝒬.
- Power threshold: ε n^{−η} ∈ 𝒬 ⇔ η ≥ ½ (ε ≠ 0, η ≥ 0): partial sums ≥ |ε|x^{1−η}/2, and ≤ 2|ε|√x for η ≥ ½ (Σ 1/√n ≤ 2√N).
- Precision rigidity: no weight satisfies the count together with a + εn^{−η}, η < ½; sharp (η ≥ ½ preserves it).
- Finitely supported perturbations lie in 𝒬; a lower bound |Σδ| ≥ c|g| with φ = o(g) excludes δ from class(φ).

## TheCountIsTheRiemannHypothesis (uses RHTower ChebyshevErrorExponentLaw, XiWardGlobalCapAndFiniteHeadArithmetic)
- Count(Λ) ⇔ RH. Upper count alone ⇔ RH, lower count alone ⇔ RH (Landau: both signs of ψ(x) − x reach x^b for every b < Θ = sup Re ρ). One-sidedness costs no precision.
- RH ⇔ Θ = ½.
- Precision exponent θ(a) = inf{θ : A(x) − x = O(x^θ)} ≥ 0 always (step function stays 1/4 from x at n or n + ½). θ(Λ) = Θ; RH ⇔ θ(Λ) = ½. Count ⇒ θ ≤ ½.

## TheBatteryOfTheCount (uses RHTower ChebyshevPsiScaling)
- Linear deviation |A(x) − x| ≥ cx excludes the count; A = κψ + o(x), κ ≠ 1 excludes it (PNT).
- Visible (never satisfy the count): cΛ, c ≠ 1; Liouville twin λΛ (−ψ + O(ψ − θ)); every mixture (1 − t)Λ + tλΛ, t ≠ 0 (partial sums (1 − 2t)ψ + o(x)); every weight equal to λΛ beyond some point (cofinite flips).
- A prime tower carries ≤ log x of partial sum; rescaled Euler factors c·Λ1_{p^ℕ} lie in 𝒬.
- Invisible (count after move ⇔ RH): finite modifications; deleting/flipping/rescaling an Euler factor; Λ + εn^{−η}, η ≥ ½.
- Λ + εn^{−η} (ε ≠ 0, 0 ≤ η < ½) never satisfies the count, unconditionally: the count would make ψ(x) − x eventually of sign −ε and size x^{1−η}, against Littlewood's oscillation. Count(Λ + εn^{−η}) ⇔ RH ∧ η ≥ ½.
- battery_classification: the count selects Λ only modulo 𝒬; it is a tail statement blind to every finite set of Euler factors.

## TheDecidingInputTheorem (uses RHTower PrimeShortIntervalsSeventeenThirtiethsUnconditional)
- Any property S of weights implying the count is: parity-breaking (fails for λΛ); precision-faithful (never S(a) ∧ S(a + εn^{−η}), η < ½); of unbounded aperture (every finite window extends to a weight failing S, via Liouville tails); stabilizer ⊂ 𝒬.
- Hence S fails at Λ if twist-stable; holds for no weight if determined by a finite window or stable under one move outside 𝒬.
- Σ_{n≤x} n^{−η} ≤ 1 + x^{1−η}/(1 − η); = o(x) for 0 < η < 1.
- Producers are precision-blind: for ε ≠ 0, 0 < η < ½, Λ + εn^{−η} satisfies PNT and the Guth–Maynard short-interval law ψ(x + x^α) − ψ(x) ∼ x^α for every α ∈ (17/30, 1), and fails the count. Every error law O(E) with x^{½+κ} = O(E) is inherited by a weight failing the count.

## TheIntegralityLatticeOfTheHorizon (uses ArithmeticEffectivityTheory TheStepanovMethodOverZ)
- Bézout for reciprocals: integer combinations of 1/b_i reach exactly 1/lcm(b_i); every combination lies in lcm⁻¹ℤ.
- Nair functional P ↦ ∫₀¹P. Integrality lattice: {∫₀¹P : P ∈ ℤ[X], deg P ≤ n} = lcm(1..n+1)⁻¹ℤ exactly. Least positive value 1/lcm(1..n+1) attained; ψ(n + 1) = max log(1/∫₀¹P) over positive integrals.
- The Stepanov–Nair method loses nothing at the integrality step; precision is lost in the analytic ceiling certifying a small positive integral.

## TheIntegralityExponentIsTheZeroWidth
- Siegel half at scale φ: for large n some P, deg ≤ n, with 0 < ∫₀¹P ≤ e^{−(n+1) + Cφ(n+1)} (small auxiliaries exist). Liouville half: every positive Nair integral ≥ e^{−(n+1) − Cφ(n+1)}.
- 1/lcm(1..N) = e^{−ψ(N)}. Siegel half ⇔ ψ(N) ≥ N − Cφ(N) (lower count); Liouville half ⇔ ψ(N) ≤ N + Cφ(N) (upper count); extends to real x for admissible (monotone, nonnegative, eventually ≥ 1) scales.
- RH ⇔ Siegel half at √x log²x ⇔ Liouville half at √x log²x.
- Integrality exponent = zero width: both halves hold at x^θ for θ > Θ, both fail for θ < Θ; inf{θ} = Θ for each half. Θ < 1 ⇔ Siegel (or Liouville) half at some θ < 1.
- Integrality reaches exactly the zero width in each half; what is open is a certificate (ceiling) for a small positive integral.

## FixedPolynomialIdealsRetainIntegralityPrecision (uses HTGeometry ContinuousSquareIntegralPositive)
- Rational moments ∫₀¹x^jQ; clearing lower denominators leaves an integer plus a fixed residue leadingCoeff(Q)(−1)^m m!/(j + m + 1).
- For every nonzero Q ∈ ℤ[X] there is C₀ > 0: for n ≥ 2 deg Q some multiple of Q of degree ≤ n has ∫₀¹ = C₀/lcm(1..n+1). Least positive integral in the ideal (Q) lies in [1/lcm, C₀/lcm].
- Fixed divisibility preserves both halves at every admissible scale, the power-scale sets, the exponents (= Θ), and the square-root criteria (each ⇔ RH).

## IntegerDirichletPolynomialsAtArithmeticPoints (uses HTGeometry ExponentialPolynomialZeroBound)
- Integer Dirichlet polynomial D(σ) = Σ_{i<N} a_i(i+1)^{−σ}. Nair functional = value at the pole: ∫₀¹P = D_P(1).
- Liouville inequality at s = m ≥ 1, sharp: lcm(1..N)^m·D(m) ∈ ℤ, nonzero |D(m)| ≥ lcm^{−m} = e^{−mψ(N)}, attained (lcm of m-th powers = m-th power of lcm). Values at s = m form lcm^{−m}ℤ.
- D(−k) ∈ ℤ. Zero estimate: nonzero D has fewer real zeros than nonzero coefficients (Rolle for exponential polynomials); |D(−k)| ≥ 1 for some k < N.
- Siegel's lemma: for 0 < M < N a nonzero D of length N vanishing at 0, −1, …, −(M−1) with height ≤ (N^M)^{M/(N−M)}; M = N impossible.
- Integrality acts only at s ∈ ℤ: exact lattice at s ≥ 1, integer values at s ≤ 0; at precision it speaks through ψ(N), i.e. at the zero width; never at a nontrivial zero.

## TheLiouvilleTwinIsARatioOfHorizonTorsions
- λΛ = 2Λ1_{Ω even} − Λ; even part of Λ is carried by squares: Σ_{m≤n} Λ1_{Ω even} = ψ(⌊√n⌋). Exact identity Σ_{m≤n} λΛ(m) = 2ψ(⌊√n⌋) − ψ(n).
- lcm(1..⌊√n⌋)² | lcm(1..n); exp(Σ λΛ) = 1/|ℤ/r_n|, r_n = lcm(1..n)/lcm(1..⌊√n⌋)²: the twin's horizon value is a reciprocal group order. Twin fails the count: 2ψ(√n) − ψ(n) − n = −2n + O(√n).

## WherePrecisionIsLost
- Chebyshev transform T_a(n) = Σ_{d≤n} a(d)⌊n/d⌋ = partial sum of a∗1. T_Λ(n) = log n! exactly; T determines the weight (precision class {0}); a nonnegative perturbation at d₀ moves T by ≥ δ(d₀)⌊n/d₀⌋ (linear).
- Stirling: 0 < log n! − (n log n − n) ≤ 1 + ½ log n.
- Count = Möbius inversion: A(n) = Σ μ(k)T_a(⌊n/k⌋); ψ(n) = Σ μ(k) log⌊n/k⌋!.
- Inversion unbounded at every precision: for θ ≥ 0, x ≥ 1 some E with |E(y)| ≤ y^θ inverts to ≥ π(x); no uniform bound Cx^{θ'} with θ' < 1. All precision is lost in the inversion; a power saving must use the arithmetic of the Stirling error with μ-cancellation.

## CurvesCalibrateThePrecisionExponent (uses ACS UpperLefschetzBounds…, TheWeilFloorOfACurveIsItsZeroWidth; ArithmeticEffectivityTheory TheHyperellipticCalibration)
- Curve datum: N_k = q^k + 1 − q^{k/2}Σβ_i^k. Count at precision θ (|N_k − q^k − 1| ≤ Cq^{kθ}) ⇔ every |β_i| ≤ q^{θ−½}; the lower half alone forces this (one-sided power-sum bound bounds all moduli).
- Precision exponent = ½ + max log|β_i|/log q ≥ ½ (functional equation pairs reciprocal moduli); = ½ ⇔ unitary.
- Odd hyperelliptic data (Stepanov) have exponent exactly ½.
- Golden datum: N_k/5^k → 1, but count at precision θ ⇔ θ ≥ ½ + log φ/log 5. Relative-error counts cannot see the sign over 𝔽_q either.
- Upper half blind to real outer eigenvalues: without one, upper square-root count ⇒ unitary; golden satisfies N_k ≤ q^k + 1 at every precision and fails the lower half. Over ℤ each half is RH (no real zero in (½, 1)).

## TheGaugeStabilizerOfTheCount
- Lower count is monotone in the weight. If a ≤ Λ pointwise: Count(a) ⇔ RH ∧ Λ − a ∈ 𝒬 (covers sign twists, Euler deletions, Liouville mixtures t ∈ [0, 1], cΛ with c ≤ 1).
- Sign gauge of a prime set F: (−1)^k log p at p^k for p ∈ F. Defect partial sums between 2θ_F and 2θ_F + 2(ψ − θ). Count(signGauge F) ⇔ RH ∧ θ_F(x) = Σ_{p≤x, p∈F} log p = O(√x log²x). Finite F passes; all primes do not.
- Torus gauge cos(2πk t_p) log p: count ⇔ RH ∧ gauge distance Σ_{p≤x}(1 − cos 2πt_p) log p = O(√x log²x). The arithmetic point is distinguished from gauge neighbours only at square-root gauge distance.

## EveryRealGaugeHasAComplexCountLift
- Complex count: both real and imaginary parts at square-root precision. Complex torus gauge e^{2πik t_p}Λ(p^k): count ⇔ RH ∧ cosine deficit O(√x log²x) ∧ signed prime sine current Σ_{p≤x} sin(2πt_p) log p = O(√x log²x). Proper prime powers change the imaginary part by ≤ ψ − θ.
- Conjugating a whole Euler factor (t_p ↦ −t_p) preserves every real coefficient. Greedy conjugation against the running sine current keeps it ≤ log x at every horizon (balancedGauge).
- Every real gauge has a complex lift with exactly the same count criterion; the image of complex-count gauges under Euler conjugation is exactly the real stabilizer; the lift can keep any finite prefix of phases.

## ProductConjugationPrecisionIsTheMeanCurrent (uses HTGeometry LogarithmicIndependentSigns)
- Independent biased conjugation of Euler factors: random sine current minus its deterministic mean is O(√x log²x) almost surely (for any bias).
- A.s.: complex count ⇔ real count ∧ mean current O(√x log²x) ⇔ RH ∧ gauge distance ∧ mean current at square-root precision. Fair conjugation has zero mean: almost every fair conjugation (also preserving any finite prefix) is a complex count lift of its real source.

## ThePrecisionLedgerOfTheCount
- RH TFAE (8): RH; Count(Λ); upper count; lower count; precision exponent ½; Siegel half at √x log²x; Liouville half at √x log²x; Count(Λ with Euler factor at 2 deleted).
- Θ = precision exponent of Λ = Siegel exponent = Liouville exponent.
- Θ < 1 ⇔ ψ − x = O(x^θ) for some θ < 1 ⇔ Siegel half at some θ < 1 ⇔ Liouville half at some θ < 1.

## SupNormCeilingsForceVanishingAtSmallRationals
- b^nP(a/b) ∈ ℤ for deg P ≤ n ⇒ P(a/b) = 0 or |P(a/b)| ≥ b^{−n}. A sup-norm ceiling below b^{−n} on [0, 1] forces P(a/b) = 0 at every a/b ∈ [0, 1].
- For every θ < 1, C: for large n every integer P of degree ≤ n with sup_{[0,1]}|P| ≤ e^{−(n+1) + C(n+1)^θ} vanishes at 0, ½, 1. Sup-norm certificates for a zero-free strip must vanish at rational points of height 2 (Stepanov-like); what sup-norm ceilings reach is the integer Chebyshev problem on [0, 1].

## OneSignedPerturbations
- Upper count antitone, lower count monotone in the weight. Upper count for a majorant b ≥ Λ ⇒ RH; lower count for a minorant a ≤ Λ ⇒ RH. For b ≥ Λ: Count(b) ⇔ RH ∧ b − Λ ∈ 𝒬. A sieve majorant of the primes at square-root precision is RH.
- For δ ≥ 0: partial sums O(x^θ) ⇒ abscissa of absolute convergence ≤ θ; abscissa < σ ⇒ partial sums O(x^σ). 𝒬 ∩ {δ ≥ 0} lies between Re s > ½ conditions: abscissa < ½ ⇒ δ ∈ 𝒬 (invisible); δ ∈ 𝒬 ⇒ abscissa ≤ ½; abscissa > ½ ⇒ visible.

## TwoPrimeTowersSeeEveryOrdinateDifference (uses RHTower Matveev EffectiveBaker, LiouvillePointReachability)
- Liouville separation |a log p − b log q| ≥ 1/max(p^a, q^b) (integrality, exponentially small in height). Baker: |k₁ log q − k₂ log p| ≥ c(2 + |k₁| + |k₂|)^{−C} (polynomial). Dirichlet: some 0 < k₁ ≤ n gives ≤ log p/(n + 1): polynomial decay is the true shape.
- One tower always aliases (Δ = 2π/log p). Two-prime non-aliasing law: |Δ log p − 2πk₁| log q + |Δ log q − 2πk₂| log p ≥ c·min(|Δ|, (2 + |Δ|)^{−C}) for all Δ, k₁, k₂ (elimination identity 2π(k₁ log q − k₂ log p) = e_q log p − e_p log q). Two towers certify ordinates of height ≤ T with margin polynomial in T; integrality alone gives e^{−O(T)}.

## MonotoneErrorsInvertAtMertensPrecision (uses RHTower MobiusMertensLittlewood, MertensSquareRootOmega)
- Abel summation against μ with Mertens function M. Monotone inversion law: E monotone, |E| ≤ B on (0, x], |M(k)| ≤ K ⇒ |I_x(E)| ≤ 3BK.
- Constant errors invert to M(x) = Ω±(√x): no exponent below ½. RH ⇔ for every δ monotone errors bounded by 1 invert to O(x^{½+δ}). Inversion with arithmetic input has exactly Mertens precision: square-root on monotone errors is RH, none on oscillating ones.

## TowerPositivityIsPrecisionExact (uses HKT IndexZeroSelectsTheVonMangoldtWeight)
- TowerIndexZero p λ: every C² compact generator has tower kernel of index zero. ⇔ RH ∧ λ = Λ on n ≥ 2. Implies the count, so it passes the deciding-input tests.
- Stabilizer trivial: Λ + δ tower positive ⇔ RH ∧ δ = 0 on n ≥ 2 (precision class {0}).
- Gap: Λ + 1/n satisfies the count ⇔ RH, and is never tower positive. Precision is not monotone along equivalences: at Λ both are RH; as properties of weights, the count sees 𝒬, positivity sees every coefficient.

## TheStirlingErrorSplits
- ψ(n) = I_n(log⌊·⌋!). log⌊y⌋! = F(y) + G(y) + h(y), F(t) = t log t − t; G monotone with 0 ≤ G ≤ 1 + ½ log y; sawtooth h(y) = F(⌊y⌋) − F(y) ∈ [−log y, 0].
- Stirling split: |M(k)| ≤ K ⇒ |ψ(n) − I_n(F) − I_n(h)| ≤ 3(1 + ½ log n)K. The monotone part inverts at Mertens precision; remaining precision lives in I(F) and I(h).

## TheSmoothTermInvertsToMobiusMoments
- I_x(F) = x((log x − 1)m(x) − ℓ(x)), m = Σ μ(k)/k, ℓ = Σ μ(k) log k/k.
- |I_n(h)| ≤ n log n − log n! < n (trivial linear size; cancellation must come from μ).
- Arithmetic Chebyshev ledger: |ψ(n) − n((log n − 1)m(n) − ℓ(n)) − I_n(h)| ≤ 3(1 + ½ log n)K. ψ is computed from the two Möbius moments, the sawtooth inversion, and the Mertens function.

## FiniteAperturePositivityCannotDecide (uses SquareRootThreshold WindowCertificatesAndThePrimeWeight)
- Aperture-A positivity (tests supported in [−A, A]) reads λ only on n ≤ e^{2A}; determined by a finite window.
- If aperture-A positivity implied the count, RH would fail (it would hold for no weight, but under RH Λ is fully Weil positive).
- Every weight is aperture-3/10 positive (below log 2/2 positivity is weight-blind), including the Liouville twin.
- Positivity spans the precision scale: weight-blind at small aperture, window-determined at finite aperture, exact on a whole tower.

## TheSuccessorEntersOnlyModuloTheSquareRootClass
- Successor weight 1: partial sums ⌊x⌋, precision 0. Count(a) ⇔ a − 1 ∈ 𝒬. For any u with u − 1 ∈ 𝒬 (successor model, e.g. over-regular Beurling count): Count(a) ⇔ a − u ∈ 𝒬. If u − 1 ∉ 𝒬 no counting weight is within 𝒬 of u.
- RH ⇔ Λ − 1 ∈ 𝒬. The count uses only the class of the integer count mod 𝒬; integer-count precision cannot decide the prime count; the deciding input must come from the prime side.
