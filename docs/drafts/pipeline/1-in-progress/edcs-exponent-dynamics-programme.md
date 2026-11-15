# Exponent dynamics of the critical strip (EDCS)

- **ID:** edcs-exponent-dynamics-programme
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (programme)
- **Source:** docs/reports/review-1411/fable.md §7.2 (questions E1–E7), §5.2, §6.4, §14 items 1, 2, 9
- **Statement:** Develop the maps on exponents (levers, walls, towers) and the maps between stages (stage maps, loss exponents) of the critical strip; answer E1–E7.

## Goal
A proof of RH is a contraction of [½, 1] with fixed point ½ applied to a seed, or a stage recursion with
bounded cumulative loss. The programme classifies the available maps, their fixed points and prices, and
the classes that provably cannot reach the line. No module has RH as an antecedent; the seed Θ ≤ 7/8 is a
theorem of the corpus.

Lean: `formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/`, umbrella
`ExponentDynamicsOfTheCriticalStrip.lean`, README in the folder.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach
Modules, in order of attack. Status: P = paper proof below, L = Lean compiled and audited.

| # | Module | Question | Status |
|---|---|---|---|
| 1 | MixedTowersOfLeversStayAboveTheBestCentre | principles 2–4; §14 item 9; E4 (convexity) | L |
| 2 | EveryRulerCarriesTheSeedAndEveryLever | principle 1; §14 items 1–5 | L |
| 3 | LeversThatBiteFailInTheWorlds | E7 | L |
| 4 | TransformsSampledOnLogarithmicallyDensePoints | E1 (tool) | L |
| 5 | TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy | E1 | L |
| 6 | TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth | E1 (converse rate law, all packets) | L |
| 7 | WeilsFormIsContinuousInTheLogarithmicEnergy | E1 (tool) | L |
| 8 | StepSamplesCarryWeilsFormOfALipschitzPacket | E1 (tool) | L |
| 9 | TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize | E1 (exactness) | L |
| 10 | TheBestDoublingFactorOfTheMarginIsTwoToTheWidth | E2 (margin) | L |
| 11 | TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung | E6; §14 item 11 | L |
| 12 | TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth | E2 (long moments) | L |
| 13 | TheGaussSumsOfAPrimeFieldCarryStickelbergersValuation | E4, E5 (tool) | L |
| 14 | TheTensorPowersOfAGaussSumReachZetaAtTheRateOfItsOrder | E5 (price law) | L |
| 15 | TheMoebiusSignOfAGaussMonomialIsAHalfIntegralStickelbergerDefect | E4 (parity) | L |
| 16 | TheHeatTimeIsTheWidthTimesTheSpacing | E1 (heat) | L |
| 17 | TheLossOfTheMarginIsBoundedOrPolynomial | E2 (loss exponent zero) | L |
| 18 | TheMoebiusSignCostsHalfAUnitAtSomePlace | E4 (price of the sign) | L |
| 19 | TheShortMoebiusMonomialsPayExactlyHalf | E3, E4 (the wall 3/5 is completion, not arithmetic) | L |
| 20 | TheGaussPairingsArePricedAboveTheSign | E4 (FCT prices dominate the sign; arithmetic barrier c ≥ k/2) | L |
| 21 | TheArtinFunctionOfTheCubeRootsOfTwoCarriesTheSeed | E6 (non-abelian seed) | L |
| 22 | EveryRayClassFunctionOfTheEisensteinFieldCarriesTheSeed | E6 (every ray class Ξ_ψ of ℚ(ω); FCT HeckeHalfPlane K (7/8)) | L |
| 23 | TheHeckeFamilyOfTheRationalsCarriesTheSeed | E6 (second field: HeckeHalfPlane ℚ (7/8)) | L |
| 24 | TheRungsLieOutsideTheSeededFamily | E6 (rungs not quotients of products of finite-order L-functions) | L |
| 25 | TheRungsAreTensorPowersOfTheCubicGaussSums | E5/E6 (ψ₆(𝔭) = conj(g̃_𝔭)^18; rung = tensor power) | L |
| 26 | TheCubicStepanovPolynomialIsIndependent | acid test, order 3 (norm form, cubic descent, independence) | L |
| 27 | TheCubicStepanovCount | acid test, order 3 (three-level Stepanov count) | L |
| 28 | TheCubicCurveCountWithoutWeil | acid test, order 3 (equidistribution; Hasse–Weil for y³ = h(x) over 𝔽_{s²}) | L |
| 29 | TheLFunctionOfACharacterOnASplitPolynomial | acid test (weight χ(Res), extension sums, vanishing, top coefficient q^{(m−1)/2}) | L |
| 30 | TheCubicNormCharacterSumHasTheWeilBound | acid test (Σ_{𝔽_{s²}} χ(N f(x)) = O(D s) by Stepanov) | L |
| 31 | TheAcidTestPassesForCubicCharacters | acid test, order 3: RH for L(χ, f), χ cubic, 3 ∤ deg f, without Weil | L |
| 32 | TheKloostermanSumsAreOrdinary | E4 rank two (K(a) a p-adic unit; eigenvalues ordinary; defects ±1/2) | L |

Open, with the input that is missing:

| Question | State | Missing |
|---|---|---|
| E1 heat | answered on models (M16): no law in w alone; in the dense models (z²+δ²)cos(Lz/2) the heat time satisfies L·Λ_L → δ (width times spacing) | for ζ: a two-sided law has to use the zero density (log γ)/2π |
| E1 mass normalisation, every block size | equivalent to width + cluster law (SRT) | boundedness of the zeros off the line in unit windows |
| E2 contraction | best factor 2^w, best slope loss 2w (M10, M12) ; RH ⇔ doubling factor 1 ⇔ every positive rate ⇔ bounded loss, and the loss is bounded or not O(K^β) for some β > 0 (M17) | a factor below √2 from the gluing calculus; GCW additive loss law holds below the binding energy of the middle only |
| E3 | open | a source outside the Gauss class |
| E4 abelian rigidity | Stickelberger valuation of prime-field Gauss sums in Lean (M13); orbit of valuations v/m (M14); Möbius parity = half-integral defect (M15); the sign costs ½ at some place and the Stickelberger price gives c ≥ k/2 > (k−1)/2: rank one non-centred in this pricing (M18) | the classification of pure Gauss monomials (relations generated by reflection and Hasse–Davenport) and the analytic step from a monomial to a source (Kubota series of order ≥ 4) |
| E5 | answered: tensor side M14 (price law); base change over ℤ = IRW thick-set lag lever, RH ⇔ ZAL ∧ thick bounded lag (IRW riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded), well-foundedness needed (Wolff tower) | inputs: ZAL for base change; a completion below the price for tensor powers |
| E6 | seeds: ζ, every Dirichlet L-function, finite-order Hecke L-functions of ℚ(ω) (MMD), and the degree-two Artin L-function of ℚ(∛2), non-abelian S₃ (M21: bridge MMD HeckeFamily ↔ HeckeLFunctions by ideal coefficients and the identity theorem); every completed ray class Ξ_ψ of ℚ(ω), ψ ≠ 1, and FCT's HeckeHalfPlane K (7/8), trivial characters of every modulus included (M22); second field: HeckeHalfPlane ℚ (7/8) (M23, ray class characters of ℚ are Dirichlet characters); the rungs are outside the multiplicative closure of the seeded family (M24: a_k(p) not an algebraic integer at split p); the rungs are the tensor powers conj(g̃_𝔭)^{18k} of the normalized cubic Gauss sums (M25); frame (3, 6) exact (M11) | the Grössencharacter rung (MMD probe with infinity type); Artin functions of other pure cubic fields need AGZ's reciprocity for m ≠ 2 |
| E7 | answered lever by lever (M3, M3 §4): centre < 2/3 uses D+F; centre < 1 and any bite at depth δ use Ramanujan to n^δ; the seed uses primes beyond Ax+O(x^{14/15}) and Ramanujan to n^{3/8} | — (all three properties together are the hypotheses of GRH; over 𝔽_q they give the line) |
| acid test 𝔽_q[T] | not started | a stage-map proof of the window gap for characters ramified at ∞ |
| Weil matrix exponent 1/8–1/4 | owned by CACT | uniform pole pairing (card cact-whole-space-threshold-onset) |

### Paper proofs

**M1 (levers, walls, mixed towers).**
- Lever for θ: ∀b, θ ≤ b → θ ≤ T(b). For monotone T this is θ ≤ T(θ), i.e. θ ∉ {b : T(b) < b} (gap law).
- Allowed set A(𝒯, s) = {b ≤ s : b ≤ T(b) ∀T ∈ 𝒯}; wall = sup A. Seed and levers put θ in A, so θ ≤ wall.
  For monotone levers sup A ∈ A (b ≤ T(b) ≤ T(sup A)), so the wall satisfies every lever: sharp.
  A is unchanged by closing 𝒯 under composition and pointwise minimum (b ≤ S(b) ≤ S(T(b))).
- Affine frames (c_r, k_r), k_r ≥ 2. A bounded solution of V_r = (c_r + V_{r+1})/k_r with f(k_r − 1) ≤ c_r
  for all r has V_r ≥ f: D_r = V_r − f satisfies k_r D_r ≥ D_{r+1}, so D_r ≥ −M/2ⁿ for all n. Symmetric
  upper bound. Equality V_0 = f forces c_r = f(k_r − 1) for all r (induction on k_r V_r = c_r + V_{r+1}).
- A tower Θ_r ≤ max(σ₀, (c_r + Θ_{r+1})/k_r), Θ_r ≤ S, with σ₀ ≤ V_r has Θ_r ≤ V_r + M/2ⁿ for all n.
- Existence: V_r = Σ_j c_{r+j}/(k_r ⋯ k_{r+j}), summable for 0 ≤ c_r ≤ k_r − 1.
- Gauss class: centres ≥ 3/5 (FCT), so V ≥ 3/5 with equality iff every frame is (3, 6); the constant
  sequence 3/5 is a tower over any sequence of pairings; the wall of the finite-field Gauss levers below
  any seed ≥ 3/5 is exactly 3/5 (the ZMod 7 frame (3, 6) forbids everything above).

**M2 (rulers).** A ruler for w on D: P β ⇔ w ≤ β (β ∈ D). Readings = D ∩ [w, ∞); two rulers agree reading by
reading; (∀b ∈ D, P b → P (T b)) ⇔ (∀b ∈ D, w ≤ b → w ≤ T b) when T preserves D. Seed 3/8 on each ruler of the
corpus: Λ ≤ 9/128, heat threshold ≤ 3/64, M(n) = O(n^β) (β > 7/8), |M_X(½+it₀)| = O(X^{3/8+ε}),
∫₀¹|ζM_X|² = O(X^{3/4+2ε}), long moments T^{4+3θ/4}, T^{6+3θ/4}, no zeros of M_X on compacts right of 7/8,
signal exponent 7/8, two-end depth e^{3v/8}, joint-ancestry gap law, Transfer ⇔ RH.

**M3 (worlds, E7).** A lever valid on a family bites at no abscissa the family realizes. Families:
- integer-norm Euler products (natural coefficients, linear count, continuation to Re s > 1/3, no zero on the
  line): every pair ½ < Θ_∞ < Θ < 2/3 (APD two-scale). No lever bites in (½, 2/3); no bound Θ ≤ G(Θ_∞) below 2/3.
- cosh models (entire, order one, functional equation, reality): every abscissa ≥ ½. No lever bites.
- edits of the primes with count Ax + O(x^{14/15}): zeros exactly on Re s = σ right of 7/8, any σ ∈ (7/8, 14/15).
  The seed is false for an edit.
A frame with centre < 2/3 is a lever in neither of the first two families.
- shifted pairs F_a(s) = ζ(s−a)ζ(s+a), a ≥ 0 (RHTower countermodel: coefficients c_a(n) = Σ_{de=n} d^a e^{−a} ≥ 0,
  Euler product, Λ(s−a)Λ(s+a) symmetric under s ↦ 1−s, c_a(p) ≥ p^a). Zeros of F_a are ρ ± a, so
  sup Re = Θ + a (upper bound from Re ρ ≤ Θ; approximation by ρ + a). Realized: [Θ, Θ+½) ⊇ [7/8, 1)
  (seed and Θ ≥ ½). A map biting at b ∈ [Θ, Θ+½) fails for a = b − Θ, where c_a(n) ≤ d(n) n^a
  (each d^a e^{−a} ≤ n^a) and no C n^ε, ε < a, bounds c_a. A frame with centre < 1 bites at some
  b ∈ (max(Θ, centre), 1) and fails for a pair. For a > 3/8: Θ + a > 7/8, the seed is false.

**M4–M5 (E1, the floor in the logarithmic energy).** Z with |Re ρ − ½| ≤ σ; f continuous, supported in
[−a, a]; E(f) = ∫₀¹ ‖f(·+x) − f‖² dx/x. Then |W(f, f)| ≤ 160 L(a, σ) (E(f) + ‖f‖²),
L(a, σ) = 4(2a + 2 + 2π) e^{2π} e^{σ(2a+3)}. No ε-loss in the rate.
Proof. (i) Weighted sampling: weights m_q ≥ 0 with unit-window sums ≤ W give
Σ m_q|Φ(z_q)|² ≤ W (2a+2π) e^{2π} e^{2σa} ‖f‖². (ii) Φ_{f(·+x) − f}(z) = (e^{−izx} − 1) Φ_f(z);
|e^{−izx} − 1|² ≥ 2e^{−σ}(1 − cos(x Re z)) for 0 ≤ x ≤ 1. (iii) Apply (i) to f(·+x) − f with the weights
m_q/ℓ_q, ℓ_q = log(|x_q|+5), divide by x and integrate over (0,1]. (iv) K(ξ) = ∫₀¹(1 − cos ξx)dx/x ≥ ℓ/4 − 5/4.
(v) Absorb the −5/4 term by (i). (vi) Each zero term lies between ∓(|Φ(z)|² + |Φ(z̄)|²)/2; the weights
1/log(|Im ρ| + 5) sum to at most 160 on unit windows. Ruler: w ≤ β ⇔ W(u, u) ≥ −C(1 + a)e^{2βa}(E + ‖u‖²)
for all sources (receiver: lag family of one bump, E grows linearly in the lag).

**M6 (converse rate law for all packets).** g bounded, supported in an interval of length < 2A:
𝔚_Q(g) ≥ −160 L(A, w)(E(g) + ∫g²). Smoothing lowers h(0) − h(t) at every t, so the floor of the smooth
sources passes to the limit. Step packets on the cells of (R, R + J]: ‖g(·+t) − g‖² ≤ min(4, 6(R+J)t) Σσ²
(a cell moves by ≤ 3(R+J)t of its mass; at each point ≤ 2 cells contribute), so E ≤ 12 log(1 + R + J) Σσ².
Window matrices: N_W + C(1 + log K)² K^θ (1 + log R) has ≤ 1 negative square for θ ≥ w; on R ≤ K^A the
shift C K^{θ+ε} suffices.

**Correction of fable.md §5.2, first lemma.** In the mass normalisation, uniformly in the block size, the
converse rate law is not a consequence of the width: a step packet of block size R resolves heights up to R,
where a unit window may carry C log R zeros off the line; the uniform statement is the width together with a
cluster law (SRT `polarGroundEnergyRate_eq_zetaZeroWidth_or_offLineCopies_cluster`). The factor is
1 + log R and disappears at block sizes polynomial in the ratio.

**M7 (continuity).** Sources u₁, u₂ of aperture a, d = u₁ − u₂, s > 0:
|W(u₁) − W(u₂)| ≤ 160 L(a, w)[(1 + 1/s)(E(d) + ‖d‖²) + s(E(u₂) + ‖u₂‖²)].
Proof. T_q(u) = Φ_u(−z) conj Φ_u(−z̄), Φ_{u₁} = Φ_{u₂} + Φ_d, so
T_q(u₁) − T_q(u₂) = Φ_d conj Φ₂' + Φ₂ conj Φ_d' + Φ_d conj Φ_d'; xy ≤ y²/(2s) + s x²/2; the sample bound of
M5 for d and for u₂.

**M8 (step samples).** F continuous, |F| ≤ M, |F(u) − F(v)| ≤ L|u − v|, supported in (log R, log(R+J)],
R + J ≤ QR; flat_j = e^{u/2} on the cell (log(R+j), log(R+j+1)]; σ_j = ∫ F · flat_j, g = Σ σ_j flat_j (the
projection on the cells); c = L + M, Λ = log Q + 1.
(i) ∫ F g = Σσ_j² = ∫g²; ∫(g − F)² = ∫F² − Σσ_j² ≥ 0.
(ii) ∫ flat_j e^{s/2} ds = 1, so on the cell of a: F(u) − σ_j e^{u/2} = ∫ flat_j(s)[F(u)e^{s/2} − F(s)e^{u/2}] ds and
F(u)e^{s/2} − F(s)e^{u/2} = e^{s/2}[(F(u) − F(s)) − F(s)(e^{(u−s)/2} − 1)], |u − s| ≤ 1/a: |g − F| ≤ c/R.
(iii) Two moduli: ‖Δ_t(g − F)‖² ≤ β and ≤ βNt for 0 ≤ t ≤ 1 give ∫₀¹ ‖Δ_t‖² dt/t ≤ 2β log(1 + N) (the density is
≤ 2βN/(1 + Nt)); with N = 4(R+J)R² the energy of g − F is O(c²Λ log(1 + N)/R²).
(iv) M7 on packets with s = 1/R:
|𝔚_Q(g) − 𝔚_Q(F)| ≤ c² (Λ/R) · 160 L((log Q + 1)/2, w)(16 log(1 + 4(R+J)R²) + 5).
(v) Charges a(h) = ∫ h e^{−u/2}, b(h) = ∫ h e^{u/2} on a window [log R, log R + log Q]:
|a(g − F)| ≤ (c/R) e^{−(log R)/2} log Q, |b(g − F)| ≤ (c/R) e^{(log R + log Q)/2} log Q, the same with M for F;
|a(g)b(g) − a(F)b(F)| ≤ 3c² (log Q)² Q/R.
Neutral forms differ by at most c² · sampleError(Q, R, J),
sampleError = (Λ/R)(160 L(·)(16 log(1 + 4(R+J)R²) + 5) + 6 Q log Q).

**M9 (the margin is a ruler at polynomial block size).** 0 ≤ θ < ½, ρ(K) ≥ K^{10}. Suppose
N_W(3K+1, ρ(K)) + C K^θ has index ≤ 1 for every K ≥ 1 (the margin law of rate θ along ρ). Then w ≤ θ.
Proof. Lag v, K ≍ e^v with the two states of the two ends (binding state e_v, antisymmetric state o_v)
inside the window, translated by log R. If 2 Re S(v) > 2 Re S(0) + (4E m₀ + 1)e^{θv}, both smooth neutral forms
lie below −D·mass − 1, D = |C| K^θ; N(s e + t o) = s² N(e) + t² N(o) and the masses are orthogonal. By M8 the
window matrix on the samples of the plane is at most the smooth form plus
2c₀²(s² + t²)·C₃K⁴(1 + log R)/R ≤ (s² + t²)/2 for K large (1 + log R ≤ 2√R, √R ≥ K⁵). Two negative squares:
contradiction. So 2 Re S(v) ≤ 2 Re S(0) + E' e^{θv} from some lag on, which is w ≤ θ (MAFT rate law).
The sampling error at ratio 3K + 1 is ≤ C₃ K⁴(1 + log R)/R (resolution N = 4(3K+1)R³, 1 + log N ≤ 8(3K+1)(1 + log R),
depth of the window at θ = 1), and K⁴(1 + log R)/R ≤ 2/K for R ≥ K^{10}.
Ruler: for K^{10} ≤ ρ(K) ≤ K^A and β ≥ 0, w ≤ β ⇔ the margin law holds along ρ at every rate β + ε (transmitter: M6).
The infimum of the nonnegative rates of the margin law is w. One sequence of matrices (ρ(K) = K^{10}) reads w.

**M10 (the best doubling factor).** a monotone, a(2K) ≤ λ a(K) + c for K ≥ 1, λ > 1. With d = c/(λ − 1):
a(2ⁿ) + d ≤ (a(1) + d) λⁿ. For 2^m ≤ K < 2^{m+1}: a(K) ≤ a(2^{m+1}) ≤ (|a(1)| + 2|c|/(λ − 1)) λ^{m+1} and
λ^m = (2^m)^{log₂ λ} ≤ K^{log₂ λ}. A level law is a(K) with index(N_W(3K+1, ρ(K)) + a(K)) ≤ 1; raising the levels keeps
it. So a doubling law with factor λ is a margin law of rate log₂ λ, and by M9 w ≤ log₂ λ. A margin law of rate
β ≥ 0 has the monotone levels max(C, 0) K^β with a(2K) = 2^β a(K). At polynomial block size: the infimum of the
factors is 2^w; every factor above 2^{3/8} occurs with no hypothesis; w = 0 iff every factor above 1 occurs.

**M11 (the frame (3, 6) is exact).** FCT: for Re s > ½ the continued correction of the cubic probe vanishes at s
iff the Grössencharacter L-function of the rung η⁶ vanishes at 6s − 3. So x ↦ (3 + x)/6 maps the zero depths of
the rung in Re w > 0 onto those of the correction in Re s > ½; a continuous monotone map commutes with the
supremum of a nonempty bounded set. The rung has zeros in ½ ≤ Re w < 1 and none on Re w ≥ 1 (FCT), so
Θ_corr = (3 + Θ_rung)/6 ∈ [7/12, 2/3], independent of the finite set of primes; Θ_rung ≤ 7/8 ⇔ Θ_corr ≤ 31/48.

**M12 (the best slope loss).** I(θ, T) = ∫₁ᵀ|ζ M_{T^θ}(½+it)|² dt ≤ C_θ T^{a(θ)} with a(2θ) ≤ a(θ) + κθ, κ ≥ 0.
Then a(2ⁿ) ≤ a(1) + κ(2ⁿ − 1), so along θ = 2ⁿ the moments are ≤ C T^{K + 2(κ/2)θ} with K = max(a(1) − κ, 0); the
sharp converse of the slope (CDG) gives w ≤ κ/2. For β ≥ w the exponents 6 + 2βθ (CDG) have a(2θ) − a(θ) = 2βθ.
The least loss is 2w; the loss 3/4 holds with no hypothesis.

**M13 (Stickelberger's valuation, prime field).** K = PadicAlgCl p, ζ primitive p-th root, π = ζ − 1. Teichmüller:
Hensel for X^{p−1} − 1 at x̃ (‖F'(x̃)‖ = ‖(p−1)x̃^{p−2}‖ = 1, ‖F(x̃)‖ < 1 by Fermat) gives a unique root above each unit
residue; uniqueness gives multiplicativity. ‖π‖^{p−1} = 1/p: Φ_p(1) = p = Π_{μ primitive}(1 − μ), and
ζ^j − 1 = (ζ − 1)Σ_{i<j}ζ^i gives ‖μ − 1‖ ≤ ‖ζ − 1‖ and back. Expansion: ζ^{x} = Σ_{k<p} C(x,k)π^k (x < p), so
g(ω^n) = Σ_k c_k π^k, c_k = Σ_x ω(x)^n C(x,k) ∈ ℤ_p. Mod p: k! c_k ≡ Σ_x x^n (x)_k = Σ_j s_j Σ_x x^{n+j} with (x)_k monic
of degree k; Σ_{x∈𝔽_p} x^e = 0 for e < p − 1 and = −1 at e = p − 1. So c_k ≡ 0 (n + k < p − 1) and a! c_a ≡ −1 at
a = p − 1 − n. Then ‖c_k π^k‖ ≤ max(1/p, ‖π‖^k) ≤ ‖π‖^{a+1} for k ≠ a and ‖c_a π^a‖ = ‖π‖^a: ‖g(ω^n)‖ = ‖π‖^a,
‖g(ω^n)‖^{p−1} = p^{−(p−1−n)}. Every K-valued character is ω^n: ω at a generator is a primitive (p−1)-th root.

**M14 (E5: the price law).** χ = ω^n of order m = (p−1)/d, d = gcd(p−1, n), n = sd, gcd(s, m) = 1:
‖g(χ)‖^{p−1} = p^{−(m−s)d}, so ‖g(χ)‖^m = p^{−v}, v = m − s ∈ [1, m−1], gcd(v, m) = 1. The extremal character
χ_m = ω^{(m−1)(p−1)/m} has order m (gcd(m, m−1) = 1) and v = 1. In g(χ_m)^m = χ_m(−1)p∏J (Mathlib) the Jacobi
product has norm 1. log_p‖g(χ_m)‖ = −1/m, so (½ − 1/m)k = k/2 + k log_p‖g(χ_m)‖, and FCT pairingC is the sum over
completed factors of weight plus k log_p‖g(χ_m)‖, plus the rows.

**M15 (E4: the Möbius parity is a half-integral Stickelberger defect).** L = (ω^{n_χ}), S = Σ n_χ, N = p − 1, r = |L|.
By M13 log_p‖g(ω^n)‖ = −(N − n)/N, so the defect r/2 + log_p‖∏ g‖ = S/N − r/2, and ∏ L = ω^S. With (∏ L)² = 1:
N | 2S, 2S = Nq; ∏ L = 1 ⇔ N | S ⇔ q even; defect = (q − r)/2. Möbius parity (∏ = 1, r odd) or (∏ ≠ 1, r even) ⇔
q − r odd ⇔ defect ∈ ½ + ℤ. Hence |defect| ≥ ½: a Möbius-signed monomial is pure at no place above p.

**M16 (E1: the heat time).** Dense models F = (z² + δ²)cos(Lz/2): zeros ±iδ and (2k+1)π/L, width δ. RHTower
cosDefectFlow_collision: real-rooted at δ/L; for 0 < μ < δ and L > 2μ/(δ² − μ²) a zero on iℝ₊ at μ/L. The bound
2x/(δ² − x²) ≤ 2μ/(δ² − μ²) for 0 < x < μ (the difference is 2(μ − x)(δ² + xμ)) gives non-real zeros at every
t < μ/L. So μ/L ≤ Λ_L ≤ δ/L and L Λ_L → δ; with L = 2δ/ε, Λ_L ≤ ε/2: no bound Λ ≥ Φ(w), Φ(δ) > 0, on the models.

**M17 (loss exponent zero is bounded loss).** MAFT: RH ⇔ ∃ C, every window (R, R + J], R ≤ J, R + J ≤ QR, has
N_W + C with ≤ 1 negative square; the windows (ρK, (3K+1)ρK] are of this kind, so RH ⇒ a constant level law.
A constant level C gives doubling laws a ≡ max(C, 0) with every factor λ ≥ 1, so w = 0 (M10) and RH. A doubling law
with factor 1 gives, for a' = max(a, 0), a'(2K) ≤ a'(K) + max(c, 0) ≤ λa'(K) + max(c, 0) for λ ≥ 1: every factor
above one, so RH. The margin law at every rate β > 0 is the ruler at 0 (M9), so RH. Dichotomy: ¬RH ⇒ some rate fails.

**M18 (E4: the price of the Möbius sign).** Conjugates L^t = (χ^t), t ∈ (ℤ/N)^×. For χ = ω^n ≠ 1 the exponent of χ^t
is (t·n mod N) ∈ [1, N − 1] (uniqueness of the exponent in [1, N], ω of order N). The residues t·a and −t·a add to N,
so Σ_t (ta mod N) = |U|·N/2 and Σ_t defect(L^t) = Σ_χ (Σ_t (tn mod N)/N − |U|/2) = 0. t is odd (N even for p odd) and
(∏L)² = 1, so ∏L^t = ∏L and L^t is Möbius-signed; by M15 its defect is in ½ + ℤ. If all were < ½ they would be
≤ −½ and the sum negative. So some conjugate has defect ≥ ½.

**M19 (short Möbius monomials pay exactly ½; towers on the sign line).** Towers with frames (k_r/2, k_r), k_r ≥ K:
V_r = (k_r/2 + V_{r+1})/k_r ≥ ½ + 1/(2k_r) > ½ (M1 lower centre bound for V_{r+1}); centres k/(2(k−1)) ≤ K/(2(K−1)) give
V ≤ K/(2(K−1)) (M1); with K = 2 + 1/ε the value is < ½ + ε. Prices: For r nontrivial characters each exponent lies in [1, N − 1], so
r/N ≤ S/N ≤ r(N − 1)/N and the defect S/N − r/2 lies in (−r/2, r/2). For a Möbius-signed monomial it is in ½ + ℤ
(M15); for r ≤ 3 only ±½ remain. Conjugates are Möbius-signed of the same length, so every conjugate has defect ±½,
and some has +½ (M18): the price is exactly k/2, centre k/(2(k−1)). FCT two_thirds_mul_period_sub_one_le_pairingC
gives c ≥ (2/3)k − 1; k/2 ≥ (2/3)k − 1 iff k ≤ 6: the two lines meet at k = 6, centre 3/5.
Insight: the valuation (arithmetic) price of the Möbius sign allows centres k/(2(k−1)) → ½; the 3/5 wall is where
per-factor completion (one Kubota series per Gauss factor) overtakes it. A source below 3/5 needs a joint completion
of a short Möbius monomial (a theta series or multiple Dirichlet series whose coefficients are products of Gauss sums
of distinct characters) at a period k ≥ 7. Paper status: the interpretation is [D]; the arithmetic is in Lean.

**M20 (FCT prices dominate the sign).** Defect of a monomial = Σ over factors of (½ + log_p‖g(x)‖). For x of order
m ≥ 2, every conjugate x^t has order m (t coprime to N, m | N) and ‖g(x^t)‖^m = p^{−v}, v ≥ 1 (M14), so
log_p‖g(x^t)‖ = −v/m ≤ −1/m. Comps: k(½ + log) ≤ (½ − 1/m)k; rows (m | k so k/m ≥ 1): k(½ + log) ≤ k/2 − 1. Summing:
k·defect(L^t) ≤ pairingC at every t, so the Stickelberger price ≤ pairingC, and with M18 pairingC ≥ k/2.

**M21 (a non-abelian seed).** MMD hecke_nonzero: HeckeFamily.LFunction χ ≠ 0 on Re s > 7/8 for every finite-order
character of ℚ(ω) on its theta-lattice continuation. AGZ: L(s, ρ) for ρ the degree-two Artin character of ℚ(∛2, ω)
is L(s, χ), χ = cubicTwoHecke (ray class mod 6, value ringComplex(twoCubicValue 𝔞)). Bridge: the MMD character with
residue a mod 6 ↦ ringComplex(twoCubicOf a) (unit hom on (O/6)ˣ, trivial on units) has idealCoeff(span a) =
heckeValue(span a); both L-series are sums over nonzero ideals on Re s > 1. Ξ_χ(s)·Γ(s)⁻¹·N^{−s/2} is entire
(1/Γ entire, N^{s/2} nowhere zero) and equals L(s, χ) on Re s > 1; MMD's LFunction is entire (χ nonprincipal); the
identity theorem gives equality everywhere, so a zero of Ξ_χ on Re s > 7/8 would be a zero of LFunction χ.

**M22 (every ray class character of ℚ(ω)).** For ψ a ray class character mod 𝔪 (K imaginary, no real places),
the residue character finiteHeckeWeight on (O/𝔪.fin)ˣ is trivial on global units (ψ((u)) = 1), so
HeckeFamily.Character.ofResidue applies; its ideal coefficient on (a) is the FCT integral weight = heckeValue (a)
(K is a PID). ψ ≠ 1 ⇒ residue ≠ 1 (ray residue classes are surjected by O, IsEmpty 𝔪.inf). Then the M21 bridge
verbatim. Family half-plane: FCT's heckeLFunction = regular part + pole coefficient/(s − 1), so (s − 1)·heckeLFunction
is entire (rayRegular); MMD's poleRemoved χ is entire with poleRemoved χ s = (s − 1)·LFunction χ s off {0, 1};
they agree on Re s > 1 (both are the ideal sum), so heckeLFunction = LFunction off {0, 1}, and hecke_nonzero gives
HeckeHalfPlane K (7/8) (Or.inl ρ ≠ 1 covers the trivial characters).

**M23 (the Hecke family of ℚ).** 𝔪 = (N)𝔪∞. ℤ/N → 𝓞_ℚ/𝔪₀ (ZMod.castHom, char | N since N ∈ 𝔪₀) is onto
(𝓞_ℚ ≅ ℤ) and both have N elements, so it is a ring isomorphism; χ_ψ := finite residue character ∘ it, a
Dirichlet character mod N. For n ≥ 1, n > 0 at the real place, so ψ((n)) = finite weight(n mod N)·sign character(1)
= χ_ψ(n) (integralHeckeWeight_mul_infiniteSign_eq_heckeValue). 𝓞_ℚ has one ideal of each norm, so heckeCoeff n =
χ_ψ(n), heckeL = L(s, χ_ψ) on Re s > 1, and the identity theorem on ℂ ∖ {1} gives heckeLFunction = χ_ψ.LFunction.
MMD dirichlet_nonzero gives HeckeHalfPlane ℚ (7/8).

**M24 (the rungs lie outside the seeded family).** a_k(n) = Σ_{N𝔞=n} ψ₆(𝔞)^k ψ_prim(𝔞); grouping FCT's ideal sum by norm gives
L(w, ψ₆^k ψ) = LSeries a_k on Re w > 1. Split p ≡ 1 (3), p > N(𝔣) (Nat.exists_prime_gt_modEq_one): two ideals P₁ ≠ P₂ of
norm p (AGZ), generators π₁, π₂, P₁P₂ = (p) so π₁π₂ = up, |π_i|² = p (Eisenstein coordinates). ψ₆(π₁) = (π̄₁/|π₁|)⁶,
π̄₁ = p/π₁ = π₂/u, u⁶ = 1 ⇒ ψ₆(π₁)p³ = π₂⁶. ψ(P_i) roots of unity (P_i ∤ 𝔣). If c = a_k(p) were integral:
y' = c p^{3k−1} π₂ u⁵ − ζ₂ π₁^{6k−1} integral with π₁ y' = ζ₁ π₂^{6k} (linear_combination from π₁π₂ = up, u⁶ = 1,
c p^{3k} = ζ₁π₂^{6k} + ζ₂π₁^{6k}); y = y'ζ₁^{m} gives π₁ y = π₂^{6k}; y = ι(π₂^{6k}/π₁), ι : K → ℂ the lift of the
embedding; integral over ℤ ⇒ over O (scalar tower, built with the cyclotomic ℤ-algebra instance) ⇒ in O
(integrally closed) ⇒ π₁ | π₂^{6k} ⇒ P₂ ≤ P₁, contradiction. Identity L(rung)L(g) = L(f) on w > 1 ⇒ coefficients
agree (LSeries.eq_of_LSeries_eventually_eq), at p: a_k(p) + g(p) = f(p) (g(1) = 1, a_k(1) = 1). Products of
heckeL: iterated convolution with δ, coefficients integral (values of a finite group character), value 1 at 1.

**M25 (rungs = Gauss tensor powers).** idealPsiSix P = elemPsiSix(π_P) (P = (π_P), unit-invariance), elemPsiSix π =
(π̄/|π|)⁶, MMD normalizedCubicGauss_cube: g̃³ = −π/|π| ⇒ conj(g̃)^18 = conj(g̃³)^6 = (−π̄/|π|)^6 = ψ₆(P). Rung prime term
at v ∌ λ: conj(g̃_v)^{18k} ψ_prim(v) N(v)^{−w}.

**M26–M28 (acid test, order three).** |E| = Q = 3N + 1. Independence: A₀ + A₁g + A₂g² = 0 (g = h^N) ⇒ norm form
A₀³ + A₁³g³ + A₂³g⁶ − 3A₀A₁A₂g³ = 0 (factor x+y+z); × h², h g³ = h^Q = h(X^Q) ⇒ bivariate identity
h(X)²A₀³ + h(X)h(Y)A₁³ + h(Y)²A₂³ − 3h(X)h(Y)A₀A₁A₂ at Y = X^Q, coefficient degree ≤ 2D + 3(K−1) < Q ⇒ zero in E[X][Y];
cubic descent: π | h(X) irreducible divides A₂, then A₁, then A₀, equation returns ⇒ all zero. Count: three levels,
3JK unknowns, one-level Hasse lemma h^k D^{(k)}(r h^M) = h^M Σ h^{k−i}P_{M,i}D^{(k−i)}r; ℓ·N_ε ≤ (K−1) + 2ND + Q(J−1).
Bound (q = s², s ≥ 3D + 10, ℓ = s, K = ⌊(s² − 2D)/3⌋, J = ⌊(s + 3D + 6)/3⌋): 3N_ε ≤ s² + (5D+4)s. Classes 1, ω, ω²
partition the nonroots ⇒ |3N_1 − s²| ≤ 2(5D+4)s + 3D; #{y³ = h(x)} = #{h = 0} + 3N_1 (cube roots, AGZ).

**M29–M31 (RH for cubic characters).** w(P) = χ(Res(P,f)), Σ_{x∈E} χ(N f(x)) = c_n (norm = Res^{n/d}, fibres of
minpoly). Split squarefree f: s_k = 0 for k ≥ m (translation, Σχ = 0); s_{m−1} g(χ^m) = g(χ)^m Π χ(d_α) (Lagrange,
fibres of the leading coefficient; Z = χ(s)^m Z kills the zero fibre) ⇒ |s_{m−1}| = q^{(m−1)/2} for χ^m ≠ 1.
Over E with |E| = s²: χ(a) depends on a^{(q−1)/3} (a/b a cube), N(y)^{N_F} = y^{N_E}; with ζ = χ(a) ≠ 1 the sum is
T_1 + ζT_ε + ζ²T_{ε²}, 1 + ζ + ζ² = 0 and equidistribution give O(Ds). L* monic of degree m − 1, Newton ⇒ c_n = −Σω^n;
norm_le_of_power_sums_bound at degrees 2k ⇒ |ω| ≤ √q; |Πω| = q^{(m−1)/2} ⇒ |ω| = √q.

**M32 (Kloosterman, rank two).** K(a) = Σ_{x≠0} ζ^{x + a/x} in PadicAlgCl p: K + 1 = Σ(ζ^y − 1) + p, each term of norm
≤ ‖ζ − 1‖ < 1, ‖p‖ = 1/p ⇒ ‖K‖ = 1. Eigenvalues α + β = −K, αβ = p: roots of X² + KX + p are integral (ultrametric),
‖α‖‖β‖ = 1/p and max ≥ ‖α + β‖ = 1 ⇒ {‖α‖, ‖β‖} = {1, 1/p}; defects ½ + log_p‖·‖ = ±½, monomial α^mβ^n: ±(m − n)/2.

## No-go closure
- **Margin in the mass normalisation at every block size** (fable §5.2, first lemma as stated). Not a consequence
  of the width. Insight: the normalisation decides exactness. Survivors, all in Lean: the exact ruler in the
  logarithmic energy (M5), the factor 1 + log R on all window matrices (M6), exactness at polynomial block size (M9).
- **Cluster law from the trivial floor.** Rejected: the terms of the zeros of a cluster have independent phases,
  and a uniform cloud of zeros off the line is invisible to a test of fixed aperture. NO POSITIVE SALVAGE FOUND
  beyond the dichotomy of SRT.
- **A stage map as a producer.** A doubling law and a slope law are rulers (M10, M12). Survivor in Lean: the best
  factor 2^w and the best loss 2w.
- **The squaring identity M_{X²} = 2M_X − ζ M_X² − D_X** (Vaughan with an empty leg at one height). Neutral: the
  quadratic term reproduces the exponent and the defect D_X = Σ_{a,b≤X} μ(a)μ(b)(ab)^{−s}(ζ_{X²/ab} − ζ) is a
  linear combination of readings. No statement beyond the pointwise ruler; not formalized.

## Log
- 2026-11-15 — created; README first draft written. Modules 1–6 compiled, axiom-clean, wired.
- 2026-11-15 — modules 7–12 compiled, axiom-clean, wired.
- 2026-11-15 — M3 §4 (shifted pairs), modules 13–32 compiled, wired (axiom checks dropped at the user's request from M21 on). E4 rank one answered without the
  classification of pure monomials (M18); the classification is needed only to identify completions.
