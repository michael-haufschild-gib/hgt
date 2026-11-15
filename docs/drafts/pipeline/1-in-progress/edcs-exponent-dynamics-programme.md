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

Open, with the input that is missing:

| Question | State | Missing |
|---|---|---|
| E1 heat | half ruler: Λ ≤ w²/2; δ²/(200 log γ) ≤ Λ from one zero | the function of the zeros that Λ is; no law in w alone is expected (a pair at depth δ inside real zeros of density log γ closes in time ≍ δ/log γ) |
| E1 mass normalisation, every block size | equivalent to width + cluster law (SRT) | boundedness of the zeros off the line in unit windows |
| E2 contraction | best factor 2^w, best slope loss 2w (M10, M12) | a factor below √2 from the gluing calculus; GCW additive loss law holds below the binding energy of the middle only |
| E3 | open | a source outside the Gauss class |
| E4 abelian rigidity | open | the factorisation of Gauss sums (Stickelberger) and the Kubota series of order ≥ 4; neither is in Mathlib or the corpus |
| E5 | over 𝔽_q both levers are theorems (IRW thick levels; AKT tensor growth); over ℤ base change needs well-founded outer modes (IRW), tensor powers the price law (FCT) | a lever from either over ℤ |
| E6 | frame (3, 6) exact (M11) | a zero-free half-plane for Grössencharacter L-functions of ℚ(ω) |
| E7 | three families (M3) | a world with Euler product and functional equation |
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
