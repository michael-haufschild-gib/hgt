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
| 7 | WeilsFormIsContinuousInTheLogarithmicEnergy | E1 (tool) | P |
| 8 | StepSamplesCarryWeilsFormOfALipschitzPacket | E1 (tool) | P |
| 9 | TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize | E1 (exactness) | P |
| – | stage maps and loss exponents | E2 | research |
| – | function-field levers and the acid test | E5 | research |
| – | rung lever; seeds for families | E6 | research |
| – | critical exponent of the complete Weil matrix | topics | research |

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

**M8 (step samples).** f continuous, |f| ≤ M, |f(u) − f(v)| ≤ L|u − v|, supported in (log R, log(R+J)],
R + J ≤ QR; σ_j = ∫ f · flat_j, g = Σ σ_j flat_j (the projection on the cells); c = 2L + M, Λ = log Q + 1.
(i) ∫ f g = Σσ_j² = ∫g²; ∫(f − g)² = ∫f² − Σσ_j² ≥ 0.
(ii) On the cell (log a, log(a+1)]: f(u) − σ_j e^{u/2} = ∫_cell [(f(u) − f(s))e^s + f(s)(e^s − e^{(u+s)/2})] ds,
so |f − g| ≤ c/a ≤ c/R.
(iii) ‖Δ_t(g − f)‖² ≤ min(4c²Λ/R², (2L²Λ + 12(R+J)Σσ²) t); D ≤ β and D ≤ βNt give
∫₀¹ D dt/t ≤ 2β log(1 + N); with N = 3(R+J)R²: E(g − f) ≤ 8c²Λ log(1 + 3(R+J)R²)/R².
(iv) M7 on packets (smooth both, mollification lowers E, masses converge), s = 1/R:
|𝔚_Q(g) − Z(f)| ≤ 160 L((log Q + 1)/2, w) c²Λ(16 log(1 + 3(R+J)R²) + 4)/R.
(v) Charges: ∫ g e^{u/2} = ∫ f e^{u/2}; |∫ (g − f) e^{−u/2}| ≤ (c/R) Λ e^{−(log R)/2}; |∫ f e^{u/2}| ≤ M Q Λ e^{(log R)/2}.
Neutral forms differ by at most (iv) + 2c²QΛ²/R.

**M9 (the margin is a ruler at polynomial block size).** θ < ½. Suppose for every K there is R ≥ K^{10} with
N_W(3K+1, R) + C K^θ of index ≤ 1. Then w ≤ θ.
Proof. Lag v, K ≍ e^v with the two states of the two ends (binding state e_v, antisymmetric state o_v)
inside the window, translated by log R. If 2 Re S(v) > 2 Re S(0) + (4E m₀ + 1)e^{θv}, both smooth neutral forms
lie below −D·mass − 1, D = |C| K^θ; N(s e + t o) = s² N(e) + t² N(o) and the masses are orthogonal. By M8 the
window matrix on the samples of the plane is at most the smooth form plus
2c₀²(s² + t²)·C₃K⁴(1 + log R)/R ≤ (s² + t²)/2 for K large (1 + log R ≤ 2√R, √R ≥ K⁵). Two negative squares:
contradiction. So 2 Re S(v) ≤ 2 Re S(0) + E' e^{θv} from some lag on, which is w ≤ θ (MAFT rate law).
Rulers: for A ≥ 10 and β ≥ 0, w ≤ β ⇔ ∀ε > 0 ∃C ∀K, R with K^{10} ≤ R ≤ K^A: index(N_W + C K^{β+ε}) ≤ 1; the
same with the floor of the block matrices in place of the index. One sequence of matrices (R = K^{10}) reads w.

## No-go closure
(to be filled per retired route)

## Log
- 2026-11-15 — created; README first draft written. Modules 1–6 compiled, axiom-clean, wired.
