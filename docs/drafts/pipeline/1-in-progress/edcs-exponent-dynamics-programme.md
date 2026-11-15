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
| 4 | TransformsSampledOnLogarithmicallyDensePoints | E1 (tool) | in progress |
| 5 | Lévy-normalised Weil floor of a configuration; the margin as a ruler | E1 | P |
| 6 | stage maps and loss exponents | E2 | research |
| 7 | function-field levers and the acid test | E5 | research |
| 8 | rung lever; seeds for families | E6 | research |
| 9 | critical exponent of the complete Weil matrix | topics | research |

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

**M4–M5 (E1, margin).** Correction of the first lemma of fable.md §5.2: the converse rate law in the mass
normalisation, uniform in the block size, is equivalent to a cluster law for off-line zeros (SRT
`polarGroundEnergyRate_eq_zetaZeroWidth_or_offLineCopies_cluster`); the width alone gives it with the factor
log(height). Statement to prove (configuration level): Z with |Re ρ − ½| ≤ σ and N(t, t+1) ≤ A₀ log(|t|+3); f
continuous, supported in [−a, a]; G(f) = ∫₀¹ ‖f(·+x) − f‖² dx/x. Then
Re W_Z(f, f) ≥ −C A₀ (1+a) e^{2σa} (G(f) + ‖f‖²). No ε-loss in the rate.
Proof. (i) Weighted sampling: weights m_q ≥ 0 with unit-window sums ≤ W give
Σ m_q|Φ(z_q)|² ≤ W (2a+2π) e^{2π} e^{2σa} ‖f‖² (SRT proof with weights; `sum_weight_mul_grid_le_of_depthWeighted`).
(ii) Φ_{f(·+x) − f}(z) = (e^{−izx} − 1) Φ_f(z); |e^{−izx} − 1|² ≥ 2e^{−σ}(1 − cos(x Re z)) for 0 ≤ x ≤ 1.
(iii) Apply (i) to f(·+x) − f with the weights m_q/ℓ_q, ℓ_q = log(|x_q|+5), divide by x and integrate over (0,1]:
2e^{−σ} Σ (m_q/ℓ_q) K(x_q)|Φ_f(z_q)|² ≤ A₀ C(a+1) G(f), K(ξ) = ∫₀¹(1 − cos ξx)dx/x.
(iv) K(2Y) ≥ K(Y) + ½ − 1/Y, so K(ξ) ≥ ¼ log(4+|ξ|) − 1 ≥ ℓ/4 − 5/4.
(v) Absorb the −5/4 term by (i) for f itself with the weights m_q/ℓ_q.
Step packets of mesh 1/R have G ≤ 4(1 + log R)·mass: the window matrices get the factor log(block size) [D].

## No-go closure
(to be filled per retired route)

## Log
- 2026-11-15 — created; README first draft written. Modules 1–3 compiled, axiom-clean, wired.
