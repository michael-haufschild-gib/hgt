# Odd-sector Weil uniqueness: does odd positivity force lam = Λ?

- **ID:** odd-sector-uniqueness
- **Stage:** 1-in-progress (Lean: MUST-1498, 1499, 1501, 1502, 1503)
- **Type:** CONJECTURE
- **Source:** rh-goal-loop-opus-2026-09-29.md row 1226; sibling of 3-formalized/even-sector-weil-uniqueness.md (MUST-1495)
- **Statement:** If real weights lam make the Weil functional (pole weight 1) nonnegative on every autocorrelation of an ODD compactly supported C² test, then lam = Λ on n ≥ 2 and RH holds. Equivalently RH ⟺ PBAP_odd.

## Goal
Complete the parity picture: even positivity alone already forces the cone point (MUST-1495). For Λ itself, odd positivity is RH (`WeilMarkovOddPositivity`). Uniqueness for arbitrary weights from odd tests is open.

## What transfers from the even proof
- The ρ-variable Bochner step transfers. Put O(Ψ) = L(z²ΨΨ^#) for even Ψ. Then y ↦ O(cos(yρ)Ψ·) is positive definite, because z²(AA^# + BB^#) is the spectral square of the odd functions zA and zB. So O(Ψ) = ∫T̃_Ψ dμ_S with μ_S ≥ 0 on the real ρ-line.
- The lifted weight T̃_Ψ is ≥ 0 on the whole cross for even Ψ. So, unlike the even case, μ_S has no sign problem at all on the segment ρ² ≤ 2.
- The obstruction is different. The even functional is not determined: L(K) = ∫(K̃ − K(0)Ẽ)/(ρ²−2) dμ_S + K(0)·L(E) has one free parameter (the r = 0 atom). The weight 1/(ρ²−2) is negative on the exceptional segment.
- The twisted-arc null identity Σ_j w_j L(K_j) = 0 gives one linear relation and no confinement.

## Reduction (paper, row 1226)
- Suppose two twisted-arc families with multipliers M, M′ (arc measures μ, μ′ annihilating every twisted moment) satisfy, for t = M(0)/M′(0),
  M(z) − tM′(z) = z²Q(z) with Q ≥ 0 on ℝ ∪ i[−√2, √2].
- Then N = Σw_jK_j − tΣw′_jK′_j is null for every lam and vanishes doubly at 0.
- With any Lévy weight ψ_g = ĝ(0) − ĝ (g ≥ 0 even), odd positivity gives L(K·ψ_g) ≥ 0 (Φ-averaging of odd shifts), hence a positive measure μ_g. Then 0 = L(N) = ∫ (z²Q/ψ_g)~ dμ_g, and z²/ψ_g > 0 on the cross minus 0.
- So μ_g is carried by the critical zeros (and the zeros of Q). The critical-zero rigidity (corpus `eq_zero_of_signedMeasure_criticalZeros`-type) then has to be adapted to give lam = Λ.

## Open cores
- [OPEN CORE 1] Is the set of twisted-arc annihilating probability measures larger than one point? Does it contain a pair ordered so that Q ≥ 0 on the cross? Monotonicity in u of the kernel [₂F₁(¼−iz/2, ¼+iz/2; ½; u²) − ₂F₁(¼,¼;½;u²)]/z² would suffice for an ordered pair.
- [OPEN CORE 2] Growth bound |lam_n| ≤ C√n log n from odd positivity (odd two-bump tests b(·−a) − b(·+a) give both signs at a node through four-bump combinations).
- [OPEN CORE 3] Critical-zero rigidity for a measure carried by Z without full-cone positivity.

## Closing step, sharpened (row 1227)
- For odd-positive lam, odd Ξ-divisible decay-class tests F̂ = zΞE give Q_v(F) ≤ 0. ρ-Bochner on the real-r functional then gives D_v ≤ 0 on ℝ ∖ (Z ∪ {0}).
- Riemann-kernel perturbation F = Φ′χ_L + εH, with H odd and the corpus zero-side estimates: if W_lam(Φ′) = 0, the linear term forces Q_v(Φ′, H) = 0 for all odd H, hence v = 0 by Hamburger-type injectivity.
- So the whole open content is W_lam(Φ′) = 0, i.e. the odd spectral measure is carried by Z ∪ {0}. This needs an ODD blind Ξ-divisible family with positive weights, or the ordered pair above.

## Approach
First settle OPEN CORE 1 from the corpus TMP construction (`TwistedArcMinimumPrincipleProof`, `TwistedArcFamilyN1Reduction` single-twisted family `swArcMoment`). The single-twisted and double-twisted mechanisms may give two different multipliers.

## Log
- 2026-10-15 — created (row 1226) from the even-sector closure analysis.
- 2026-10-15 (row 1228) — OPEN CORE 1 is likely NEGATIVE.
  - The PBAP atlas records [P] that the null face is one ray, G₀ = (E′ geodesic profile) ⋆ (arc kernel). If so, no second null multiplier exists, and the ordered-pair route fails.
  - Remaining routes to odd uniqueness:
    - (i) A one-sided almost-periodic rigidity. If D_v = Σ_{n≥2} v_n cos(r log n) is ≤ 0 off Z ∪ {0}, has atoms ≤ 2πm_γ on Z and a free atom at r = 0, and its FT is discrete on ±log n, then v = 0. The two-sided carried version is corpus `eq_zero_of_signedMeasure_criticalZeros`. The one-sided version needs W_lam(Φ′) = 0, so it is circular through the Riemann-kernel perturbation.
    - (ii) A falsification instead. Construct, under RH, an odd-positive lam ≠ Λ exploiting the r = 0 atom, which odd tests cannot see. Finitely many exceptional atoms are impossible, because their FT is smooth and nonzero. Multiples (1±t)Λ fail, because the archimedean symbol γ changes sign at |r| ≈ 6.3.
  - Status: OPEN; no formal work started. The odd growth bound (OPEN CORE 2) mirrors MUST-1489, using the odd tests b_odd(x−a) + b_odd(x+a) (node +‖b‖²) and b_even(x−a) − b_even(x+a) (node −‖b‖²).
- 2026-10-15 (row 1229) — MAIN LEAD: the a = ¼ twisted arc witness.
  - Corpus `TwistedArcFamilyN1Reduction`: the a-twisted generator g_u − a·s_u has log-profile multiplier (¼+τ²)(¼+τ²−a), and moment-TAMP_a gives a blind witness for a ∈ [0,¼).
  - At a = ¼ the multiplier is (¼+τ²)τ² ≥ 0, with a double zero at τ = 0.
  - A blind Ξ-divisible PD null kernel G₁ with Ĝ₁(0) = 0 and Ĝ₁ > 0 on ℝ∖(Z∪{0}) gives ∫_{off}(−D_v)Ĝ₁ = 0 (the r = 0 atom is invisible), hence D_v = 0 off Z∪{0}. G₀ then gives c₀Ĝ₀(0) = 0, so c₀ = 0, D_v is carried by Z, and rigidity follows.
  - Still to check: (1) moment-TAMP at a = ¼. a = 0 is the clamped beam 𝔐² (`ClampedBeamPositivity`); a = ¼ adds a second-order tension term, and positivity of clamped beams under tension is the question. (2) Segment bookkeeping: Ĝ₁(iy) changes sign at y = ½, so the even-proof MUST-1488 step must be redone for the r²-weighted odd measure.
- 2026-10-15 (row 1230) — Segment bookkeeping refines the lead.
  - In the odd sector, ν^odd ≥ 0 forces three signs: D_v^{real} ≤ 0 off Z∪{0}; D_v^{seg} ≥ 0 on the imaginary segment |y| ≤ √2 (weight r² = −y²); and the r = 0 atom c₀ is free.
  - A null kernel G closes the argument iff Ĝ ≥ 0 on ℝ, Ĝ ≤ 0 on the segment, Ĝ(0) = 0, and Ĝ ≠ 0 off Z. That is an odd-type spectrum τ²·P(τ²) with P > 0 on the reachable cross.
  - The a = ¼ multiplier (¼+τ²)τ² fails, because (¼+τ²) changes sign at y = ½. The needed shape is τ²·(cross-positive).
  - (𝔐 − ¼) applied to the untwisted arc kernel 𝒦_u has multiplier τ².
  - NEW TARGET: a minimum principle for the moments of √(y/2)(¼ − ∂²)𝒦_u − ¼·√(y/2)𝒦_u, i.e. the single twist minus a quarter of the untwisted kernel. This is second order (a string under tension) rather than fourth (a beam). The 1/|x| tail of the untwisted kernel (pole/mass) must be handled.
  - Odd uniqueness ⟸ this minimum principle + translation to a Weil null kernel + the D_v pairing argument + critical-zero rigidity.
- 2026-10-15 (row 1231) — Sharpened obstruction for the odd null kernel.
  - Why the plain τ² kernel fails: the untwisted kernel T_0 = (cosh v − c)^{−1/2} has the e^{−|v|/2} (1/|x|) tail, i.e. a pole of its multiplier at τ = ±i/2, and −∂² does not remove it.
  - Why the pole factor must be squared: a regular kernel needs the factor (¼+τ²) to cancel those poles, and a single factor changes sign on the segment at y = ½. The only sign-definite choice is (¼+τ²)².
  - Required spectrum: τ²(¼+τ²)²·Σ(τ). This is the image of the twisted generator under −∂², i.e. a SIXTH-order arc operator (𝔐−¼)𝔐².
  - Its minimum principle (the blind annihilating measure) is OPEN. The 4th-order clamped-beam argument (`ClampedBeamPositivity`) does not obviously extend.
  - Why differentiating G₀ fails: −G₀″ has the right spectrum r²Ĝ₀ (≥ 0 on ℝ, ≤ 0 on the segment by MUST-1488, double zero at 0), but differentiation destroys blindness.
  - Status: OPEN; the closing step is a new minimum principle in the arc lane.
- 2026-10-15 (row 1232) — Core reduction.
  - Odd positivity plus even mean-zero positivity is exactly "W_lam + κ positive definite for some κ ≥ 0" (Weil positivity modulo constants). The segment cancels between the two sectors.
  - Q* (under RH): does any nonzero v have D̂_v ≤ Z + κδ₀? A solution needs D̂_v({0}) > 0, which is a squares-type Dirichlet pole at u = ½.
  - In the regular class (D̂_v minus its atom is a function), Bohr mean zero kills v, so odd rigidity holds there as in `WeilPositivityHalfPoleRigidity`.
  - Budget closure: every log r or pole budget that obeys one-sided bounds is ±εΛ, and both signs fail.
  - Soft tools (Carathéodory moments, recurrence, local averages) cannot decide Q*; arithmetic input is needed.
  - Status: OPEN, sharpened to Q*.
- 2026-10-15 (row 1233) — Dual form.
  - Under RH, Q* ⟺ approximate odd certificates exist: blind PSD K_j on mean-zero tests (K̂_j(0) = 0) with A(K_j)/P(K_j) → 0 at every spectral location.
  - An exact certificate would be a second null ray. That is not expected (index law, card modular-null-face-single-ray). Limits off the face (atlas "null edge at infinity", chirp tests) are the open source.
  - Crux: the low band |r| < 14, where blind spectra cannot concentrate (Carlson edge).
- 2026-10-15 (row 1235) — [L] MUST-1498 `RHTower/WeilOddConeMinorantRigidity`.
  - Odd Weil positivity admits no minorant of Λ other than Λ, and RH ⟺ ∃ odd Weil-positive lam ≤ Λ. The same holds modulo constants.
  - Mechanism: the c/2-translate of the log-shift test is odd.
  - Remaining odd uniqueness is the majorant / positive log-mean side, i.e. Q* restricted to D̂_v({0}) > 0.
- 2026-10-15 (row 1236) — [L] MUST-1499 `RHTower/WeilOddConeHalfPoleRigidity`.
  - Odd Weil positivity forces w = 0 in the symbol-plus-atom class: the half-pole class, including squares.
  - Q* is now confined to perturbations whose symbol is singular off the origin, i.e. carries mass on the critical zeros.
  - Next: the zero-carried class. A D̂_v that charges Z must come with the archimedean density, the budget-closure heuristic of row 1232.
- 2026-10-15 (rows 1237–1242) — State of Q*.
  - Parity–sign table complete [L]: MUST-1501/1502/1503.
  - Tail-sign law: near-radical tests cannot certify excess in moment-constrained sectors.
  - Poisson principle excludes multipliers Λ⋆c.
  - Summable-atom class closed [P].
  - Hermite–Biehler form: does (s−½)^κ admit a Dirichlet companion Q ≠ 1?
  - The open core is now symbols carrying a positive-density share of Z.
- 2026-10-15 (loop rows 1243–1244):
  - [L] MUST-1504 `RHTower/WeilParityPoleWeightWindows`: the odd pole-weight window of Λ is (−∞, 1] under RH and empty otherwise. The even window is [1, ∞) under RH and empty otherwise. The windows meet only at 1. β > 1 fails on odd tests unconditionally, via the odd log-shift translate with pole term −A_L².
  - [P, conjecture] The pole-free odd blind tier is probably RH-free. Tempered weights with prime density c ≈ 2.05 put the anomaly atom at r = 0, which odd tests cannot see. The ζ-free certificate inequality `2c Re P₁(1+ir) ≤ Ω(r)` is tight near r ≈ 6 and not certified. Odd RH content = Λ's exponential density, i.e. the pole room 2S².
  - Pole-density law: odd positivity at β > 0 forces a one-sided O(1) smoothed Chebyshev bound on lam.
- 2026-10-15 (rows 1245–1247):
  - [P] Q* reduces to the flat-density case. Pairing with G₀ forces the odd Weil measure onto Z unless lam − Λ has spectral mass at r = 0, and the corpus `eq_zero_of_signedMeasure_criticalZeros` finishes. Schur products of G₀ cannot give mean-zero near-null tests (row 1246).
  - [L] MUST-1505 `RHTower/WeilOddBlindPoleWeightWindow`: odd Farkas at every β. Blind odd positivity above 1 ⟹ a second odd-positive system exceeding Λ. Odd thinness ⟹ the blind odd window is ⊆ (−∞, 1].
- 2026-10-15 (route-tt row 538) — OPEN CORE 2 closed in Lean: `RHTower/OddSectorWeightGrowth`, `RHTower.OddSector.exists_abs_le_of_weilPositiveOddAt` (WeilPositiveOddAt 1 lam ⟹ |lam n| ≤ C√n(1 + log n), n ≥ 2), via the corpus odd node tests `oddPlus`/`oddMinus` and the even-sector node bounds. Standard axioms, `lake --old` clean, wired.
- 2026-10-15 (route-tt row 540) — Odd rigidity injectivity (OPEN CORE 3 / closing-step injectivity) in Lean, including the invisible r = 0 atom:
  - `RHTower.eq_zero_of_forall_even_meanZero_atomPairing_riemannKernel_eq_zero` (`RHTower/OddSectorRiemannKernelRigidity`): T_w(Φ ⋆ g) = 0 for all even C² compact mean-zero g ⟹ w(n) = 0 for n ≥ 2. Since Φ′ ⋆ H = −Φ ⋆ H′ and {H′ : H odd} = even mean-zero tests, this is exactly "T_v(Φ′ ⋆ H) = 0 ∀ odd H ⟹ v = 0".
  - Built on `RHTower.eq_zero_of_riemannKernelTransform_eq_const_of_sq` (G_w ≡ C ⟹ C = 0, w = 0) and `GaloisForLFunctions.HTGeometry.quarter_eq_zero_of_coeffTheta_relation_of_sq` (Hamburger with an x^{−1/4} correction: the correction vanishes).
  - Remaining OWU content: W_lam(Φ′) = 0 (OPEN CORE 1, odd blind null kernel).
- 2026-10-15 (loop row 1264) — [L] MUST-1513: odd positivity at any β transfers to nonnegative resonators with an ODD profile `g′`. The spectral square is `z²ĝĝ^#DD̃`, so there is no 1/z² obstruction. This gives the odd log-density ceiling of Λ at every β (`odd_log_density_le`), closing row 1248's open item. Next: the unconditional odd window ⊆ (−∞, 1]. It needs the odd far-bump lower density `≥ β` and the ceiling, compared through dyadic L² control of `lam⁺`. This would discharge the "odd thinness" premise in MUST-1505.
- 2026-10-15 (loop row 1265) — [L] MUST-1515: unconditional odd window. `RHTower.OddSector.le_one_of_weilPositiveOddAt`: WeilPositiveOddAt β lam ⟹ β ≤ 1, for every real lam. Corollaries `le_one_of_primeBlindPositiveOddAt` and `riemannHypothesis_imp_primeBlindPositiveOddAt_iff` (under RH the blind odd window is exactly (−∞, 1]). This discharges the thinness premise of MUST-1505. Ingredients: absolute convergence on Re s > 1 from odd positivity alone (`summable_abs_div_rpow_of_weilPositiveOddAt`; dyadic lam⁺ via star resonators, lam⁻ via far-bump window covers), a Laplace/Fubini bridge from far-bump window sums to σF(σ), and the odd log-density ceiling with Abel's bound. Modules `RHTower/OddSectorWeightAbsoluteConvergence`, `RHTower/OddSectorPoleWeightAtMostOne`.
- 2026-10-15 (loop row 1268) — [L] MUST-1519: Q* is bypassed jointly. Odd positivity at any β₀ ≥ 0, together with even positivity on pole-free tests, forces RH ∧ lam = Λ (`riemannHypothesis_of_weilPositiveOddAt_of_weilPositiveEvenPolar`). At β₀ = 0 this is the uniqueness of the primitive-hyperplane certificate (`riemannHypothesis_iff_exists_weilPositiveOddAt_zero_weilPositiveEvenPolar`). The r = 0 atom (Q* fakes) is visible to even pole-free tests. Q* alone (odd positivity without even input) stays open.
- 2026-10-15 (loop row 1269) — [L] MUST-1520: RH ⟺ `PrimeBlindPositiveHyperplane`, i.e. pole-free blind positivity on mixed combinations of odd tests and even pole-free tests (`riemannHypothesis_iff_primeBlindPositiveHyperplane`).
