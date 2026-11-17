# ECS missed connections of review 1611 (E-M1–E-M9)

- **ID:** ecs-missed-connections-1611
- **Stage:** 1-in-progress (conjecture loop on the formalized items)
- **Type:** THEOREM (paper → Lean), goal loop
- **Source:** docs/reports/review-1611/route-ecs.md §8
- **Statement:** formalize each corpus connection E-M1–E-M9 of the ECS route as unconditional Lean theorems about the critical state, with corollaries.

## Goal
Each E-M item names corpus results ECS does not import. The task is the theorem the connection gives, not a re-export. Order: easiest first.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (per item)
- [x] 2 → 3  formalized (per item)

## Items

| Item | Target theorem | Module (ECS/) | Status |
|---|---|---|---|
| E-M2 | RH ⇔ Pick matrices (D(p)+D(q))/(p+q) PSD on any bounded-uniqueness set of real probe nodes (intervals, integers ≥ 5) | Pick/RealProbeNodesDecideTheRiemannHypothesis.lean | formalized |
| E-M3 | half-line one-bound-state law: RH ⇔ arch − prime ≥ 0 on the charge hyperplane of H; off RH it is negative there and ≥ −(a − γ)W₈; second critical ratio W₁ ∈ (W₀, ∞), index ≤ 1 below it | Energy/TheChargeHyperplaneHasItsOwnCriticalRatio.lean | formalized |
| E-M4 | collar coercivity Q_R ≥ ‖G‖²/8000 + aW₈; collar form prime-blind; collar equation of the state = backward prime wave of its far part | Collar/TheCollarIsCoerciveAndPrimeBlind.lean | formalized |
| E-M5 | wall tail = Σ_k μ_{σ_k}(F)/(−σ_k − p); trivial moments determine every profile of H; the wall tail determines the profile (holomorphic off [5/2,∞), coefficients read on verticals); collar Hankel inertia on H | Wall/TheArchimedeanWallTailIsATrivialZeroSum.lean | formalized |
| E-M1 | bounded confined index ⇔ Weil-kernel finite index ⇔ finite layer ⇔ bounded heat counts ⇔ line above a height; bounded index ⇒ Lindelöf + quasi-RH (the Lindelöf wall of stage 2) | Index/TheBoundedIndexStratumIsLindelofDeep.lean | formalized; the exact index law of the confined form is the E-J loop's Index/TheConfinedFormCountsTheZerosRightOfTheLine.lean |
| E-M1 × E-M2 | probe index law: on a uniqueness set S ⊆ [1, ∞) for bounded holomorphic functions on Re w > 1 (integers ≥ 2), some real Pick matrix (D(p_i)+D(p_j))/(p_i+p_j) has n negative squares iff ζ has ≥ n zeros right of the line; integer form; RH ⇔ index 0; off RH index ≥ 2; odd index ⇒ one more; bounded ⇔ FiniteOffLine ⇒ Lindelöf | Pick/TheRealProbeKernelIsAKreinForm.lean, Pick/TheRealProbeKernelCountsTheZerosRightOfTheLine.lean | formalized |
| E-M7 | B13 ⇔ (finite layer ⇒ every critical state has F e^{−8u} subexponential a.e. on sets thick toward −∞) and the heated one-base form | Decay/StageTwoInThickLagForm.lean | formalized; the receivers are the E-Q loop's Decay/SubexponentialThickTailGivesTheAbscissaLaw.lean (my earlier level-sum module was redundant with it and is removed) |
| E-M9 | no finite mode set reproduces the state on any terminal ray (finite QNM sets incomplete) | Modes/NoFiniteModeSetReproducesTheState.lean | formalized |
| E-M6 | model table in ECS form | Index/FiniteLayerKreinStructureAndRigidity.lean (E-Q loop: over-regular Beurling finite layer, Beurling–Lévy rigidity) | covered by the E-Q loop |
| E-M8 | function-field calibration | Models/CurveCriticalStatesAndStepanovExclusion.lean (E-Q loop, E-Q3) | covered by the E-Q loop |

Peers: the E-J loop (card ecs-just-work-items-review-1611.md) owns E-J1–E-J9; E-M2 ⊂ E-J5(a), E-M1 ⊂ E-J1, E-M5 = E-J7. New modules only; one import line each in the ECS umbrella.

## Conjecture loop

| # | Conjecture | Module (ECS/) | Status |
|---|---|---|---|
| C1 | probe index law (E-M1 × E-M2) | Pick/TheRealProbeKernelCountsTheZerosRightOfTheLine.lean | formalized |
| C2 | W₀ in Pick form (E-J5(b)): for R > 0 the integer Pick matrices (D(m)+D(n))/(m+n) + a(R)/(m+n−8), m,n ≥ 7, are PSD iff R ≤ inf_A windowThreshold A; off RH W₀ is the largest such ratio | Pick/TheConfinedPickMatricesDecideTheCriticalRatio.lean | formalized |
| C2′ | finite node blocks approximate W₀ from above: R ≤ W₀ ⇒ every block PSD; R > W₀ ⇒ all large blocks fail | Pick/TheConfinedPickMatricesDecideTheCriticalRatio.lean | formalized |
| C3′ | confined probe index law: the confined Pick matrices have ≤ #right zeros negative squares at every ratio, monotone in R, and every n ≤ #right zeros is attained at a large ratio | Pick/TheConfinedPickMatricesCountTheZerosRightOfTheLine.lean | formalized |
| C3 | the critical ladder in Pick form (k-th critical ratio = first ratio with k negative squares of integer Pick matrices) | — | queued: needs window-test density of negative planes in H |
| C4 | E-M8 calibration: curve probes q^{-pm} (p ≥ 5) are dense in H_D (bounded power-series uniqueness); B_D + aW₈ ≥ 0 on H_D iff all curve Pick matrices PSD; curve RH iff bare curve Pick PSD; off curve RH the ground constant a* is the least PSD ratio; cubic Kummer data (Stepanov): PSD at every a ≥ 0; a* ≤ Σ_{|β|≠1} C_β C_{β⁻¹} (function-field form of C6) | Models/CurvePickMatricesDecideTheCurveCriticalState.lean | formalized |
| C5 | E-M6 Pick row: filled for curve models (C4). For Beurling/DH models no Weil form on half-line profiles exists (E-T2 absent), and without a functional equation the zero set is not reflection-invariant, so the probe kernel is not a Krein form: the Krein reading of C1/C2 needs the exact functional equation | — | blocked on E-T2 |
| C7 | Galerkin convergence of the finite-block minimizers to the critical state (E-J5(b), second half) | — | queued: needs Rellich compactness for probe sums (exists_strong_negative_limit_of_bounded_weilQuad is for C² compact tests) |
| C6 | W₀ bounded below by the off-line zeros: a(W₀) ≤ Σ_{off-line ρ} m_ρ/√((8+2x_ρ)(8−2x_ρ)), x_ρ = Re ρ − ½; hence √63·a(W₀) ≤ N_off (in [0, ∞]) | Pick/TheOffLineZerosBoundTheCriticalRatioFromBelow.lean | formalized |

## Paper proofs

### E-M2
Let S ⊆ (½, ∞) be a bounded-uniqueness set on Re w > ½ (an accumulation point in (½, ∞), or a Blaschke-divergent sequence → ∞, e.g. the integers ≥ 5). If the real Pick matrices of K(p,q) = B(e_p, e_q) = (D(p)+D(q))/(p+q) are PSD on S, then K is a PSD kernel on S (real symmetric), and Carathéodory–Pick gives G holomorphic on Re > 0 with Re G ≥ 0 and G = D on S. Cayley transforms c(G), c(D) = (·−1)/(·+1) are bounded by 1 on Re > ½ (Re D > 0 there unconditionally), and agree on S; so c(G) = c(D) and G = D on Re > ½. Then K = Carathéodory kernel of G on Re > ½, PSD, and RH follows from riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel. Converse: restriction.

### Probe index law (E-M1 × E-M2)
Let v_p(ρ) = √m_ρ/(p − (ρ − ½)) ∈ ℓ²(zeros) for p ≥ 1 and R the reflection ρ ↦ 1 − ρ̄. The zero-side
explicit formula gives K(p, q) = B(e_p, e_q) = ⟨R v_q, v_p⟩ (`bareMixedEnergy_probe_eq_inner`).
Upper bound: on the common kernel of the evaluations at the right zeros the form Σ_ρ conj(w(Rρ)) w(ρ)
is a sum of |w(ρ)|² over on-line zeros, so the index is ≤ #right zeros (`hermNegIndex_probeGram_le`).
Density: if a ⊥ v_p for p ∈ S, then F(w) = Σ √m_ρ a_ρ/(w − z̄_ρ) vanishes on S; the Peetre bound
|w − ζ|⁻² ≤ K(R, δ)/(1 + |ζ|²) at distance ≥ δ and Σ m_ρ/(1 + |ρ − ½|²) < ∞ make F holomorphic off the
discrete set {z̄_ρ} and F/(w + 1)² bounded on Re w > 1; so F = 0 there, on the connected complement of
the countable pole set, and |√m_ρ a_ρ| ≤ ε·B for every small ε (evaluate at z̄_ρ + ε), so a = 0
(`orthogonal_probeSpan_eq_bot`). Attainment: for n distinct right zeros the vectors e_ρ − e_{Rρ} have
Krein Gram −2I and norm ≤ 2; approximating each within 1/(5(n + 1)) by probe combinations gives a
congruent Gram C K Cᴴ within 5ε of −2I, negative definite, so index K ≥ n
(`card_le_hermNegIndex_probeGram_of_near`, `probeIndex_law`). Corollaries: n = 1 with
`rightZeros_zeta_eq_empty_iff`; parity from `even_ncard_rightZeros`; boundedness from
`rightZeros_zeta_finite_iff_finiteOffLine` and `confinedIndexBounded_tfae`; integer nodes from
`bareMixedEnergy_probe` and `isRightProbeUniquenessSet_natFrom` (Blaschke divergence at δ = 1).

### C2. W₀ in Pick form
(⇐) Let G be a window test (C², support in [−A, 0]) and g(x) = G(log x)x⁻⁶ (0 for x ≤ 0), C² on ℝ with
g(0) = 0. Weierstrass gives a polynomial π with |π − g'| < ε on [0, 1]; h(x) = ∫₀ˣ π, φ = g − h:
|φ|, |φ'| ≤ ε on [0, 1]. P(u) = e^{6u}h(eᵘ) = Σ_k c_k e^{(k+7)u} and G − P = e^{6u}φ(eᵘ) on u < 0. For
Re z ≥ −½, integrating (e^{(6+z)u}φ(eᵘ))' over (−∞, 0] gives (6+z)∫(G−P)e^{zu} = φ(1) −
∫e^{(6+z)u}φ'(eᵘ)eᵘ, so |∫(G−P)e^{zu}| ≤ 2ε/|6+z| (`norm_integral_error_le`). With y_F(ρ) =
√m_ρ∫F e^{(ρ−½)u}: ‖y_G − y_P‖² ≤ 20ε²Σ m_ρ/(1+|ρ−½|²). Weil's form is Re⟨Ry_G, y_G⟩ (W_eq_inner +
explicit formula), the bare form of P is Re⟨Ry_P, y_P⟩ (`bareMixedEnergy_probe_eq_inner_W`), and
∫_{u<0}P²e^{−8u} ≤ ∫G²e^{−8u} + 2ε∫|G|e^{−2u} + ε². Hence Pick(c) ≤ Q_R(G) + Kε; Pick ≥ 0 for all ε
gives Q_R(G) ≥ 0, and Q_R(H) ≥ 0 with weilQuad H < 0 is testCriticalMultiple H ≥ R
(a(R) = 7J(1)/(a_φ R)). (⇒) The mixed energy is bilinear on the domain (Gamma, prime, pole and
confinement parts), so Q_R(Σc_k e_{k+7}) is the Pick form; below every threshold Q_R ≥ 0 on the domain.

## Log
- 2026-11-16 — created; E-M2, E-M3, E-M4 formalized.
- 2026-11-17 — E-M5, E-M9, E-M7 (stage-2 form) formalized; E-M6/E-M8 found covered by the E-Q loop; E-M1 Lindelöf wall compiling. Next: probe index law (E-M1 × E-M2, Krein–Langer on real probe nodes).
- 2026-11-17 — E-M1 Lindelöf wall and the probe index law formalized; all items formalized or covered.
- 2026-11-17 — conjecture loop: C2, C2′, C3′, C4, C6 formalized; C3, C7 queued; C5 (Beurling Weil form, E-T2) next.
