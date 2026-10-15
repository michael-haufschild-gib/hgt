# CHMD Stage 16: Growth–Positivity Collapse of the Causal Wave (one-sided bound ⟺ RH ⟺ two-point packets)

- **ID:** chmd-stage16-growth-positivity-collapse
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, in progress)
- **Source:** docs/reports/rh-current-frontier-map.md §CHMD · card new-route-synthesis-conjecture-loop-2026-10-15.md (Stages 1–15)
- **Statement:** Let φ_Λ(y) = cosineShiftFn Λ sechHalf y be the CHMD causal wave. Unconditionally, for every exponent 0 ≤ a < ½: (∃M, φ_Λ(u) ≤ M e^{au} on u ≥ 0) ⟺ (∃M, φ_Λ(u) ≥ −M e^{au} on u ≥ 0) ⟺ (every nontrivial zero ρ has |Im √(γ_ρ²+2)| ≤ a) ⟺ (∃K, |φ_Λ(u)| ≤ K e^{a|u|} on ℝ). At a = 0: RH ⟺ φ_Λ bounded above ⟺ bounded below ⟺ φ_Λ(y) ≤ φ_Λ(0) for all y ⟺ all two-point difference packets nonnegative ⟺ the Laplace transform (KG pole series) is positive-real on Re s > 0.

## Goal
The CHMD frontier "Needs" reads: prove every finite Toeplitz form of φ_Λ nonnegative; a Bochner measure is not produced unconditionally. This stage removes the Bochner cone from the target: positivity of the whole Toeplitz hierarchy is forced by a *one-sided growth bound* on the single function φ_Λ, and conversely. The N×N hierarchy collapses to the N = 2 difference packets of Stage 13. Mechanism: the zero-side series of Stage 15 is a sum of cosines with complex frequencies ρ_ρ = √(γ_ρ²+2); an off-line zero gives a frequency with Im ≠ 0, i.e. an exponentially growing hyperbolic mode; Landau's theorem (corpus `exists_differentiable_extension_of_le_exp`) continues the Laplace transform of a one-sidedly bounded function past the first pole; a tilted-ray identity-theorem argument (corpus `FiniteOffLineLandau` pattern) shows the KG pole series blows up there.

Non-circularity: no RH input anywhere; the Laplace identity uses only Stage 15's unconditional series plus `zero_sum_inv_sq`.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (paper proof is the Lean proof)
- [ ] 2 → 3  formalized: `formal/GaloisForLFunctions/RHTower/CHMDStage16GrowthPositivityCollapseAndTwoPointCriterion.lean`
- [ ] 3 → 4  n/a (route RH only)

## Approach
1. KG spectral data at zeros: `kgFreq ρ = rhoC (gammaOf ρ)`, `kgWeight ρ = specSq sechHalf (gammaOf ρ)`; Re kgFreq > 1, |Im kgFreq| < ½, reflect symmetry kgFreq(1−ρ̄) = conj kgFreq ρ, equal frequency ⟹ equal weight, norm-summability.
2. Real complex series: (φ_Λ u : ℂ) = Σ' m_ρ cos(u kgFreq ρ) kgWeight ρ (reflect involution kills the imaginary part).
3. Laplace identity on Re s > ½: ∫₀^∞ φ_Λ e^{−su} = Σ' m (w/2)(1/(s−iρ) + 1/(s+iρ)) =: kgPoleSeries s.
4. kgPoleSeries analytic off the locally finite pole set {±i kgFreq ρ}; exact decomposition near a pole: G(p₀+d) = A/d + B(d), ‖A‖ ≥ ‖w₀‖/2, ‖B‖ ≤ C.
5. Generic tilted-ray lemma: holomorphic extension past a blow-up point is impossible.
6. Landau (corpus) + 4 + 5 ⟹ one-sided bound at exponent a ⟹ all |Im kgFreq| ≤ a.
7. Corollaries: exact growth law; RH chain at a = 0 (bounded above/below, φ ≤ φ(0), |φ| ≤ φ(0), two-point packets); positive-real criterion.

## What this changes in the route
- "Produce a Bochner measure" is replaced by "bound the KG prime wave on one side". In prime-side terms (Stage 13 formula) this is a one-sided bound on Σ Λ(n)/√n K_S(log n, y) by the explicit pole + archimedean terms: Wall 1 (one-sided √x prime counting) in KG coordinates. The Toeplitz cone carries no extra content beyond that single one-sided inequality.
- All positivity receivers of Stages 4–14 are now receivers of a growth statement.

## Log
- 2026-10-15 — created; another agent owns Stages 1–15 (Stage 15 built 19:59, not yet in umbrella). This stage goes in a new module; umbrella wiring after Stage 15's line.
