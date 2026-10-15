# CHMD Stage 16: Growth–Positivity Collapse of the Causal Wave (one-sided bound ⟺ RH ⟺ two-point packets)

- **ID:** chmd-stage16-growth-positivity-collapse
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md §CHMD · card new-route-synthesis-conjecture-loop-2026-10-15.md (Stages 1–15)
- **Statement:** Let φ_Λ(y) = cosineShiftFn Λ sechHalf y be the CHMD causal wave. Unconditionally, for every exponent 0 ≤ a < ½: (∃M, φ_Λ(u) ≤ M e^{au} on u ≥ 0) ⟺ (∃M, φ_Λ(u) ≥ −M e^{au} on u ≥ 0) ⟺ (every nontrivial zero ρ has |Im √(γ_ρ²+2)| ≤ a) ⟺ (∃K, |φ_Λ(u)| ≤ K e^{a|u|} on ℝ). At a = 0: RH ⟺ φ_Λ bounded above ⟺ bounded below ⟺ φ_Λ(y) ≤ φ_Λ(0) for all y ⟺ all two-point difference packets nonnegative ⟺ the Laplace transform (KG pole series) is positive-real on Re s > 0.

## Goal
The CHMD frontier "Needs" reads: prove every finite Toeplitz form of φ_Λ nonnegative; a Bochner measure is not produced unconditionally. This stage removes the Bochner cone from the target: positivity of the whole Toeplitz hierarchy is forced by a *one-sided growth bound* on the single function φ_Λ, and conversely. The N×N hierarchy collapses to the N = 2 difference packets of Stage 13. Mechanism: the zero-side series of Stage 15 is a sum of cosines with complex frequencies ρ_ρ = √(γ_ρ²+2); an off-line zero gives a frequency with Im ≠ 0, i.e. an exponentially growing hyperbolic mode; Landau's theorem (corpus `exists_differentiable_extension_of_le_exp`) continues the Laplace transform of a one-sidedly bounded function past the first pole; a tilted-ray identity-theorem argument (corpus `FiniteOffLineLandau` pattern) shows the KG pole series blows up there.

Non-circularity: no RH input anywhere; the Laplace identity uses only Stage 15's unconditional series plus `zero_sum_inv_sq`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (the Lean proof is the paper proof)
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/RHTower/CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean` (number-free name; the other agent's Stage 16–21 took the numbers), namespace `RHTower.CHMDGrowthCollapse`; `lake build --old` green, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), wired into `RHTower.lean` after Stage 15; STATUS MUST-1529
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
- 2026-10-15 — Lean complete (≈1270 lines, 9 sections): KG spectral data, real cosine series, Laplace identity, pole-set analyticity, exact blow-up decomposition, generic tilted-ray lemma, pole exclusion, growth law, RH chain at `a = 0`, positive-real criterion. Module renamed number-free because the other agent's Stages 16–21 appeared meanwhile (their work: Schwarz-square/cosh–sinh strip kinematics of the packets, complementary, no overlap on these theorems). STATUS MUST-1529; ledger entry appended to the shared CHMD card.
- Surviving target (next loop): the one-sided bound `φ_Λ(u) ≤ φ_Λ(0)`, i.e. the KG prime wave `Σ Λ(n)/√n K_S(log n, u) ≥ P(u) + A(u) − φ_Λ(0)`; this is Wall 1 in KG coordinates — any attack must name the input that passes Wall 1.
- 2026-10-15 — **Loop step 2: the gate on spectral-realisation candidates.** Conjecture tested: "a self-adjoint realisation of the KG frequencies `√(γ_ρ²+2)` (a unitary flow with cyclic vector whose matrix coefficient is `φ_Λ`) exists in one of the known classes." Gate: spectral density `(1/2π) log R` (no Weyl law of integer dimension) and non-trace-class prime dependence. Kills: manifold Laplacians (Weyl `R^d`), Berry–Keating/quantum-graph prime-length models (CANNOT-546 decoupling), trace-class/finite-rank prime perturbations (CANNOT-549), adele-class/absorption models (positivity of the trace form is RH, Wall 12). Mechanism-level kills in KG coordinates: `Λ ≥ 0` with a positive KG kernel fails because `cos(u√(−∂²+c))` preserves positivity only at `c = 0`, where the pole exponent is ½; imaginary KG time `cosh(v√(−∂²+2))` is positivity-preserving but blind (weighted zero density only); twisted-arc annihilation is mean-periodicity with complex spectrum allowed (null face); KG energy is conserved for the spatial wave, the time-series "energy" `Σ w ρ²(cos²+sin²)` is trivially constant; positive-real/Herglotz is a receiver (lag MUST-268 classification). **No candidate passes Wall 1.**
- **Positive survivor (formalised, MUST-1530)** `formal/GaloisForLFunctions/RHTower/CHMDKleinGordonSeparationLawAndApproximateRealisation.lean` (namespace `RHTower.CHMDSeparationLaw`, wired after the growth module, standard axioms, `lake build --old` green): the separation law `Re ρ_ρ > √(7/4)` strictly for every zero, poles of the Laplace transform in `{√(7/4) < |Im s|, |Re s| < ½}`, pole series analytic on the closed strip `|Im s| ≤ √(7/4)`; the pole of ζ sits exactly on the separation line (`∫₀^∞ P(u)e^{−su}du = (2/cos²¼) s/(s²+7/4)`), so the archimedean-minus-prime transform is not analytic at `i√(7/4)` while the zero-side series is: the prime side carries the pole, on the boundary of the absolute-convergence strip (Wall 6 = the strip below the first possible pole, in KG coordinates). Approximate-realisation principle: `φ_Λ = p + e`, `p` maximal at `0`, `e` bounded above on `[0,∞)` ⟹ RH (a realisation may carry a bounded defect).
- Sharpened requirement for the next loop step: a unitary realisation of the KG prime wave with bounded defect, of Hodge-index type, whose spectral density is `(1/2π) log R` on `|R| ≥ √2` and whose prime dependence is not a trace-class modification of the archimedean reference. The other agent's Stage 22 (`CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion`) now imports the growth module and decomposes `chmdWave` into pole, archimedean and prime waves.
