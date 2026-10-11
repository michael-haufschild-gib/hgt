# HCF single-line exact receiver and the Gaussian–von Mangoldt chirp

- **ID:** HCF-LINE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** route HCF (frontier map, "cofinal ceiling"); working ledger `1-in-progress/hcf-exact-layer-loop-2026-10-09.md` rows 14–20
- **Statement:** For every `a > 0`, RH ⇔ `b ↦ ν(a+ib) = Σ_q exp(-(a+ib) z_q²)` is bounded ⇔ `log |Σ_n Λ(n) n^{-1/2} exp(-(log n)²/(4(a+ib)))| = o(|b|)`.

## Goal
Replace the HCF height family (amplified diagonal bounded at every height `t`) by one height with
complex amplification.  This leaves one explicit prime sum in one real variable, with no zeros,
heights, or Gamma factor in the statement.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proofs = Lean proofs below)
- [x] 2 → 3  formalized: all theorems below, `lake build --old` green, axioms = propext, Classical.choice, Quot.sound
- [ ] 3 → 4  publication-ready (not pursued: user directive "no stage 4, only the RH proof")

## Lean theorems (namespace `RHTower`)
- `riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line` — RH ⇔ ν bounded on `Re τ = a`.  This closes the converse that `XiGaussianHeatVerticalBound` records as blocked by possible cancellation.
- `riemannHypothesis_iff_forall_norm_xiGaussianHeatTraceC_le_real` — RH ⇔ `‖ν(a+ib)‖ ≤ ν(a)` for all `b` (contraction form; 2×2 Toeplitz = chirp Weil cone).
- `xiGaussianHeatTraceC_eq_bottomSource`, `riemannHypothesis_iff_xiGaussianBottomSourceC_bounded_on_vertical_line` — ν = −(i/π) J, where J is the Gaussian transform of `logDeriv XiC` on `Re s = 3/2`.
- `pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime` — πν(τ) = Arch(τ) + 2πe^{τ/4} − (π/τ)^{1/2} S(τ) on `Re τ > 0` (identity-theorem continuation of the real-time formula).
- `riemannHypothesis_iff_gaussianPrimeChirpSum_le_sqrt_norm` — RH ⇔ S(a+ib) = O(|τ|^{1/2}).
- `xiGaussianHeatTraceC_exponentialType_iff(_xi_zeros)`, `gaussianPrimeChirpSum_exponentialType_iff` — exponential type κ ⇔ all zeros satisfy 2|γ||β−½| ≤ κ (hyperbolic ladder).
- `riemannHypothesis_iff_gaussianPrimeChirpSum_subexponential` — RH ⇔ S(a+ib) = O(|τ|^{1/2} e^{ε|b|}) for every ε > 0.
- `abs_re_sub_half_le_of_xiGaussianHeatTraceC_exponentialType` — finite type κ ⇒ |β − ½| ≤ κ/18.
- `norm_xiGaussianHeatTraceC_le_zeroFree`, `norm_gaussianPrimeChirpSum_le_zeroFree` — unconditional: saving exp(−b²/(116 a log(2|b|/a))) below the trivial exp(b²/(4a)).
- `tendsto_xiGaussianHeatVerticalVariance_of_rh`, `mult_one_iff_tendsto_xiGaussianHeatVerticalVariance_of_rh` — HCF variance law: under RH the vertical Bohr mean square of ν tends to the λ-coincidence sum, and it equals 2Σ_q e^{−2aλ_q} iff all zeros are simple.
- `riemannHypothesis_iff_criticalFeatureComplexAmplifiedTrace_bounded_on_vertical_line` — the same for HCF's own diagonal Σ F_0(z)² e^{−τz²}; generic Phragmén–Lindelöf step `norm_le_max_of_vertical_of_sector_of_growth`.

Modules: `RHTower/XiGaussianHeatVerticalLineReceiver`, `XiGaussianHeatBottomSourceReceiver`,
`XiGaussianHeatPrimeChirpReceiver`, `XiGaussianHeatVerticalExponentialType`,
`XiGaussianHeatVerticalZeroFreeGrowth`, `HedenmalmCriticalFeatureComplexAmplificationReceiver`,
`XiGaussianHeatVerticalVarianceLaw`.

## Approach
- ν is holomorphic on `Re τ > 0` with growth exp(b²/σ)/σ.  It is bounded on the sector |Im τ| ≤ Re τ because ‖z_q‖² > 150.
- Phragmén–Lindelöf on the strip π/4 < Im s < π/2 via τ = a + e^s (growth exponent 2 < 4) joins the 45° ray to the vertical line.
- Along a ray a + re^{iφ} with φ ↑ π/2, only finitely many exponents e^{iφ}w_q have negative real part.  An off-line copy with Im w > 0 is among them.  The light-cone lemma (`HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg`) then gives unboundedness.
- The ladder uses the multiplier exp(iκe^s), whose modulus is at most 1 on the strip.

## Insight
- A single off-line zero gives only LINEAR growth exp(2|γδ||b|).  Quadratic growth b²δ²/a requires infinitely many off-line zeros.  So exponential type, not growth order, is the exact invariant: type = sup 2|γ||β−½|.
- The HCF producer is RH-strength.  It has the cleanest form: the chirp sum has exponential type zero on one vertical line.  The unconditional state is log|S| ≤ (¼ − c/log b) b²/a.

## Extensions (cycles 24–31)
- `xiGaussianHeatTraceC_sector_bounded_iff_xi_zeros`: sector of slope T ⇔ conical zero-free region 2T|γ||β−½| ≤ γ² − (β−½)²; T = 6 unconditional; RH ⇔ every T.
- `exists_norm_xiGaussianHeatTraceC_le_vinogradovKorobov`: VK saving for the unconditional producer.
- `not_tendsto_zero_xiGaussianHeatTraceC`, `exists_frequently_le_norm_gaussianPrimeChirpSum_sub_main`: unconditional Ω(√|b|).
- `frequently_le_norm_xiGaussianHeatTraceC`, `frequently_le_norm_gaussianPrimeChirpSum_sub_main`: sharp Ω-constant √π ν(a) (= RH O-constant) (uses corpus `HTGeometry.exists_simultaneous_dirichlet`).
- `gaussianPrimeChirpSum_growth_gap`: O(√|b|) or ≥ exponential, nothing in between.
- `exists_norm_xiGaussianHeatTraceC_le_quadratic_coefficient`: quadratic coefficient ≤ Δ∞²/a (lower half open; needs Turán-type non-cancellation).
- `asymptoticQuasiRH_iff_amplifiedTrace_rates_uniformly_below_quarter`: asymptotic quasi-RH ⇔ HCF rates at large heights uniformly < ¼ (exact, height axis).
- `eventually_volume_amplifiedTrace_exceeds_exp_le_powerSaving`: deep HCF amplification (rate > κ) occupies measure ≤ U^{1−√κ/40}.

Hierarchy: RH ⇔ sublinear growth on the vertical line ⇔ every height rate is 0. The hyperbolic deviation D = sup 2|γ||β−½| is the vertical exponential type. Asymptotic deviation Δ∞ ⇔ uniform height rates (vertical quadratic coefficient ≤ Δ∞²/a). Unconditional: each height rate < ¼; rates > κ are polynomially rare; the vertical growth has the VK saving.

## Log
- 2026-10-10 — created directly in 3-formalized (cycles 14–20 of the HCF exact-layer loop)
- 2026-10-10 — extensions cycles 24–31 added

## Extensions (cycles 35–37)
- **Vertical Bohr spectrum** (`XiGaussianHeatVerticalSpectralLaw`): under RH, the Bohr coefficient of the prime chirp (π/τ)^{½}S(τ) on Re τ = a at frequency λ ≥ 0 is −π Σ_{γ_q²=λ} e^{−aλ}; the archimedean part has empty vertical spectrum unconditionally.
- **Separation-free power sums** (`HTGeometry/PowerSumTuranLowerBound`): some |z_i| ≥ 1 ⇒ ∃ν ∈ [M+1, M+N], |Σ z_i^ν| ≥ 1/(2eN(6(N+1)(M+2N+2))^N).
- **Exact vertical quadratic law** (`XiGaussianHeatVerticalQuadraticLowerLaw`): inf{c : ν(a+ib) = O(e^{cb²})} = Δ∞²/a; asymptotic quasi-RH ⇔ vertical rate < 1/(4a).
- **Mean-value producer** (`XiGaussianHeatVerticalMeanCriterion`, cycle 38): RH ⇔ the vertical Cesàro mean of ν (equivalently of the prime chirp) on one line tends to 0; a polynomially bounded primitive Σ e^{−τw}/w on one line already forces RH.
- **Zero-free half-plane** (`XiGaussianHeatZeroFreeHalfPlane`, cycle 42): RH ⇔ ν(τ) has no zeros in some right half-plane ⇔ the prime chirp equation (π/τ)^{1/2}S(τ) = Arch(τ) + 2πe^{τ/4} has no solution far right. Under ¬RH the zeros of ν reach every right half-plane (Hurwitz limit of normalized translates).
- **Gram index** (`XiGaussianHeatVerticalGramIndex`, cycle 43): the vertical heat Gram form Q_a on ℂ[ℝ] has negative index = number of off-line zero quadruples (finite case), independent of a; RH ⇔ Q_a ⪰ 0.
- **Hermite index law** (`XiGaussianHeatHankelIndex`, `XiGaussianHeatGramIndexInfinite`, cycle 44): the heat Hankel form of the moments m_n(a) = Σ_q w_q^n e^{−aw_q} and the vertical heat Gram form both have negative index = number of off-line zero quadruples ∈ ℕ ∪ {∞}, unconditionally, for every a > 0; RH ⇔ H_a ⪰ 0.
- **Hodge-index law** (`XiGaussianHeatArchPrimeHankel`, cycle 45): the Hankel matrix of the arithmetic moments w_n(a) = (−1)^n(Arch−Prime)^{(n)}(a)/π has negative index 1 + #off-line quadruples (ℕ∪{∞}); RH ⇔ it is ⪰ 0 on P(−¼) = 0.
- **Determinant criterion** (`XiGaussianHeatHankelDeterminants`, cycle 46): RH ⇔ det(M_{i+j}(a))_{i,j<N} > 0 for all N, with M_n(a) explicit arch−prime data; Sylvester's criterion added to HTGeometry.
- **Inertia and sign law** (`XiGaussianHeatHankelDeterminantSignLaw`, cycle 58): the negative inertia of the N-th heat moment section rises to #U ∈ ℕ∪{∞}. For finite U, (−1)^{#U}Δ_N(a) ≥ 0 for all large N, and infinitely many Δ_N(a) > 0 force #U even.
- **Linear window** (`XiGaussianHeatHankelLinearWindow`, cycle 65): H_a(P) = trace(Re P) + trace(Im P), Route U's polynomial-square trace. So Re H_a(P) > 0 whenever a(deg P + 1) ≤ κ (`heatHankel_re_pos_of_window`), and Δ_N(a) > 0 whenever aN ≤ κ (`heatMomentDet_pos_of_mul_le`). This supersedes the earlier super-exponential window.
- **Euler-factor parabola geometry** (`XiHeatEulerFactorParabolaDuality`, cycle 67): zeros lie strictly inside Re w > (Im w)² − ¼. Each Euler factor is, by Poisson summation, a heat trace over (2πm/log p − i/2)² on the boundary, and the vertex is the pole −¼.
- **Blow-up law** (`XiGaussianHeatHankelDeterminantBlowup`, cycle 71): under ¬RH some Δ_N vanishes in (κ/N, a₀] for every a₀ > 0, and RH ⇔ no Δ_N vanishes at positive heat time.
- **Complete monotonicity** (`XiGaussianHeatTraceCompleteMonotonicity`, cycle 74): RH ⇔ the real zero heat trace is completely monotone (via Bernstein–Widder, the holomorphy of `rateLaplaceC`, and the identity theorem).
- **Height horizon** (`XiGaussianHeatHankelHeightHorizon`, cycle 228): for every rank N there is H(N) with Δ_M(a) > 0 for all M ≤ N and all a > 0 whenever every off-line zero has |γ| > H(N) (`exists_height_heatMomentDet_pos`, `exists_height_forall_le_heatMomentDet_pos`). A nonpositive Δ_N anywhere locates an off-line zero of height ≤ H(N) (`exists_offLine_height_le_of_heatMomentDet_nonpos`). Proof via Hardy real zeros (`hardyRealZero`) as Lagrange nodes (`HTGeometry/PolynomialCoeffMassLagrange`), with the form-to-determinant bridge `heatMomentDet_pos_of_forall`.
- **Large-time detection** (`XiGaussianHeatHankelLargeTimeDetection`, cycle 246): for an off-line frequency u a bounded rank (other frequencies with Re w ≤ Re u + 1, plus two) carries a negative direction at every large heat time (`exists_heatHankel_re_neg_of_im_ne_zero`), so RH ⇔ ∀N, Δ_N(a) > 0 for all large a (`riemannHypothesis_iff_forall_eventually_heatMomentDet_pos`).
- Terminal state: STATUS MUST-904/912/939, CANNOT-503; ledger `1-in-progress/hcf-exact-layer-loop-2026-10-09.md` rows 42–246 (row 100: map of producer analogies onto corpus walls).
