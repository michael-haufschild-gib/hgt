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
- `exists_norm_xiGaussianHeatTraceC_le_quadratic_coefficient`: quadratic coefficient ≤ Δ∞²/a; lower half PROVED in `XiGaussianHeatVerticalQuadraticLowerLaw` (`vertical_quadratic_rate_le_iff`: exact rate Δ∞²/a).
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
- **Root-flip symmetry** (`XiGaussianHeatHankelRootFlip`, cycle 527): H_a depends only on the Hermitian square P·P^*, so the root flip (P/(X−r))(X−r̄) preserves H_a for every a, without RH (`heatHankel_rootFlip`). A Rayleigh ground state of Re H_a/g that is unique up to scalars has only real roots, for any reference g depending only on P·P^* (`im_eq_zero_of_heatHankel_simple_minimizer`). This is the polynomial analog of the CvS zero flip (MUST-787/788). STATUS MUST-948.
- Window dichotomy (row 530, paper): the test class at (a, N) has Weil aperture 2√(aN), so ¬RH ⇒ a*_N = O(1/N). With the Lean window a*_N ≥ κ/N, the window is either infinite (RH) or of exact order 1/N.
- **Real-node witnesses** (`XiGaussianHeatHankelRealNodeWitness`, cycle 540): Re H_a(Q(X−r)) = Re H_a(Q(X−Re r)) + (Im r)² Re H_a(Q), so negative directions are witnessed by ∏(X − x_i) with real nodes and no larger degree. RH ⟺ Re Σ_q e^{−aw_q}∏(w_q − x_i)² ≥ 0 for all real nodes (`riemannHypothesis_iff_realNodes_heatHankel_nonneg`). STATUS MUST-1217.
- **Window ceiling** (`XiGaussianHeatHankelWindowCeiling`, cycle 548): without RH, some Δ_M(a) ≤ 0 with M ≤ D log³(1/a)/a + 1 at every small a (`exists_heatMomentDet_nonpos_small_time`). With the linear window this brackets the HCF window, κ/N ≤ a*_N ≤ C log³N/N, under ¬RH. STATUS MUST-1221.
- **Complete inertia** (`XiGaussianHeatHankelInertia`, cycle 551): H_a is nondegenerate (`eq_zero_of_forall_heatHankel_eq_zero`) with infinite positive index (`exists_heatHankel_pos_subspace`). With the index law its inertia is (∞, #U, 0), so (ℂ[X], H_a) is a Pontryagin space Π_{#U}. STATUS MUST-1224.
- **Jacobi's rule** (`XiGaussianHeatHankelJacobiSignChanges`, cycle 554): at any heat time where no Δ_N(a) vanishes, the number of off-line zero quadruples equals the number of sign changes of (Δ_N(a))_N (`card_eq_signChanges_heatMomentDet`). Such heat times are dense in (0,∞), unconditionally (`exists_heatTime_signChanges_eq_card`). STATUS MUST-1227.
- **Polynomial horizon** (`XiGaussianHeatHankelPolynomialHorizon`, `XiCriticalZeroSeparatedNodes`, cycles 557–558): ∃C, if all off-line zeros have |γ| > C·N^{63}, then Δ_M(a) > 0 for all M ≤ N and all a (`exists_poly_height_heatMomentDet_pos`). This is the quantitative CANNOT-503, with nodes from the Hardy census. STATUS MUST-1228.
- **Near-linear horizon** (`XiGaussianHeatHankelLinearHorizon`, `XiCriticalZeroLinearNodes`, cycles 559–560): ∃C, if all off-line zeros have γ² > C(N+1)²(1 + log(N+1)), then Δ_M(a) > 0 for all M ≤ N and all a > 0. Nodes are linear in rank via the pinned Montgomery–Taylor proportion. With MUST-939 the detection rank of an off-line zero at height γ is γ^{1+o(1)}, so finite-rank HCF is a height verification. STATUS MUST-1238.
- **Small-time complete monotonicity** (`XiHeatMomentSmallTimePositivity`, cycle 561): ∃a₀ > 0, M_n(a) > 0 for all n and 0 < a ≤ a₀, unconditionally (phase locking at the peak √(n/a)). The CM criterion's content lies at a > a₀. Corrects the BLOCKED verdict of ledger row 72. STATUS MUST-1232.
- **Localized inertia** (`XiGaussianHeatHankelLinearHorizon`, cycle 562): rank-(d+1) negative index ≤ #distinct upper off-line frequencies with Re w ≤ C(d+1)²(1 + log(d+1)), at every heat time. The Jacobi form bounds sign changes of Δ_0..Δ_{d+1}. STATUS MUST-1233.
- **Stable tests** (`XiHeatStableTestPositivity`, cycle 563): at a ≤ a₀, Re H_a(P,P) > 0 for every nonzero P with roots in Re r ≤ 0, any degree. The RH content at small heat time needs nodes in Re w > 0. STATUS MUST-1237.
- **Positive-node form** (`XiGaussianHeatHankelPositiveNodeWitness`, cycle 564): RH ⟺ Re Σ_q e^{−aw_q}∏(w_q − x_i)² ≥ 0 for all a > 0 and all positive real nodes. Witnesses exist at arbitrarily large resonant heat times. Dual to stable-test positivity (MUST-1237). STATUS MUST-1241.
- **Large-time census** (`XiGaussianHeatHankelLargeTimeCensus`, cycle 571): eventually sign(conj on S_L)·Δ_{\|S_L\|}(a) > 0. The large-time ladder is a parity census of off-line zeros by height. STATUS MUST-1245.
- **Exact large-time inertia** (`XiGaussianHeatHankelLargeTimeInertia`, cycle 572): eventually hermNegIndex(section of rank |S_L|) = #{upper off-line frequencies with Re ≤ L}, positive index #{Im ≥ 0}, null index 0. RH ⟺ every level is eventually positive definite. This sharpens the parity census to the exact count. STATUS MUST-1248.
- **Window at the optimal order** (`XiGaussianHeatHankelExponentialTypeTransfer`, `XiGaussianHeatHankelSincLevelWitness`, cycle 573): ¬RH ⇒ some Δ_k(K/n) ≤ 0, k ≤ n+1, for all large n; RH ⟺ every window constant K is eventually admissible. This replaces the log³N/N ceiling by K/N. The transfer is unconditional for any even exponential-type zero-side witness (K > (eB+1)²/4). STATUS MUST-1251.

- **Scale capstone** (`XiGaussianHeatRouteScaleCapstone.hcf_scale_capstone`, 2026-10-11) collects across heat-time scales: the unconditional window aN ≤ κ; RH ⟺ every window constant K admissible (MUST-1251); the 1/N ceiling under ¬RH; no intermediate growth (MUST-1254); exact large-time inertia and RH ⟺ every level eventually definite (MUST-1248). The route producer is a single statement: unbounded window constant, which is all-aperture Weil positivity (R2). Producer search: ledger rows 576–587, none found.
- **Window from a Weil margin** (MUST-1261, 2026-10-11): a pole-vanishing margin μ₀(A) > 0 gives the HCF window aN ≤ K for every K < A²/4 on the pole hyperplane, at the sharp turning-point constant. Unconditional instance aN ≤ 1/32 (prime 2 included), at most one negative square. Card `hcf-window-aperture-converse.md`.
