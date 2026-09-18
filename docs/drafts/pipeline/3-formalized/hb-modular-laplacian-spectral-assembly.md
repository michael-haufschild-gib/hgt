# HB on-line clock: spectral assembly on the modular surface (input (ii)(b))

- **ID:** HB-SPEC-001
- **Stage:** 3-formalized (assembly inequality and the on-line sign law for the principal-subtraction source in Lean; the Maass–Selberg value of `⟨F,1⟩` for the Arthur-truncated source stays a paper input, off the critical path)
- **Type:** THEOREM (Lean)
- **Source:** docs/notes.md row 40, input (ii)(b); card `3-formalized/hb-scalar-scalar-quadratic-source-closed-forms.md` passes 26–30
- **Statement:** For `t ≥ 50`, `F := Λ¹(E*(·,½+it)²) ∈ L²(SL(2,ℤ)\H)`, `Δ` the Friedrichs Laplacian (`Δ ≤ 0`) and `K(s,·)` the certified plateau kernel at `s = −3/2+it`, `Im⟨F, K(s,Δ)F⟩ ≥ |⟨F,1⟩|²·Im K(s,0)/vol − t⁹·‖F − P₀F‖²`, where `P₀` is the orthogonal projection onto constants.

## Goal
This is the only input of the on-line sign law of the two-rate clock that is not yet a Lean theorem. Everything
else is certified: `Im K(s,0) ≥ t¹¹/2176` (`skewPlateauMu_constant_mode_im_ge`), `Im K(s,−l) ≥ −t⁹` for every
`l ≥ 0` (`skewPlateauMu_line_im_ge_neg`, combining the low band `[0,t]` and the uniform bound on `[t,∞)`),
`⟨F,1⟩ = c₀(ρ)·vol` with `c₀ = 4|ξ(1+2it)|²·Re(ξ'/ξ)(1+2it) > 0` and `t·c₀/|ξ(1+2it)|² → ∞`
(`XiLogDerivLineOnePositive`, `XiLogDerivLineOneGrowth`), and `‖F − P₀F‖² ≪ |ξ(1+2it)|⁴·O(1)` on the compact part
of the fundamental domain with the cusp part `≪ e^{−πt/2}t^{1+ε}` (`EisensteinCuspTailImaginaryOrderBound`).
With the statement above, the on-line clock coefficient has definite sign for all large `t`, which is the
consistency check of the route's physical premise on the line. It is receiver-side: it has no RH content and
does not touch the producer obstacle (C), which is closed by the general-Fuchsian barrier.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof (S1–S4 below), no open dependency
- [x] 2 → 3  formalized: Lean theorems `hb_online_clock_spectral_assembly'` (assembly, every `F ∈ L²(𝒟)`, `t ≥ 50`) and `hb_online_sign_law_eisenstein_source` (sign law for `F_P`, all large `t`); `lake build` green on both modules, axioms `propext, Classical.choice, Quot.sound`
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
What is actually needed is much less than the spectral theorem of the modular surface (no discreteness of the
spectrum below `¼`, no spectral gap, no Eisenstein Plancherel):
1. `L²(Γ\H)` with the hyperbolic measure on the standard fundamental domain (the corpus has the holomorphic
   Petersson product `peterssonInner` and `isFundamentalDomain_modularStrip`; a weight-0 version is needed).
2. The Dirichlet form `q(u) = ∫|∇u|²dμ` on `Γ`-periodic `H¹` and its Friedrichs extension `−Δ ≥ 0`
   (Mathlib has Lax–Milgram: `IsCoercive.continuousLinearEquivOfBilin`; no Friedrichs extension as such).
3. Resolvents `R(λ) = (Δ−λ)⁻¹` for `λ ∉ (−∞,0]` from Lax–Milgram on `q + (−λ)⟨·,·⟩`, with `R(λ)* = R(λ̄)`.
4. The spectral measure `μ_f` of a vector from the Herglotz function `λ ↦ ⟨f, R(λ)f⟩` (the corpus owns
   Herglotz/Nevanlinna representation tools: `BoundedRealHerglotz`, `CaratheodoryNevanlinnaPick`); it is a
   positive measure supported in `[0,∞)` in the variable `l = −μ`.
5. `K(s,·)` is rational with poles at `μ = 2` (double) and `μ = λ₁, λ̄₁` off the real axis, so
   `⟨f, K(s,Δ)f⟩ = ∫ K(s,μ)dμ_f(μ)` follows from 3–4 by partial fractions; then
   `Im⟨f,K f⟩ = ∫ Im K dμ_f ≥ −t⁹·μ_f([0,∞)) = −t⁹‖f‖²` for `f = F − P₀F`, using only the certified pointwise
   bound `Im K(s,−l) ≥ −t⁹` on `l ≥ 0`.
6. `μ_{F−P₀F}({0}) = 0` needs only "`L²` harmonic functions are constant", i.e. `q(u) = 0 ⟹ u` constant,
   which is elementary for the Friedrichs form.
Estimated size: several thousand lines; the hard parts are 1–2 (periodic `H¹` on the fundamental domain and the
form domain). No numerics, no RH input.

### Refined plan (2026-09-13, after the corpus audit)
Existing bricks: `HTGeometry/ModularFundamentalDomainMeasure.isFundamentalDomain_fd` (𝒟 is a fundamental domain for
`PSL2Z` with `dx dy/y²`), `ModularFundamentalDomainVolume.volume_fd_lt_top`, and
`HTGeometry/FriedrichsFormOperator` (`formEmbeddingCovariance J := J J†` bounded, positive, self-adjoint, injective
with dense range; `friedrichsFormOperator` its closed inverse; `friedrichsFormOperator_represents_form`). With these,
the unbounded Laplacian is never needed:
- B1. Pre-domain `P`: smooth `Γ`-invariant `u : ℍ → ℂ` with `∫_𝒟 |u|² dμ + ∫_𝒟 |∇u|² dx dy < ∞`
  (the Dirichlet form in Euclidean coordinates is the conformally invariant one), inner product
  `⟨u,v⟩_V = ⟨u,v⟩_{L²(𝒟)} + q(u,v)`.
- B2. `V := ` completion of `P`; `J : V →L L²(𝒟)` the extension of the inclusion, `‖J‖ ≤ 1`.
  Injectivity (closability of `q`) needs only interior test functions: if `u_n → 0` in `L²` and `∇u_n → G` in `L²`,
  test against `φ ∈ C_c^∞(𝒟°)` and integrate by parts inside a box (Mathlib divergence theorem), so `G = 0`.
  No Stokes theorem on the surface and no boundary identification is needed. Dense range: `C_c^∞(𝒟°)` extended
  `Γ`-periodically lies in `P` and is dense in `L²(𝒟)` because `∂𝒟` is null.
- B3. `C := formEmbeddingCovariance J = (1−Δ)⁻¹`: self-adjoint, `σ(C) ⊂ [0,1]` (from `‖J‖ ≤ 1` and positivity),
  and `C 1 = 1` since `q(1,·) = 0`.
- B4. Assembly: `g(r) := Im K(s, 1 − 1/r)` is continuous on `[0,1]` (the kernel has a finite limit as `l → ∞`) and
  `g ≥ −t⁹` on `[0,1]` by `skewPlateauMu_line_im_ge_neg`; split `F = ⟨F,1⟩/vol·1 + F⊥`; `cfc g C 1 = g(1)·1`, the
  cross terms vanish by self-adjointness, and `re_inner_cfc_self_ge` gives
  `Re⟪cfc g C F⊥, F⊥⟫ ≥ −t⁹‖F⊥‖²`.
Remaining hard content: B1–B2 (smooth `Γ`-invariant functions as a pre-Hilbert space, the completion, the
integration-by-parts argument). Everything else is assembled from existing theorems.

## Log
- 2026-09-13 — created in 0-backlog after passes 26–30 closed every other input of the on-line sign law; the
  reduction to steps 1–6 (no spectral gap, no discreteness, no Eisenstein Plancherel) is the scoping result.
- 2026-09-13 — step 5 discharged in abstract form: `HTGeometry/SelfAdjointFunctionalCalculusLowerBound.re_inner_cfc_self_ge` (bounded self-adjoint `A`, `c ≤ g` on the spectrum ⇒ `c‖f‖² ≤ Re⟪g(A)f,f⟫`); with `A = (1−Δ)⁻¹` no spectral measure is needed. Remaining: steps 1–3 and 6.
- 2026-09-13 — corpus audit: fundamental-domain measure and Friedrichs covariance already exist; plan refined to B1–B4 (bounded covariance only, closability via interior test functions, no surface Stokes theorem).
- 2026-09-13 — B3–B4 CLOSED IN LEAN: `HTGeometry/CfcEigenvectorRankOneAssembly`, `HTGeometry/FormEmbeddingCovarianceSpectrum`, `HTGeometry/ModularDirichletFormDomain` (`modular_spectral_assembly`, `modularCovariance_one`, `inner_modularOne`, `norm_modularOne_sq`; standard axioms). The HB kernel specialisation (`skewPlateauCov`, `hb_online_clock_spectral_assembly`) is written in the scratchpad and waits for the `ThetaCuspHawkingBM` chain to be rebuilt. Remaining: B1–B2 meaning content (`J` injective and of dense range), and the source `F = Λ¹(E*²)` as an `L²(𝒟)` element.
- 2026-09-13 — B2 closability CLOSED IN LEAN: `HTGeometry/ModularDirichletFormIntegrationByParts`, `HTGeometry/ModularDirichletFormClosable` (`formInclusion_injective`). Remaining: dense range of `J` (D1 continuous approximation in `L²(𝒟)`, D2 smoothing with support in `𝒟°`, D3 periodisation into the pre-domain), the HB kernel module (scratchpad, chain blocked), and the source element `F = Λ¹(E*²)`.
- 2026-09-13 — dense range CLOSED IN LEAN (`…Periodization`, `…SmoothApprox`, `…Dense`): `modularFriedrichsOperator` is the self-adjoint Friedrichs Laplacian `1−Δ` with bounded inverse `modularCovariance`. B1–B4 all closed. Remaining: the HB kernel module (scratchpad `CovKer.lean`, blocked on the `ThetaCuspHawkingBM` chain rebuild) and the source element `F = Λ¹(E*²)` in `L²(𝒟)`.
- 2026-09-13 — accounting: `⟨F,1⟩ = ‖Λ¹E*‖²` is the Maass–Selberg relation at `Y = 1` (paper input); Lean would need the real-analytic Eisenstein series on the line as a Γ-invariant eigenfunction (corpus gap: Fourier model vs Poincaré sum). Dominance needs `A ≥ 50` in `exists_re_logDeriv_xi_lineOne_ge_div`.
- 2026-09-13 — kernel module IN TREE: `RHTower/ThetaCuspHawkingBMSkewPlateauCovarianceKernel` (`hb_online_clock_spectral_assembly'`: `t¹¹/2176·|∫_𝒟F|²/vol 𝒟 − t⁹‖F−P₀F‖² ≤ Re⟪(Im K̂)(C)F,F⟫`, `t ≥ 50`, every `F ∈ L²(𝒟)`); axioms standard (scratch), `lake build` audit deferred (upstream chain under rebuild by another agent). Remaining: source `F` + bound (α) via the Fourier model; Maass–Selberg value of `⟨F,1⟩` (needs the Eisenstein series on the line).

### Eisenstein on the line (E1–E4, scoped 2026-09-13 evening)
The corpus already has, at the absolute-convergence parameter `Re s > 1`: the completed Poincaré series
(`d4BMCompletedEisensteinPoincareSeries`), its `S`/`T` invariance (`…ModularGeneratorInvariance`), its
eigen-equation, and its identification with the cusp Fourier model
(`d4BM_actualCompletedPoincare_eq_canonicalCuspLeg : Poincaré(x + i y) = d4BMCompletedEisensteinCuspLeg .scalar (s − 1/2) x y`).
The Fourier model is defined for every parameter `u`; so the line is reached by analytic continuation in `u`:
- E1. `u ↦ cuspLeg .scalar u x Y` is `DifferentiableOn ℂ` on the quarter-plane `Ω = {−1/2 < Re u, 0 < Im u}`
  (convex, so preconnected; contains `{Re u > 1/2, Im u > 0}` and the line points `it`, `t > 0`; avoids the
  real poles of `Λ(2u)`, `Λ(1+2u)`). Constant part: `reflectedCompletedLambda = Γ_ℝ·ζ` via
  `Complex.differentiableAt_Gamma`, `differentiableAt_riemannZeta`, `DifferentiableAt.const_cpow`; tail: locally
  `Complex.differentiableOn_tsum_of_summable_norm` with `analyticOnNhd_modifiedBesselKOrder`, the coefficient bound
  `‖coef(u,n)‖ ≤ n^{3|Re u|+1}` and the order-uniform Bessel bound `d4BM_norm_modifiedBesselKOrder_le`.
- E2. Identity theorem (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`) for
  `u ↦ leg(u, S·z) − leg(u, z)` (translation invariance is exact in the Fourier phases), then
  `SpecialLinearGroup.SL2Z_generators` + `Subgroup.closure_induction`: `E*(·, ½ + it)` is an `SL(2,ℤ)`-invariant
  function on `ℍ`, defined by the Fourier model.
- E3. Eigen-equation on the line: the corpus has `d4BM_canonicalCuspFullSecondJet_eigenEquation` for every `u`
  (`Y ≥ 1`) and the Poincaré/canonical second-jet weld for `Re s > 1`; identify the canonical jets with the true
  derivatives of the leg for all `u` (or continue by the identity theorem), and extend below `Y = 1`.
- E4. Maass–Selberg at `Y = 1` on the line by Green's identity on the truncated fundamental domain for the
  invariant eigenfunction (corpus: the truncated modular Green/Stokes modules at `Re s > 1`), giving
  `⟨F,1⟩ = ‖Λ¹E*‖² = 4|ξ|²Re(ξ'/ξ)(1+2it) + Im(ξ(1+2it)²)/t`.
E1–E2 CLOSED IN LEAN (2026-09-13 night): `RHTower/ThetaCuspHawkingBMEisensteinLineInvariance` (`differentiableOn_cuspLeg`, `eisensteinLineModel_smul`, `eisensteinLineModel_I_mul_smul`); axioms standard (scratch), `lake build` audit deferred with the chain. E3–E4 are larger.
- 2026-09-13 (night) — E3/E4 scoping notes. E3: the corpus has first-jet `hasDerivAt` theorems for the signed
  Whittaker tails (`…ActualSignedFirstJetWeld`), the canonical full second jet with its eigen-equation for every
  `u` at `Y ≥ 1` (`d4BM_canonicalCuspFullSecondJet_eigenEquation`), and the Poincaré/canonical second-jet weld
  at `Re s > 1`; the line eigen-equation follows once the canonical jets are shown to be the true chart
  derivatives of the model for all `u` in the quarter-plane (termwise differentiation with the order-uniform
  Bessel bounds, as in E1) and the height restriction `Y ≥ 1` is removed (needed down to `y = √3/2`).
  E4: unfolding does NOT bypass Green's identity — the `x`-average of `Λ^Y E*` on the strip is not the
  truncated constant term for small `y` (other cusp translates contribute), so the Maass–Selberg value needs
  Green's identity on `𝒟_Y` for two invariant `C²` eigenfunctions (side cancellation from invariance by the
  chain rule, no series needed) plus the cusp boundary term from the Fourier expansion, then `s' → s̄`.
- 2026-09-13 (late) — E3 refined: NO identity theorem needed. The corpus has, for every height `Y > 0`, the
  per-mode derivatives (`hasDerivAt_d4BMSignedWhittakerMode_{horizontal,vertical}`, second jets) and the
  per-mode eigen-equation `d4BM_signedWhittakerMode_secondJet_eigenEquation`, and the constant-part
  eigen-equation `d4BM_cuspConstantFullSecondJet_eigenEquation`; only the *summable majorants* of the mode jets
  are restricted to `Y ≥ 1` (`d4BM_norm_modifiedBesselKOrder_signed_local_le`). Plan: (A) all-heights majorants
  on `Y ∈ [Y₀/2, 2Y₀]` for the mode and its jets, from `d4BM_norm_modifiedBesselKOrder_le` applied to the
  shifted orders `ν + k`, `|k| ≤ 2` (every jet is a finite combination of `√Y·K_{cY}(ν+k)` with polynomial
  factors), times the coefficient bound `(N+1)^{3|Re u|+1}`; (B) `hasDerivAt_tsum_of_isPreconnected` in `x`
  and in `Y` (twice) for the weighted tails; (C) sum the per-mode eigen-equations: the model satisfies
  `Y²(∂²_x + ∂²_Y)E* = (u² − 1/4)E*` for every `u` and every `z ∈ ℍ`; then transport to the chart
  Laplacian on `ℍ` (partials → Fréchet derivatives) for E4.
- 2026-09-13 (late) — E3 step A CLOSED IN LEAN: `RHTower/ThetaCuspHawkingBMEisensteinModeJetMajorants` (window Bessel bound `norm_modifiedBesselKOrder_window_le`, the `WindowDominated` predicate with closure lemmas, degree-`d` majorants for `P₀, P₀', P₁, P₁'`, the raise-zero words, the second jet `whittakerP0SecondJetR`, all signed-mode jets, `summable_pow_mul_besselModeMajorant`, `WindowDominated.weighted`); axioms standard (scratch). Next: step B, termwise differentiation of the weighted tails in `x` and `Y` via `hasDerivAt_tsum_of_isPreconnected`.
- 2026-09-13 (late) — E3 CLOSED IN LEAN: `RHTower/ThetaCuspHawkingBMEisensteinLineEigenEquation` (`weightedTail`, termwise `∂_x`, `∂²_x`, `∂_Y`, `∂²_Y` via `hasDerivAt_tsum_of_isPreconnected` with the all-heights majorants; `weightedTail_eigen`; constant-part derivatives; `lineModel_eq_cuspLeg`; `lineModel_eigen : Y²(∂²_x + ∂²_Y)E* = (u² − 1/4)E*` for every `u` and `Y > 0`; `lineModel_eigen_deriv`). Axioms standard (scratch, concatenated with the majorant module because my new modules have no oleans: their import closure contains a stale `HTGeometry/MilnorKTheory` with 24 dependents, so a `lake build` would cascade; audits deferred). Remaining: E4 (Green's identity on the truncated domain, the cusp boundary term, `s' → s̄`) and the source element.
- 2026-09-13 (late, correction from the numerics in `2-fully-proven/computations/results.md`, section "Eisenstein
  source components and cusp subtraction"). Their `R = t² M²/(2176 V₀ V)` with `M = ∫F`, `V = ‖F − P₀F‖²` is exactly
  the assembled bound's dominance ratio. Findings: (1) principal subtraction `F_P = S² − 1_{y>H} a₀²` at `H = 1`
  gives `R ≈ 0.15, 0.82, 3.03` at `t = 50` and zeta ordinates 24, 64; the smooth corpus cutoff gives
  `0.35, 1.12, 4.06`; (2) subtracting the full zeroth Fourier mode of `S²` (Arthur truncation of the square,
  which is what the card called `Λ¹(E*²)`) gives `R ≈ 0.004–0.02`: the constant mode loses the cusp mass of the
  tail, `M_C = M_P − ∫_{y>H} Q dμ`. Corrections to the earlier accounting: (a) my claim
  `⟨Λ¹(E*²),1⟩ = ‖Λ¹E*‖²` holds for the principal subtraction (cross term vanishes, tail² kept), not for the full
  subtraction; (b) the normalized Eisenstein tail is `O(1)` relative to the constant term (the certified sup bound
  `B_t/|Λ| ≍ t log²t/|ζ(1+2it)|` is large, and numerically `V ≈ 2·10²` at `t = 50`), so
  `‖F‖² ≤ 16(π/3)|Λ|⁴(1+o(1))` is false; (c) the true sizes are `M ≈ 4|Λ|²Re(ξ'/ξ)(1+2it) ≈ 2|Λ|² log(t/π)`
  (from `Re ψ(½+it)`, far above the certified `A/t` lower bound) and `V ≍ |Λ|⁴·polylog t`, so `R ≍ t²/polylog`
  and the sign law holds for all large `t`, numerically from ordinate ≈ 30 for `F_P`. Certified route for `V`:
  Parseval in `x` on the strip (no cross terms between modes) with the certified `K_{it}` bounds and
  `Σ_{n≤N} d(n)²/n ≪ log⁴N` gives `V ≲ t log⁸ t·|Λ|⁴` — enough for `R → ∞` (`R ≳ t/log⁶ t`) but with an
  astronomically large threshold; a polylog bound for `V` is a fourth-moment estimate for truncated Eisenstein
  series (cf. arXiv 2408.14815). The source convention (principal vs full subtraction, sharp vs smooth cutoff)
  must be fixed by the physical action, not by the favourable value of `R`.

### The sign law without Maass–Selberg (plan S1–S4, 2026-09-13 late)
With the principal-subtraction source `F_P = E*² − 1_{y>H} c(y)²` (`c` the Weyl constant term, `H ≥ 1` fixed), the
assembled bound needs only `t² M² > 2176·vol·V` with `M = ∫_𝒟 F_P`, `V = ‖F_P‖²`. Both sides are elementary:
- S1. `F_P` as an `L²(𝒟)` element from the Fourier model (`lineModel`), real-valued on the line (constant part
  real by `Λ(2it) = conj Λ(1+2it)`, tail real by the coefficient symmetry `d ↔ n/d` and `K_{it}` real).
- S2. Lower bound `M ≥ ∫_1^H ∫_0^1 E*² dx dy/y² ≥ ∫_1^H c(y)² dy/y² = 2|Λ(1+2it)|²(log H − 1/t)` — the tail has
  zero mean in `x` and `tail² ≥ 0`, so no Maass–Selberg relation and no Green identity are needed.
- S3. Upper bound `V ≤ C·t·log^k t·|Λ|⁴ + 16H²·vol·|Λ|⁴`: Parseval in `x` for `∫ tail² dx = Σ|a_n|²`, Young's
  inequality `∫ tail⁴ dx ≤ (Σ|a_n|)²Σ|a_n|²`, the certified `K_{it}` bounds (uniform for `x ≥ 1`, `e·e^{−x}` for
  large `x`), and `Σ_{n≤N} d(n)² ≤ N(1+log N)³` (corpus `Sieve`). The normalized tail is `O(1)`, so sup norms
  alone cannot give this; the mean-square structure is essential.
- S4. Combine with `hb_online_clock_spectral_assembly'`: `∃ t₀, ∀ t ≥ t₀`, the on-line clock coefficient
  `Re⟪(Im K̂)(C)F_P, F_P⟫` is positive. The threshold is large (numerics: crossover near zeta ordinate 30).
E4 (Green's identity / Maass–Selberg) is thereby removed from the critical path of the sign law.
- 2026-09-18 — S1–S4 CLOSED IN LEAN (`H = e²`). Modules (namespace `RHTower`): `BesselKImaginaryOrderPowerSaving`
  (`‖K_{iτ}(x)‖ ≤ 420 e^{−πτ/2} τ^{−1/3}` for `τ ≥ 2`, `x > 0`, by the contour `θ = π/2 − 1/τ` and the corpus's
  first/second derivative tests), `EisensteinLineModeSizeBounds` (ℓ¹/ℓ² mode sums, head `N ≤ t/(πY)` with the
  power saving, tail geometric), `EisensteinLineTailParseval` (`∫_0^1‖tail‖² = 8Σ modeSize²`, zero mean in `x`,
  `‖tail‖ ≤ 4Σ modeSize`), `EisensteinLineConstantTerm` (`∫_1^{e²}‖c‖²/y² ≥ (5/2)‖Λ‖²`,
  `‖Λ‖² ≥ e^{−πt}‖ζ(1+2it)‖²`), `EisensteinLineSourceSlices` / `…Integrability` / `…MeanSquare`
  (`M ≥ (5/2)‖Λ‖²`, `V ≤ 128‖Λ‖⁴e² + 256‖Λ‖²P₂(log t+1) + 2K(t)`), `EisensteinLineSourceL2` (the `L²(𝒟)`
  element, `∫_𝒟 F = M`, `‖F‖² = V`, `‖F − P₀F‖² ≤ ‖F‖²`, `0 < vol 𝒟 ≤ 2`), `EisensteinLineSourceRatio`
  (`V ≤ ‖Λ‖⁴(128e² + B t^{5/3}(log t)^{50})` for `t ≥ T`, using the corpus's
  `exists_lower_bound_riemannZeta_near_one_line`), `HBOnLineSignLawEisensteinSource`
  (`hb_online_sign_law_eisenstein_source`). S2 used `H = e²` (so `log H − 1/t ≥ 3/2`) rather than a free `H`.
  S3's exponent is `t^{5/3}` polylog, weaker than the card's `t log^k t` (the ℓ¹ head sum is bounded by
  `t^{2/3}(1+log(t+1))/(π√Y)` instead of a divisor-sum estimate) but sufficient since `t^{5/3+ε} = o(t²)`.
  Threshold implicit (from the zeta lower bound constants); the numerics' crossover near ordinate 30 is not
  certified. Receiver-side; no RH content (STATUS MUST-351).
