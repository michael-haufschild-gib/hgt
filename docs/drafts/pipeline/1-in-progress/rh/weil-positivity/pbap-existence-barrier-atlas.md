# Prime-blind positivity: the existence problem and its barriers

- **ID:** pbap-existence-atlas
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (open-core map with proved laws)
- **Source:** route-tt loop rows 380–459 (`1-in-progress/route-tt-loop-2026-10-13.md`)
- **Statement:** RH is equivalent to PBAP, the nonnegativity of ζ's pole and archimedean functional on PD tests blind at every log n. Uniqueness of the Weil cone is complete and unconditional. Existence is the entire RH content; this card maps where existence can and cannot come from.

## Goal
A producer of PBAP (equivalently of a positive spectral measure with atoms at the zeros) from ζ-free or automorphic data. The non-circularity requirement is that the producer must not encode the zero locations.

## What is proved (Lean unless marked)
- RH ⟺ PBAP (`TwistedArcMinimumPrincipleProof`).
- PBAP_S ⟺ RH ∧ S ⊇ {prime powers} (`PrimeBlindNodeCriticality`).
- Pole-weight window ⊆ {1}, unconditional (`WeilPoleWeightForcedOne`, built on `WeilPoleWeightWindow`).
- Degree classification: the only Γ_ℝ^d member with RH is ζ^d (`WeilConeDegreeHerglotzClassification`).
- Anomaly bound: Re P + γ(0)‖f‖² ≤ weilArchRe. Strong violators are pole-negative (`WeilBlindPoleSignLaw`).
- Positive classes far from the null face: separated narrow bumps (`SeparatedBumpPrimeBlindPositivity`, another lane) and windows (corpus ground energy ≥ 1/10).
- [P] Null face analytic part = one ray G₀ = (E′ geodesic profile) ⋆ (arc kernel). Index law: cusp +1, corner +1, kernel −2, excluded mode +1.
- [P] The arc-TMP mechanism exists only for SL₂(ℤ):
  - Dirichlet characters q ≥ 2: the Fricke circle radius 1/q fails to separate.
  - Fricke groups Γ₀(2)⁺, Γ₀(3)⁺: the central L-function ζ²(1+p^{½−w}) is never a square.
  - Non-arithmetic Hecke groups: no Euler product.

## Proved laws on where positivity can come from [P]
1. **Two budgets.** On blind tests, arch ≥ (Ω(0) + Cap)·g(0), where Cap < |Ω(0)| ≈ 5.37 is the integers' Lévy capacity (strictness certified by G₀). The pole must cover the remainder. Every deformation (pole weight, conductor, node dilation, Hecke/Fricke group) is critical exactly at ζ's data.
2. **Exact inertia of the Markov part (row 466; corrects row 460).** W = M + P, with M Markovian (archimedean and prime jumps) and P of signature (1,1).
   - With k distinct off-line quadruples, (ind₋(M_even), ind₋(M_odd)) = (k+1, k) exactly.
   - The endpoints are pinned by the Weil-null Riemann kernels Φ and Φ′ (Φ̂ = Ξ), with C(Φ) = ½ and S(Φ′) = −¼.
   - [L] `WeilMarkovOneBoundState.riemannHypothesis_iff_not_exists_negDef_markovPlane`: RH ⟺ no plane carries a negative-definite archimedean-minus-prime form.
   - With `exists_markovEnergy_neg`, RH ⟺ exactly one bound state.
   - The −2 loss in the corpus inertia law is removable.
   - Soft bound-state counts diverge (row 454).
2b. **Doob transform by Φ (row 467) [P].** W(Φv) = 𝓔(v) − ‖v‖²_m + 2(∫v dm)² − 2(∫vτ dm)², where:
   - m = Φcosh(x/2)dx;
   - 𝓔 is a Dirichlet form with jump kernels ω and Λ.
   - On even v: RH ⟺ the Poincaré inequality 𝓔 ≥ ½Var_π, for the symmetrized Biane–Pitman–Yor law π = 2Φcosh(x/2)dx.
   - The gap eigenvalue has infinite multiplicity unconditionally (Ξ-divisible pole-free tests).
   - −L = (rate-1 reset) + (zero Gram) on L²(m) = ℂ1 ⊕ E₁ ⊕ Z.
   - The prime reset rate is exactly 1 + (ΩΞ)^∨/cosh(x/2).
   - ζ(s−a)ζ(s+a) has the same Markov structure, so a proof must use coefficient size (wall 9).
2c. **Exactness law (row 468).** The gap 1 is attained on an infinite-dimensional space, and off-line zeros are threshold resonances at 1 − exp(−Θ(e^{2L})). So any proof with slack fails: coupling, curvature, Lyapunov, CLR. Only an exact sum-of-squares or spectral identity can certify RH (wall 12, quantitative).
3. **Null edge at infinity.** Under RH the moment region's lower boundary is the half-line {(P, −P) : P ≤ P₀}. Only G₀ attains it; the rest is a Tauberian limit of chirp-scale tests that interpolate zeta's zero set up to the Nyquist height (no smooth blow-up, by Titchmarsh). Every explicit positive class sits at positive distance from this edge.
4. **Atoms versus densities.** Every proven positivity in reach yields densities that vanish at zeros, or bounds kept away from the edge. This covers unitarity, Maass–Selberg, Rankin–Selberg, Kuznetsov with Weil/Salié bounds, Lévy energy and Pitt/Beckner. RH needs a positive measure with atoms at the zeros, i.e. a point spectrum (wall 12).
5. **Incompatible algebras.** On Dirichlet-polynomial tests the arithmetic part is divisibility-triangular (Smith/GCD-positive, product-type symbols) while the archimedean part is quotient-type multiplicative Toeplitz, so no divisibility Cholesky factorization exists.

## Open sub-problems (sharp, ζ-free or explicit)
- **Cores.** Do Ψ-blind compact cores (ζ-divisible wandering vectors with compactly supported Möbius inverse) exist for large support ratio?
  - The dimension count gives threshold 2, which matches the proven no-go.
  - The dual separators are Hurwitz-type combs; bounded separators are impossible beyond ratio ≈ 5.83.
  - Only ≈ 215 = e^{|Ω(0)|} constraints resonate.
- **Sign of S = Σ Λ(n)n^{−½} log n · G₀′(log n).** It decides whether node dilation is doubly critical at ζ.
- **Quasi-RH ladder.** PBAP(t) ⟸ (zero-free strip Re s > 1 − t/2) + anomaly fill. The converse has no mechanism.
- **Bound-state form.** A nonlocal oscillation theory for arithmetic jump operators would bound ind₋(M_even) and so the number of off-line quadruples. The last quadruple needs the sign content of the pole (row 460).

## No-go closure
- **Killing mechanisms:** wall 12 (forced dual measure), atoms/densities (law 4), the null edge at infinity (law 3).
- **Strongest positive survivor:** the Lean anomaly bound and pole-sign law (`WeilBlindPoleSignLaw`), the unconditional window ⊆ {1}, and the uniqueness of ζ in the arc mechanism.
- **New insight:** the existence problem is concentrated on a single geometric locus (the null edge at infinity), whose tests are chirp-scale zero interpolants. No finite-scale, unitary or Markovian positivity reaches it.
- **Status:** OPEN. The paper laws are in the route-tt log rows 435–459.

## Log
- 2026-10-14 — created from route-tt rows 380–459.
- 2026-10-14 (opus loop row 1211, MUST-1467): `SeparatedBumpPrimeBlindPositivity` is now uniform in the number of bumps (`exists_primeBlind_nonneg_bumpSum`, packing lemma `natCast_le_one_add_div_of_separated`). Support-blind tests have Lévy gain Θ(log 1/δ) against pole loss O(√δ log 1/δ). Violators must be blind by cancellation. Open: the critical separation scale. The crude bound needs s ≳ 9.3√δ. Is there a support-blind violator at s ≍ √δ, or does positivity persist down to s ≍ δ?
- 2026-10-14 (opus loop row 1212, MUST-1471): `SeparatedBumpWeilPositivity` gives FULL Weil positivity for separated narrow bumps of span < 2 log(1/δ), with no blindness. The threshold 2 log(1/δ) is the pole scale: beyond it you need short-interval PNT with error o(e^{D/2}). Finite-scale positivity classes now cover both the blind and the non-blind narrow-bump regimes below the pole scale. Both stay away from the null edge.
- 2026-10-14 (opus loop row 1213): CORRECTION to route-TT rows 462–464 (RH ⟺ PBAP_even, m_e ≤ 0 via G₀).
  - Autocorrelations of EVEN tests satisfy ĝ(iy) = |∫e(u)e^{yu}du|² ≥ 0 for all real y, so the even cone ⊆ {ĝ ≥ 0 on ℝ ∪ iℝ}.
  - The shifted-Gamma tests F̂_j = ΞQ_j have ĝ_j(iy) < 0 on ½ < |y| < 5/2 for every j ≥ 1. So the corpus uniqueness chain is not available in the even sector.
  - G₀ is even-type iff S(y) = 4√2/√π·Γ(¾−y/2)Γ(¾+y/2)∫√(y_u/2)·½[P_{y−½}(u) + P_{y−½}(−u)]dν* ≥ 0 for all real y (exact ₂F₁ identity).
  - Large-y Legendre asymptotics reduce this to a nonnegative cosine transform of the arc measure in the angle variable. That fails if ν* has atoms at the corner ρ.
  - Status: RH ⟹ PBAP_even only; the converse is OPEN.
- 2026-10-14 (row 1213, Lean): MUST-1472 / CANNOT-554 `RHTower/EvenTestLaplacePositivity`. Even-type autocorrelations are ≥ 0 on iℝ. The shifted-Gamma tests are < 0 at ½ < y < ¾ for every j ≥ 1. Whether the even cone is thin (an "even TMP") is the open core of the even sector.
- 2026-10-14 — route-tt rows 461–468:
  - Parity split: the TMP floor is an even-sector fact and the density ceiling an odd-sector fact. RH ⟺ PBAP_even [P sketch].
  - Exact inertia (k+1, k) [P], with the one-bound-state law in Lean (`WeilMarkovOneBoundState`).
  - Doob/BPY Poincaré form of RH [P].
  - Exactness law.
- 2026-10-14 (row 1214, MUST-1473): extreme-pair principle. A single blind test built from positive narrow bumps has span < log(2/δ) however the blindness arises, so it is PBAP-positive. Single-test violators need edge profiles whose self-correlation vanishes on the dense node set near the extreme lag (chirp edges, cf. route-TT row 457).
- 2026-10-14 — rows 469–476 (user directive: prove that M = arch − primes has exactly one negative square):
  - [L] RH ⟺ M ≥ 0 on odd tests (`WeilMarkovOddPositivity`). The pole's single negative square lives in the even sector, and ind₋M_e − ind₋M_o = 1 unconditionally.
  - In the odd half-line picture, the obstruction is the anti-Markov reflected-prime ("product", XY = n) jumps.
  - Uniform sign law: every Doob/ground-state/reset frame leaves exactly one sign-bad kernel component, namely the PNT remainder (pole ↔ prime main term). So positivity is exact cancellation at √x precision (wall 1).
  - Refined exactness law: slack is available only modulo the Weil radical E₁, where the form is the zero-data form.
  - Killed mechanisms: SUSY index, hyperbolic-Laplacian/Selberg-¼, inverse scattering, Gutzwiller sign, positivity mod radical, tensor-power trick, virial/Pohozaev, spectral synthesis, exact reset.
- 2026-10-15 (opus loop row 1215, MUST-1475): CONE-level PBAP for narrow-bump configurations with any bump sign pattern of regularity κ, blind only in combination (`SeparatedBumpConePositivity`). The new ζ-free tail lemma `HTGeometry/LogNodeExponentialTail`: a function vanishing at every log n contributes only √2·Lip/√N₀ to the e^{y/2}-moment beyond log N₀. Cone-level violators therefore need roughness at far lags plus anomaly-window mass.
- 2026-10-15 (row 1217): STALE CLAIMS CORRECTED. li-route C188 ("τ* > 0 heuristically favoured, β > 1 cones possibly nonempty") is superseded. MUST-1463 empties every β ≠ 1 cone for any real weights, so PBAP_β fails for all β > 1. Under RH this forces the odd blind margin τ* = inf A/|pole| (pole < 0) = 0, and τ* > 0 would imply ¬RH. The twin card's "κ > d open" is closed by MUST-1477.
- 2026-10-15 (row 1218): route-TT row 422's logged Lean target (β < 1 cones empty, hypothesis-free) is already done by MUST-1463 (`eq_one_of_weilPositiveAt`), with no Ξ-decay input. Even-sector uniqueness (C1218) is open; it is likely driven by vertical growth/large values rather than null tests.
- 2026-10-15 (opus loop rows 1222–1224, MUST-1493/1494/1495): **RH ⟺ PBAP_even is now PROVED [L]**, closing the "converse OPEN" of row 1213.
  - Statements (`RHTower/EvenSectorFullPositivity`): `weilPositiveEvenAt_one_iff` (the even Weil cone is {Λ} under RH, ∅ otherwise) and `riemannHypothesis_iff_primeBlindPositiveEvenAt`.
  - The even TMP is not needed. In ρ² = r² + 2, even positivity gives one spectral measure ν_S (S = sech(z/2)) on the real λ-line (`EvenSectorSechRepresentation`).
  - The ordinary shifted-Gamma family still kills it on ρ² ≤ 2 (`EvenSectorTwistedArcNull`), because on the ρ-line only |y| ≤ √2 < 3/2 occurs, where Σ_j w_j p_j(y) > 0 (MUST-1488).
  - The negative values at 5/2 ≤ y found in row 1213′ lie outside the reachable range.
  - Consequence for this atlas: the existence problem may be posed on the even cone only. Its dual measures may a priori sit anywhere on the real λ-line, including exceptional λ < 1/4, and are then forced onto λ > 1/4.
- 2026-10-15 — route-tt rows 481–493 (user: Gordian knot / what is missing):
  - −M is an exact Hodge-index form: pole plane = hyperbolic plane spanned by Φ, Φ′ ⊂ rad(W) with M(aΦ + bΦ′) = −a²/2 + b²/8; nonneg tests = effective cone; {C = 0} = Φ^{⊥_M}; V₀ = pole-free tests = (∂² − ¼)(tests) and M = W|_{V₀} ⊕ H, so ind₋M = ind₋W + 1 = 2k + 1.
  - L482: Riemann–Roch axioms degenerate to homogeneity in the analytic setting; the missing object is an independently defined nonnegative expression for M on V₀ (or {C = 0}).
  - L483 (Gram rigidity): Φ⋆(tests) ⊂ rad(W) unconditionally, so every exact Gram of M on the hyperplane has vectors spectrally supported on the zeros; no zero-free Gram exists (explains law 4).
  - [P] exact Φ-smoothed PNT: K_M ⋆ Φ = −cosh(x/2), i.e. Σ_n Λ(n)n^{−½}[Φ(x−log n) + Φ(x+log n)] = (A⋆Φ)(x) + cosh(x/2) (the Doob mass identity; the opus lane's `WeilPhiDoobPrimeAtoms` has the ingredients).
  - L488: Krein window extensions of K_W are indeterminate (Beurling–Malliavin), finite window data never pin the zeros. L491: in the Doob frame no pointwise kernel domination holds in d* ≤ |u−u′| < log 2.
  - [L] `WeilMarkovOnePoleHyperplane`: RH ⟺ M ≥ 0 on {∫F e^{−x/2} = 0} (either single pole hyperplane).
  - Killed: positivity-preserving flows to K_W, Lee–Yang via BPY, Krein–de Branges Hamiltonian (circular), Euler-local Gram (symbol identity Σ_p log p(P_p − 1) = Ω off zeros; corpus `positiveEulerDilationOperator`), Lefschetz induction, dilation calculus, reflection positivity.
- 2026-10-15 — route-tt rows 503–504 [L] `WeilMarkovOddSectorTrivialZeroSquares`: for f supported in [ε, ∞), M(f − f̃) = 2M(f) + 2Σ_{k≥0}(∫f e^{−(2k+½)x})² + 2Σ_n Λ(n)n^{−½}(f⋆f)(log n). The reflected archimedean kernel of the odd sector is the sum of squares of the Mellin transform at the TRIVIAL zeros; the reflected prime atoms are the product pairing (≥ 0 for f ≥ 0). RH ⟹ M(f) + Σ_k f̃(−2k)² + Π(f) ≥ 0 on half-line tests [L]; converse by H¹-continuity [P]. On atomic tests the per-prime bracket is indefinite (no local completion of squares).
- 2026-10-15 — route-tt rows 505–515: [L] even counterpart M(f + f̃) = 2M(f) − 2Σ_k f̃(−2k)² − 2Π(f) and the two-sided law |Σ_k f̃(−2k)² + Π(f)| ≤ M(f) under RH for half-line tests with vanishing cosh-moment; [L] `W_reflect_re_eq`: the holomorphic zero sum Re Σ_ρ m_ρ f̂(γ_ρ)² = ℓ₀² + ℓ₁² − Π(f) − Σ_k f̃(−2k)² is archimedean-free (pairing of K_W with f⋆f); RH ⟺ |holomorphic| ≤ |Hermitian| zero sum. Laws: L507 resolution (RH content at resolution ≍ 1/γ; hyper-narrow atomic tests archimedean-dominated), L508 growth (positivity = temperedness of the Φ-mean-periodic K_W; the one negative square is the subtracted non-tempered pole exponential), L511 (Φ-balance is eigenvalue 0, no maximum principle; Landau one-sided reduction = wall 1), de Branges shift family E_h = ξ(½+h−iz) HB ⟺ zero-free beyond ½+h, damped forms W_σ ⟺ same ladder.
- 2026-10-15 — route-tt rows 527–528 [L] `WeilMarkovFarOutNonnegativeOddPositivity`: correction to the resolution law for the M-form — nonnegative half-line tests do not detect off-line zeros through M (the pole square 4S_f² ≍ e^{x₀}(∫f)² dominates any e^{(2β−1)x₀} amplification; witnesses of ¬RH need a near-vanishing sinh-moment, i.e. sign changes). Unconditional positive cone: f ≥ h > 0 on its support [x₀−1, x₀+1] with ∫f² ≤ B ⇒ M(f − f̃) > 0 for x₀ ≥ X₀(h, B); mechanism = PNT window growth of the product pairing Π(f) ≥ e^{−(x₀+¼)}h²(ψ(e^{2x₀+½}) − ψ(e^{2x₀−½})) against the O(∫f²) archimedean mass and short-lag ratio pairing (lags ≤ 2 ⇒ n ≤ 7). The one negative square of M lives on sign-changing tests with small S_f.
