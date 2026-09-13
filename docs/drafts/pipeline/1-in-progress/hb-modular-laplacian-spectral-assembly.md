# HB on-line clock: spectral assembly on the modular surface (input (ii)(b))

- **ID:** HB-SPEC-001
- **Stage:** 1-in-progress (assembly inequality in Lean; closability and the source element open)
- **Type:** THEOREM (paper) — Lean blocked by missing infrastructure
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
- [ ] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
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
