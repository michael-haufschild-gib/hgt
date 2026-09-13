# HB on-line clock: spectral assembly on the modular surface (input (ii)(b))

- **ID:** HB-SPEC-001
- **Stage:** 0-backlog
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

## Log
- 2026-09-13 — created in 0-backlog after passes 26–30 closed every other input of the on-line sign law; the
  reduction to steps 1–6 (no spectral gap, no discreteness, no Eisenstein Plancherel) is the scoping result.
- 2026-09-13 — step 5 discharged in abstract form: `HTGeometry/SelfAdjointFunctionalCalculusLowerBound.re_inner_cfc_self_ge` (bounded self-adjoint `A`, `c ≤ g` on the spectrum ⇒ `c‖f‖² ≤ Re⟪g(A)f,f⟫`); with `A = (1−Δ)⁻¹` no spectral measure is needed. Remaining: steps 1–3 and 6.
