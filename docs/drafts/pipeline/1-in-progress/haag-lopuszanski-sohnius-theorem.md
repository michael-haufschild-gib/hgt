# Haag–Łopuszański–Sohnius theorem (unconditional Lean classification)

- **ID:** hls-classification
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** goal directive 2026-08-21 (user)
- **Statement:** Every ℤ₂-graded extension of a Coleman–Mandula even algebra
  (Lorentz ⊕ translations ⊕ internal) by a finite-dimensional odd part carrying a
  positive-definite state form is, as a Lie superalgebra, the super-Poincaré algebra:
  the odd part is `N` Weyl pairs `(Q^I_α, Q̄^I_α̇)` plus Lorentz scalars,
  `{Q^I_α, Q̄^J_β̇} = 2 δ^{IJ} σ^μ_{αβ̇} P_μ`, `{Q^I_α, Q^J_β} = ε_{αβ} Z^{IJ}` with
  `Z` antisymmetric and central, and `[P_μ, Q^I_α] = 0`.

## Goal
Give the corpus an unconditional Lean 4 proof of the HLS classification.  Mathlib has
no Lie-superalgebra, no super-Poincaré, and no HLS content (verified 2026-08-21).
The existing corpus files `HLSKinematics`, `HLSPhysicalAssumptions`, `HLSFockAlgebra`,
`HLSScattering` supply kinematics and physical-assumption interfaces but contain **no
classification theorem**; this card supplies it.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: complete paper proof, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `haag_lopuszanski_sohnius`, build green, axiom audit PASS
- [ ] 3 → 4  publication-ready

## Approach (the weight-theoretic route — no Weyl complete reducibility needed)
Complexified Lorentz = `sl₂ ⊕ sl₂` with Cartan pair `(h, h̄)`.  Even part in the
spinorial basis: `sl₂ ⊕ sl₂ ⊕ P_{αα̇} ⊕ 𝔅`.  Its joint `(h,h̄)`-weights are
`(0,0), (±2,0), (0,±2), (±1,±1)`; in particular its **diagonal** weights `(c,c)` are
only `c ∈ {-1,0,1}`.

1. `star`-positivity: `Q` a joint generalized weight vector of weight `(a,b)` ⟹ `Q★`
   has weight `(b,a)` ⟹ `{Q, Q★}` has weight `(a+b, a+b)` and is nonzero, so
   `a+b ∈ {-1,0,1}`.
2. Raising `e` shifts `(a,b) ↦ (a+2,b)`; so `a+b ∈ {0,1} ⟹ e·Q = ē·Q = 0`, and
   lowering gives `a+b ∈ {-1,0} ⟹ f·Q = f̄·Q = 0`.
3. `a+b = 0` ⟹ killed by all four ⟹ `h = [e,f]` acts as `0` ⟹ weight `(0,0)`
   (Lorentz scalar sector).
4. `a+b = 1` ⟹ bi-primitive ⟹ `a,b ∈ ℕ` ⟹ `(1,0)` or `(0,1)`.  Symmetrically for `-1`.
   Hence the weights of the odd part lie in `{(0,0),(±1,0),(0,±1)}`.
5. On the `(1,0)` space, `e = ē = f̄ = 0` and `h = e∘f`; the `[h,f] = -2f` relation forces
   `h = 1` exactly, and `e, f` are mutually inverse bijections `(−1,0) ↔ (1,0)`.  So the
   spinor sector is `ℂ² ⊗ V₊`, i.e. `N = dim V₊` Weyl supercharges.  `star` matches the
   undotted and dotted sectors, so both have dimension `N`.
6. Weight bookkeeping + equivariance gives `{Q,Q̄} ∈ P`-sector, `{Q,Q} ∈ M ⊕ 𝔅`.
7. `[P,Q]` lands in the barred sector; the `[P,P] = 0` Jacobi identity plus positivity
   kills the coefficient, giving `[P_μ,Q^I_α] = 0`; then `[P,{Q,Q}] = 0` kills the `M`
   component of `{Q,Q}`, leaving `{Q^I_α,Q^J_β} = ε_{αβ} Z^{IJ}` with `Z` internal,
   antisymmetric and (odd–odd–odd Jacobi) central.
8. Positivity of the state functional on the `P`-sector makes the coefficient matrix
   `a^{IJ}` positive definite, so a `GL(N)` change of supercharge basis normalizes it to
   `2 δ^{IJ}`.
9. Physical layer: a Lorentz-scalar odd generator would connect a boson and a fermion of
   equal mass and equal spin, contradicting `HLSOneParticleData.spin_statistics`.  So the
   scalar sector vanishes in a physical HLS system.

Non-vacuity: build the `N = 1` super-Poincaré algebra as an explicit model of the input
structure (memory: `check-hypotheses-have-models`).

## Lean modules landed
- `HTGeometry/HLSEvenAlgebra.lean` — the even Coleman–Mandula algebra `𝔤₀` in spinorial
  coordinates, its bracket, Jacobi identity, Cartan pair `(adL, adR)`, and the
  diagonal-weight rigidity theorem `hlsEven_joint_weight_eq_zero`.
- `HTGeometry/HLSGradedSymmetry.lean` — the real-form conjugation `hlsEvenConj`, the
  `HLSGradedSymmetry` input structure (graded Jacobi + star + state positivity), the
  `𝔰𝔩₂ ⊕ 𝔰𝔩₂` action on the odd part, and `hlsGenEigen_bilinear` (weights add along an
  equivariant bilinear map).
- `HTGeometry/HLSOddWeights.lean` — `wt_constraint` (positivity confines `a + b̄` to
  `{0, ±1}`), `wt_weights` (the odd weights are exactly `(0,0), (±1,0), (0,±1)`),
  the exact Cartan eigenvalues on each sector, the `eL/fL` sector isomorphism, and
  `wt_sectors_eq_top`.
- `HTGeometry/HLSMomentumAction.lean` — `act_mom_eq_zero`: `[P_μ, Q] = 0`, unconditional.

## Log
- 2026-08-21 — created; corpus audited (no existing classification theorem), mathlib
  audited (no supersymmetry content at all).  Weight route fixed.
- 2026-08-21 — spin-½ forcing and `[P, Q] = 0` proved in Lean; four modules wired into
  the `HTGeometry` umbrella.  Remaining: `{Q, Q̄} = 2 δ σ P` normalization, `{Q,Q} = ε Z`,
  centrality of `Z`, the capstone statement, and the non-vacuity model.
