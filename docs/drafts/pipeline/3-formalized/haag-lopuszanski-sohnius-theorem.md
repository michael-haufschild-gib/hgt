# Haag–Łopuszański–Sohnius theorem (unconditional Lean classification)

- **ID:** hls-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** goal directive 2026-08-21 (user)
- **Statement:** Every ℤ₂-graded extension of a Coleman–Mandula even algebra
  (Lorentz ⊕ translations ⊕ internal) by a finite-dimensional odd part carrying a real form and
  a positive state functional is, as a Lie superalgebra, the super-Poincaré algebra: the odd
  part is Lorentz scalars plus `N` Weyl pairs `(Q^I_α, Q̄^I_α̇)`,
  `{Q^I_α, Q̄^J_β̇} = 2 δ^{IJ} P_{αβ̇}`, `{Q^I_α, Q^J_β} = ε_{αβ} Z^{IJ}` with `Z` antisymmetric
  and central, and `[P_μ, Q^I_α] = 0`.

## Goal
Give the corpus an unconditional Lean 4 proof of the HLS classification.  Mathlib has no
Lie-superalgebra, no super-Poincaré and no HLS content whatsoever (verified 2026-08-21); the
pre-existing corpus files `HLSKinematics`, `HLSPhysicalAssumptions`, `HLSFockAlgebra`,
`HLSScattering` supply kinematics and assumption interfaces but contain **no classification
theorem**.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: complete proof, no open dependency
- [x] 2 → 3  formalized: `haag_lopuszanski_sohnius`, `lake build` green,
      `#print axioms` = `[propext, Classical.choice, Quot.sound]` only
- [ ] 3 → 4  publication-ready

## Capstone
`GaloisForLFunctions.HTGeometry.HLSGradedSymmetry.haag_lopuszanski_sohnius`
(`formal/GaloisForLFunctions/HTGeometry/HLSTheorem.lean`).

## Lean modules
| Module | Content |
|---|---|
| `HTGeometry/HLSEvenAlgebra.lean` | the even Coleman–Mandula algebra `𝔤₀ = 𝔰𝔩₂ ⊕ 𝔰𝔩₂ ⊕ P ⊕ 𝔅` in spinorial coordinates; bracket, antisymmetry, Jacobi; Cartan pair `adL, adR`; `hlsEven_joint_weight_eq_zero` |
| `HTGeometry/HLSGradedSymmetry.lean` | real-form conjugation `hlsEvenConj`; the `HLSGradedSymmetry` input structure (graded Jacobi + star + state positivity + spectrum condition); the `𝔰𝔩₂ ⊕ 𝔰𝔩₂` action on the odd part; `hlsGenEigen_bilinear` |
| `HTGeometry/HLSOddWeights.lean` | `wt_constraint`, `wt_weights` (odd weights `= (0,0), (±1,0), (0,±1)`), exact Cartan eigenvalues per sector, the `eL/fL` sector isomorphism, `wt_sectors_eq_top` |
| `HTGeometry/HLSMomentumAction.lean` | `act_mom_eq_zero`: `[P_μ, Q] = 0` |
| `HTGeometry/HLSBrackets.lean` | `br_pos_pos_eq_zero`, `br_neg_neg_eq_zero`, `br_pos_neg_is_int`, `br_central_antisymm`, `act_br_pos_neg_eq_zero` (centrality), `central_charge_commute`, `central_charge_ideal`, `br_pos_dotPos_mom` |
| `HTGeometry/HLSSuperchargeBasis.lean` | `hlsExistsOrthonormal`; the coefficient form `hlsBeta`, its hermiticity and positivity; `exists_supercharge_basis` |
| `HTGeometry/HLSTheorem.lean` | `haag_lopuszanski_sohnius`; `supercharge_linearIndependent` |
| `HTGeometry/HLSScalarExclusion.lean` | `act_poincare_zero_on_scalar`; `hls_spin_statistics_forbids_statistics_flip` |
| `HTGeometry/HLSWitness.lean` | the `N = 1` super-Poincaré model `hlsWitness`, `hlsGradedSymmetry_nonempty`, `hlsWitness_haag_lopuszanski_sohnius` (non-vacuity) |

## Proof architecture (the weight route — no Weyl complete reducibility)
Complexified Lorentz `= 𝔰𝔩₂ ⊕ 𝔰𝔩₂`, Cartan pair `(h, h̄)`.  The joint `(h,h̄)`-weights of `𝔤₀`
are `(0,0), (±2,0), (0,±2), (±1,±1)`.

1. **Positivity confines the odd weights.**  For a joint generalized weight vector `Q` of weight
   `(a,b)`, `Q★` has weight `(b̄, ā)` and `{Q, Q★} ≠ 0`, so `a + b̄ ∈ {0, ±1}`.
2. **Raising/lowering.**  `a + b̄ ∈ {0,1} ⟹ e·Q = ē·Q = 0`; `∈ {−1,0} ⟹ f·Q = f̄·Q = 0`.
3. `a + b̄ = 0` ⟹ killed by all four ⟹ `h = [e,f]` acts as `0` ⟹ weight `(0,0)`.
4. `a + b̄ = ±1` ⟹ the `[h,f] = −2f` (resp. `[h,e] = 2e`) relation forces `h = ±1` **exactly**,
   giving `(±1,0)` or `(0,±1)`.  Hence the odd part is scalars `⊕` Weyl spinors, and `e, f` are
   mutually inverse bijections between the two undotted sectors.
5. **`[P,Q] = 0`.**  With `T = [P_{10̇}, ·]` on the highest-weight sector and `U = ★∘T`:
   `[P,P] = 0` gives `U² = 0`; the graded Jacobi identity applied to the translation `{Q, Q★}`
   gives `{U Q, Q} = 0`; feeding both into the Jacobi identity for `{Q, U Q}` yields
   `{T Q, (T Q)★} = 0`, hence `T Q = 0` by positivity.  Lowering operators and conjugation
   propagate this to all sectors.
6. **Bracket normal form.**  `[P,Q] = 0` kills the Lorentz component of `{Q,Q}`, leaving an
   internal `Z`; the `f`-Jacobi identity makes `Z` antisymmetric; the Jacobi identity together
   with nondegeneracy of the positive form makes `Z` central and abelian, spanning an ideal of
   the internal algebra.
7. **Normalization.**  The coefficient form of `{Q, Q̄}` is positive definite Hermitian; its
   orthonormal basis gives `{Q^I_α, Q̄^J_β̇} = 2 δ^{IJ} P_{αβ̇}` and `N` linearly independent
   supercharges.
8. **Scalar sector.**  Lorentz-scalar odd generators commute with the whole Poincaré algebra, so
   they would connect one-particle states of equal mass and spin but opposite statistics —
   impossible by `HLSOneParticleData.spin_statistics`.

## Log
- 2026-08-21 — created; corpus and mathlib audited; weight route fixed.
- 2026-08-21 — spin-½ forcing and `[P,Q] = 0` proved.
- 2026-08-21 — bracket normal form, centrality, orthonormal supercharge basis, capstone,
  `N = 1` non-vacuity witness, scalar-sector exclusion.  Nine modules wired into the
  `HTGeometry` umbrella; axiom audit clean.  Promoted to stage 3.
