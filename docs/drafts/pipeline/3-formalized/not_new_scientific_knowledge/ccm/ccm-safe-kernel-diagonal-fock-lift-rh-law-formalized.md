# The CCM half-unit covariance is a canonical diagonal Fock lift — formalized closure

- **ID:** `ccm-safe-kernel-diagonal-fock-lift-rh-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-safe-kernel-diagonal-fock-lift-rh-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-EQUIVALENT TARGET]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCM.CCMDiagonalFockLift` (new)
- `GaloisForLFunctions.RHTower.CCM.CCMHalfUnitCauchySeam` (new in the parent card)
- `GaloisForLFunctions.HTGeometry.PrimeLogHerglotz`,
  `GaloisForLFunctions.HTGeometry.PrimeLogCauchySeamRank` — the formal prime-log transport wall
  `(15b)`, `(15c)`, pre-existing.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)`, `(2)`, `(3)` | `safeKernel`, `cauchyKernel`, `fockKernel`, `kernelMatrix` | the three kernels and their Gram matrices |
| `(5)` | `cauchy_quadratic_form` | the exponential feature realization `∑ αᵢαⱼ/(xᵢ+xⱼ) = ∫₀^∞ (∑ αᵢe^{−xᵢt})² dt` |
| `(2)`, positivity | `posSemidef_cauchyMatrix` | the Cauchy kernel is PSD *because* it is that Gram matrix |
| `(3)` | `fockMatrix_eq_hadamard`, `posSemidef_fockMatrix` | `D = A ∘ C` and the Schur product theorem |
| `(4)`, `(9)` | `rhMatrix_eq_sub`, `rhKernel_eq_safe_sub_fock` | `J_RH = A − D` exactly |
| `(10)`–`(12)` | `defect_form_eq` | the defect form of the diagonal lift is the `J_RH` form |
| `(7)` | `contractive_iff_rhForm_nonneg` | contractivity on a finite kernel core ⟺ nonnegativity of the RH form |
| `(8)` | `defect_form_eq` | the two forms being equal, their negative indices coincide |
| `(15b)`, `(15c)` | `PrimeLogHerglotz`, `PrimeLogCauchySeamRank` (pre-existing) | the formal prime-log transport wall |

## Axioms

`#print axioms` on all ten declarations of the new module returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- Positive semidefiniteness of the safe kernel `A` — the de Branges–Rovnyak positive-real theorem,
  which appears as an explicit hypothesis of `posSemidef_fockMatrix`.
- The equivalence `(13)` `J_RH ⪰ 0 ⟺ RH`, imported from the infinitesimal Euler-ray index card.
- The analytic RKHS completion and the density argument extending the lift from the algebraic
  kernel span; the Lean statements are at the level of finite kernel cores, which is where the
  card's own proof lives.
- The card's open gates: convergence of the finite Gauss/Sonin degree-two columns to `T₀`,
  contractivity of the limiting lift, and RH.

## Verification performed

- `lake env lean` on the new module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCM.CCMDiagonalFockLift`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.
