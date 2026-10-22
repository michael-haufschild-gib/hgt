# The causal Möbius quotient is the Euler-region restriction of the shifted-Xi Pick carrier — formalized closure

- **ID:** `ccm-causal-pick-affine-conjugacy-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-causal-pick-affine-conjugacy-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

`GaloisForLFunctions.RHTower.CCM.CCMCausalPickAffineConjugacy` (new), over the Pick-cluster modules
`CCMEulerRayLoewner`, `CCMEulerRayLogDerivativeIndex`, `CCMDiagonalFockLift`,
`CCMHalfUnitCauchySeam`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(9)` | `affineEmbed`, `neg_I_mul_affineEmbed` | `−i j_ω(z) = 1/2 + ω + z` |
| `(1)`, `(8)` | `causalPhi`, `shiftedXiQuotient` | the two quotients |
| `(11)` | `shiftedXiQuotient_comp_affineEmbed` | the affine embedding identifies them |
| `(12)` | `affineEmbed_cauchy_denominator` | `i/(j_ω z − conj(j_ω v)) = 1/(1+2ω+z+conj v)` |
| `(13)` | `causalPickKernel`, `schur_pullback_eq_causalPickKernel` | the pulled-back Schur kernel is the causal Pick kernel |
| `(7)` | `causalPhi_eq_explicit` | the explicit archimedean/Euler factorization of `Φ_ω` |
| `(3)`, `(5)` | `conjugacyScalar`, `conjugacyScalar_mul_causalPhi` | the scalar conjugacy identity |
| `(20)` | `causalPhi_zero_shift`, `conjugacyScalar_zero_shift`, `causalPickKernel_zero_shift` | the critical degeneration to `Φ₀ = 1`, `A₀ = 1/(1+z)`, `K₀ = 0` |

## Axioms

`#print axioms` on all nine declarations returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The completed-zeta formula `(6)`, which appears as the explicit hypothesis `hXi`.
- The signed-Möbius causal transform `(2)` itself.
- The generalized Schur index theorem and locality of negative squares behind `(14)`, and the
  Schur-multiplier property of `τ_ω` in `(16)`.
- The card's open gates: complete Pick positivity `(17)` from the pointed source construction, its
  cofinal retention as `ω ↓ 0`, and RH.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCM.CCMCausalPickAffineConjugacy`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.
