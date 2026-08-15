# The infinitesimal CCM half-unit seam is an indefinite Cauchy Schur ratio — formalized closure

- **ID:** `ccm-infinitesimal-half-unit-cauchy-seam-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-infinitesimal-half-unit-cauchy-seam-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

`GaloisForLFunctions.RHTower.CCMHalfUnitCauchySeam` (new), over the pre-existing
`RHTower.re_inv_pos_of_re_pos` of `GammaSewnMobiusXiWardCofinalBoundaryLift`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(2)`, `(7)` | `re_hadamardPair_pos` | each centred Hadamard pair has positive real part for `Re z > 1/2`; this is the card's own proof of `(2)` from `(7)` |
| `(3)` | `safeKernel` | the unconditional safe kernel |
| `(4)` | `rhKernel` | the RH kernel |
| `(5)` | `seamKernel`, `rhKernel_eq_safe_mul_seam` | the exact Schur factorization `J_RH = J_safe ∘ H` |
| `(6)` | `det_seam_two_point` | the exact two-point seam minor `−(x−y)²(2x+2y−1)/(4xy(x+y)²)` |
| `(6)`, sign | `det_seam_two_point_neg` | strictly negative for distinct `x, y > 1/2` |
| no scalar transport | `seamMatrix`, `det_seamMatrix`, `not_posSemidef_seamMatrix` | the seam matrix is not positive semidefinite, so no universal scalar Schur multiplier crosses the seam |
| diagonal Fock carrier | `fockKernel`, `rhKernel_eq_safe_sub_fock` | `J_RH = J_safe − D` exactly, with `D = J_safe/(x+y)` |
| Fock Gram factor | `integral_exp_ray` | `∫₀^∞ e^{−xt}e^{−yt} dt = 1/(x+y)`, so `D` is a Schur product with a positive kernel |

## Axioms

`#print axioms` on all eight declarations returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The Hadamard product representation `(7)` of `ξ′/ξ`, and the classical zero strip. Both are the
  card's declared parents; what the card *proves* from them — that each pair term is
  positive-real-part beyond the seam — is formalized.
- The de Branges–Rovnyak positive-real kernel theorem, i.e. positive semidefiniteness of `(9)` and
  hence of `J_safe`. Cited parent.
- The card's own open gates: contractivity of the source realization of the Fock lift, `J_RH ⪰ 0`,
  and RH.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMHalfUnitCauchySeam`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.
