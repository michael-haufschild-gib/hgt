# Finite Hecke weights give unit-periodic ideal theta

- **ID:** finite-hecke-weights-give-unit-periodic-ideal-theta
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke and class-field programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** The actual finite residue character, extended by zero on nonunits, times the actual real-parity Gaussian gives an absolutely convergent integral-ideal theta sum invariant under translation by global-unit place logarithms.

## Exact target

Let `ψ` be a ray class character of modulus `𝔪`. Extend its finite component to
`𝓞 K / 𝔪.fin` using `MulChar.ofUnitHom`. At each real place in `𝔪.inf`, use the
already defined parity `heckeParity`; all remaining coordinates have parity zero.
For an integral ideal `b`, sum the resulting finite weight times the scaled
parity Gaussian over `a ∈ b`. Prove absolute convergence for every positive
Gaussian parameter and invariance under `y ↦ y + log |u|` for every global unit.
No extra compatibility condition may be assumed: it must follow from the actual
ray class character and the existing global-unit relation.

## Proof route and dependency audit

1. `MulChar.ofUnitHom` is defined even for the trivial residue ring; do not assume
   that zero is a nonunit when `𝔪.fin = ⊤`. Agreement on units is
   `MulChar.ofUnitHom_coe`.
2. The already imported Hecke theorem `norm_char_eq_one` bounds values on units;
   the extension is zero on nonunits. The corpus also has the general theorem
   `RHTower.norm_mulChar_apply_le_one`, but its separate analytic imports are
   unnecessary for this specialization.
3. `reduce_eq` identifies reduction of a global unit with its quotient image.
   `finite_character_mul_parities_globalUnit` proves cancellation with real signs.
4. At a real place, `exp(-log |σ(u)|) σ(u)` is its sign. Thus the parity
   monomial gains precisely the existing infinite sign character under
   `(y,a) ↦ (y + log |u|, u*a)`. The Gaussian norm is unchanged by
   `norm_sq_numberFieldPlaceScale_unit`.
5. The parity Gaussian's half-rate majorant and the proved actual fractional-ideal
   Gaussian convergence give absolute parity summability. Every integral ideal
   injects into the unit fractional ideal, so restriction gives convergence even
   for the zero ideal. The finite weight has norm at most one. Reindexing by
   multiplication by a unit gives theta periodicity.

## Status

In [HeckeIdealThetaIsUnitPeriodic.lean](../../../../formal/GaloisForLFunctions/HeckeLFunctions/HeckeIdealThetaIsUnitPeriodic.lean):

- `finiteHeckeWeight`, `integralHeckeWeight`, `reduce_globalUnit`
- `norm_finiteHeckeWeight_le_one`, `integralHeckeWeight_mul_parities_unit`
- `heckeCoordinateParity`, `heckeRealMonomial`, `parityMonomial_heckeCoordinateParity`
- `real_embedding_scaled_unit`, `heckeRealMonomial_unit`
- `summable_norm_parityGaussian_fractionalIdeal`, `summable_norm_parityGaussian_integralIdeal`
- `heckeThetaKernel`, `heckeThetaKernel_unit`, `summable_norm_heckeThetaKernel`
- `heckeIdealTheta`, `heckeIdealTheta_unit`

The complete scratch passes. Four transitive axiom audits (finite norm bound,
kernel invariance, absolute convergence, theta periodicity) use only `propext`,
`Classical.choice`, and `Quot.sound`. The final direct `lake --old env lean` source
audit passes without warnings. The module is wired into `HeckeLFunctions.lean`;
no umbrella was compiled. No proof limits were raised. The completed scratch
files are removed. The norm proof now reuses the already imported finite-group
character norm theorem; the final direct source audit passes again without
warnings after this dependency reduction. Its olean is built for the written
ideal-coset and affine-parity consumers.

The ideal theta is periodic for every real parameter; absolute convergence is
proved for every positive parameter. These statements concern actual ray-class
characters and actual ideals, with no assumed compatibility or analytic input.
Primitive residue-ring Gauss sums and unit-domain Mellin unfolding remain open
for the full Hecke functional equation.
