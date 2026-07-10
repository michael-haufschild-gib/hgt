# Real-zero-free nonreal mobility in the gamma-completed cell

- **ID:** gamma-cell-real-zero-free-nonreal-mobility
- **Stage:** 3-formalized
- **Type:** POSITIVE STRUCTURE THEOREM (Lean) / exact actor-classification theorem
- **Scientific status:** `[BRIDGE]`, not new scientific knowledge.  The exact conjunction is a
  useful sharpening, but the mechanism is the routine action of a reciprocal degree-zero
  Dirichlet polynomial on a gamma-completed Dirichlet series.
- **Lean:** `formal/GaloisForLFunctions/RHTower/GammaCellNonrealMobility.lean`.

## Positive statement

Define `RealZeroFreeNonrealStripMobility C` to mean that the class `C` contains a member `f` and a
point `rho` such that:

- `f` has no zero at any real point of the open critical strip;
- `rho` is nonreal and strictly inside the open strip;
- `f rho = 0` and `Re rho != 1/2`.

Then

`RealZeroFreeNonrealStripMobility GammaFECell`.

The witness is

`zetaDzoQuartic(s) = riemannZeta(s) * dzoQuartic(s)`,

where

`dzoQuartic(s) = 1 + 40*16^(-2s) + 256*16^(-4s)`.

The explicit mobile zero is

`rho = 5/8 - i*pi/(8 log 2)`.

## What is structurally realized

The theorem combines, in one member:

1. the genuine all-prime zeta factor;
2. integer-valued multiplicative Dirichlet coefficients;
3. a strip-nonvanishing gamma completion and exact self-dual functional equation;
4. no zero anywhere on the real open strip;
5. an explicit nonreal off-line strip zero.

More generally, the nonzero integral multiplicative degree-zero class acts on `GammaFECell`:

`GammaFECell f ∧ IntegralMultiplicativeFEClass g ∧ (∃ s, g s ≠ 0)`

`-> GammaFECell (f * g)`.

This is an exact actor classification: an integral multiplicative degree-zero member acts on every
gamma-cell member if and only if it is nonzero somewhere.  The displayed reciprocal quartic is one
explicit actor.

Thus the useful positive object is the action orbit.  The next constraint is a section or invariant
that singles out the primitive all-prime source inside that orbit.  Real-axis zero-freeness is
constant on too much of the orbit to supply that section.

## Lean certificate

- `dzoQuartic_mem_gammaFECell`
- `gammaFECell_exists_ne_zero`
- `gammaFECell_mul_integralFEClass_of_exists_ne_zero`
- `integralFEClass_acts_on_gammaFECell_iff`
- `gammaFECell_mul_dzoQuartic`
- `zetaDzoQuartic_mem_gammaFECell`
- `zetaDzoQuartic_nonreal_offline_strip_zero`
- `zetaDzoQuartic_real_strip_ne_zero`
- `gammaFECell_real_zero_free_nonreal_strip_mobility`

The exact module build passes.  The listed declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Research consequence

The actor classification exposes a positive construction problem:

> Construct a source-native primitive section, fixed by the exact Euler data, whose value changes
> under every nonconstant degree-zero reciprocal actor.

The live constraint is transverse to the degree-zero action orbits and sensitive to source
primitiveness, while remaining strictly weaker than a restatement of zeta's coefficients.
