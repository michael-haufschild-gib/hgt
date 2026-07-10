# Real-zero-free nonreal mobility in the gamma-completed cell

- **ID:** gamma-cell-real-zero-free-nonreal-mobility
- **Stage:** 3-formalized
- **Type:** POSITIVE STRUCTURE THEOREM (Lean) / selector-boundary theorem
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

The class is closed under the displayed positive reciprocal-quartic action:

`GammaFECell f -> GammaFECell (f * dzoQuartic)`.

Thus the useful positive object is the action orbit, not merely a failed implication.  The next
constraint must distinguish the primitive all-prime source from its degree-zero multiplicative
decorations; real-axis zero-freeness does not make that distinction.

## Lean certificate

- `dzoQuartic_mem_gammaFECell`
- `gammaFECell_mul_dzoQuartic`
- `zetaDzoQuartic_mem_gammaFECell`
- `zetaDzoQuartic_nonreal_offline_strip_zero`
- `zetaDzoQuartic_real_strip_ne_zero`
- `gammaFECell_real_zero_free_nonreal_strip_mobility`

The exact module build passes.  The listed declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Research consequence

The positive replacement for the no-go is a construction problem:

> Find a source-native primitive normalization that is fixed by the exact Euler data but is not
> preserved by multiplication with nonconstant degree-zero reciprocal factors.

A condition invariant under the degree-zero action cannot see the distinction between zeta and the
displayed real-zero-free nonreal-mobile member.  A condition that merely restates the coefficients
of zeta is tautological.  The live target lies between these extremes.
