# Full detail payment with every non-first-prime mixed term

- **ID:** acs-joint-nonfirst-mixed-payment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** One fixed detail head leaves almost all coarse Gamma, a
  positive logarithmic detail reserve, and detail square mass after jointly
  paying the entire Haar Weil diagonal, Gamma mixing, and all mixed prime
  powers of exponent at least two.

## Exact source

Let `Q=fullDetailCoupledSourceForm q d X`,
`B₂=squarePrimeMixedSource q d X`, and
`Bodd=oddHigherPrimePowerMixedSource d q X`.
The proved bound gives, for every ε>0, some A≥1 such that d vanishing below A implies

`Q−B₂−Bodd ≥ (1−ε)Γg + (fullDetailPrimeGap/4)D + ∫h²`.

Use all even exponents in B₂ and only odd exponents at least three in Bodd.
Subtracting the all-higher-power source as well would count even exponents
at least four twice and would not represent the intended source.

## Proof

The existing full-detail theorem at ε/2 retains
`(1−ε/2)Γg+(fullDetailPrimeGap/2)D+∫h²`.
The square mixed-tail theorem and the odd higher-power tail theorem each
cost at most δΓF beyond fixed
heads. Take the maximum of the three heads, and use
`ΓF≤2Γg+8*haarGammaUpperConstant*D`.
With `δ=min(ε/8,fullDetailPrimeGap/(64*haarGammaUpperConstant))`, their
combined cost is at most `εΓg/2+fullDetailPrimeGap*D/4`. Positivity of both
energies justifies multiplying these coefficient inequalities. Subtract
the two signed terms using each term's absolute value, yielding the stated
lower bound. Applying this to the actual tail coefficients gives the
uniform tail formulation with no hypothesis on the original d.

For any finite family of such profiles, use the first A detail coefficients
as a linear readout into ℝ^A. At ε=1/2 the paid form is nonnegative on
its kernel. On a subspace where every nonzero vector has strictly negative
form, the readout is injective. Its dimension is therefore at most A,
uniformly over the family size, coefficients, and support horizon.

## Remaining source

Even after this joint payment, first-prime mixing, the coarse signed
residual, polar cross terms, and finite heads remain. No second use of the
whole-square coercivity reserve is permitted.

## Dependencies

- `TheFullDetailSourceRetainsCoarseGamma.lean`: existing direct check passed.
- `TheMixedSquareSourceHasUniformSmallTails.lean`: direct check passed.
- `OddHigherPrimePowerMixedTailsAreGammaSmall.lean`: existing corpus result.

## Lean verification

Module:
`ArithmeticIndexDescent/EveryMixedExponentAboveOneLeavesACoarseReserve.lean`.

Declarations:

- `fullDetailNonfirstMixedSourceForm`
- `exists_fullDetailNonfirstMixed_coarse_reserve`
- `exists_fullDetailNonfirstMixed_uniform_tail`
- `exists_uniform_fullDetailNonfirstMixed_negative_dimension`

Direct check passed, without diagnostics:

```
lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/EveryMixedExponentAboveOneLeavesACoarseReserve.lean
```

No web search, novelty checks, numerical experiments or axiom checks.
