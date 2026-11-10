# Two-prime upper bounds and the inhomogeneous frequency

- **Stage:** 1-in-progress
- **Source:** review-0911 §11.4 and §11.6.

## Exact obstruction

`HeightsAtTheZerosOfTheSplineAreInPhase` chooses heights `2πM` and
approximates `M log p` and `M log q` by integers. The opposite sign for the
cubic spline requires prescribing the additional phase of the height
modulo `2π`. The corresponding continuous torus has frequencies
`(1, log p, log q)`; its dual forms are
`m + a log p + b log q`, with integer coefficients.

Replacing the constant frequency `1` by `log(-1)=iπ` changes these forms.
The report's three-logarithm substitution needs an exact normalization
identity before a standard integer-coefficient logarithm bound can apply.
The corpus's qualitative inhomogeneous Baker theorem proves independence
of `1` and algebraic logarithms; its effective prime-log theorem does not
contain the constant term.

## Required result

A quantitative lower bound for the actual dual forms, strong enough to
give an inhomogeneous hitting time compatible with the spline tower's
weight and window inequalities. Then construct the opposite-sign cubic
tower or prove that the upper bound forces attainment. Neither conclusion
follows from qualitative density alone.

The needed arithmetic statement is published: for fixed `p,q`,
`|m+a log p+b log q| ≥ c(2+|m|+|a|+|b|)^(-C)` outside the zero triple.
[Waldschmidt, Chapter 12, general case](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/LIL.pdf#page=105)
includes a constant term and gives this specialization. Its proof, rather
than the homogeneous prime-log theorem, remains to be formalized.

## Existing positive boundary

`exists_zeroConfig_finPrimes_bddBelow_nonattained` gives a cubic lower-side
counterexample for every finite prime set.
`exists_zeroConfig_finPrimes_bddAbove_nonattained_quartic` gives the
upper-side counterpart for the quartic spline. Both are unconditional;
the remaining issue is the cubic upper side.
