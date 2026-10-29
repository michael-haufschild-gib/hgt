# Cancelled Robin calculus for overlapping atoms

Status: all three modules formalized, individually checked, and wired.

## Actual mixed expansion

For actual `C²` functions `f,g` supported in one interval `[0,w]`, with
`0<w<=1`, the retained mixed Lévy integral satisfies

```
abs(int levyMixed(f,g)
  -(log(1/w)+archRobinConstant)*int f*g-mixedBumpRobin(f,g,w))
  <= exp(1/2)/4*w*(int f^2+int g^2).
```

The mixed finite part is the quarter difference of the Robin energies of
`f+g` and `-f+g`. Polarization retains the actual overlap mass in the leading
logarithmic term. Neither separation nor positive square mass is assumed.
The scalar Robin remainder and Lévy polarization are existing corpus inputs.

## Perturbation bounds

For compact `C²` profiles, `W>=0`, and a nonnegative Lipschitz bound `L` on
`f-g`, the exact inequalities are

```
abs(bumpRobin(f,W)-bumpRobin(g,W)) <= W*L*(L1(f)+L1(g)),
abs(mixedBumpRobin(f,shift_a f,W)-mixedBumpRobin(g,shift_a g,W))
  <= 2*W*L*(L1(f)+L1(g)).
```

The second bound is uniform in all real shifts `a`. Factoring the difference
of squared increments cancels `1/y` before integration; absolute masses
are invariant under translation.

Every fixed `C²` unit-interval profile produces `C>0` such that, throughout
`1<=c<=2`, its actual dilation difference has Lipschitz bound `C*(c-1)` and
absolute mass at most `6*C*(c-1)`. A bounded first derivative and a Lipschitz
first derivative supply the estimate. Outside a fixed compact interval both
derivative terms vanish. The mixed Robin change has a produced bound
`K*W*(c-1)` uniform in shifts, including the version divided by `c`.

## Lean closure

- `TheMixedRobinExpansionSurvivesActualOverlap.lean`: needed check3118, final check99690.
- `TheRobinFinitePartIsStableUnderLipschitzPerturbations.lean`: needed check70200, final check97156.
- `SmoothDilationHasASmallLipschitzDifference.lean`: final check72703.

All checks passed clean. Every printed capstone dependency list contains
only `propext`, `Classical.choice`, and `Quot.sound`. All three modules are
imported by the programme umbrella. No full or umbrella build was run.

## Boundary

These are scalar analytic estimates. The leading overlap Gram mass,
all pair sums, the literal prime correction, and both pole moments still
need one complete relative form comparison. No completed paper proof of
that comparison is claimed. The existing successor backlog records that
unproved extension; no new implementation is part of this closure.
