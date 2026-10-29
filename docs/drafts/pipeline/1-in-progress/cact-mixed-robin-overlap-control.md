# Cancelled Robin calculus for overlapping atoms

## Target

For two actual smooth functions `f,g` supported in one interval `[0,w]`,
`0<w<=1`, retain the mixed Lévy integral and prove

```
abs(int levyMixed(f,g)
  -(log(1/w)+archRobinConstant)*int f*g-mixedBumpRobin(f,g,w))
  <= exp(1/2)/4*w*(int f^2+int g^2).
```

The polarized Robin term is the quarter difference of the Robin energies of
`f+g` and `-f+g`. The actual overlap mass remains in the leading logarithmic
term. There is no separation or positive-mass assumption.

## Role

This is source calculus needed for genuine overlap, not a positivity theorem.
The scalar Robin remainder and Lévy polarization already exist in the corpus.
Their mixed consequence keeps the cancellation that would be lost by splitting
an overlapping pair into divergent cross integrals. At a common window of
length `O(1/N)`, its normalized remainder is `O(1/N)`.

The further target is the quantitative finite-part perturbation law

```
abs(bumpRobin(f,W)-bumpRobin(g,W)) <= W*Lip(f-g)*(L1(f)+L1(g)),
abs(mixedBumpRobin(f,shift_a f,W)-mixedBumpRobin(g,shift_a g,W))
  <= 2*W*Lip(f-g)*(L1(f)+L1(g)).
```

The second estimate is uniform in every displacement `a`. Factoring squared
increments cancels `1/y` before integration. The actual-dilation draft supplies
`Lip(phi(./c)-phi)=O(c-1)` and an absolute mass bound `O(c-1)` from the fixed
smooth profile. A bounded first derivative and a Lipschitz first derivative
give the derivative-difference estimate. Outside a fixed compact interval both
derivative terms vanish. The normalized mixed finite part retains this modulus
after division by `c`.
Adjacent pairs must also pay their leading overlap Gram mass using the actual
prime defect. Distant pairs and pole moments have separate width comparisons.

## Inputs and status

Searches180,183,187; actual source read in SSHA/TheRobinConstantOfAnAtom and
SSHA/WeilsFormIsContinuousInTheLevyNorm. Search192 found no direct matching
Robin perturbation theorem in the displayed leads. Both
`TheMixedRobinExpansionSurvivesActualOverlap.lean` and
`TheRobinFinitePartIsStableUnderLipschitzPerturbations.lean` are drafted and
unchecked. `SmoothDilationHasASmallLipschitzDifference.lean` drafts the actual
profile producer and normalized finite-part comparison. The three form an
import chain. No result is claimed until Lean and the final individual audit
pass.
