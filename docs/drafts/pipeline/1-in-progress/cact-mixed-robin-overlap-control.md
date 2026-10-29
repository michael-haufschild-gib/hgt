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

The further missing input is uniform control of the polarized finite part as
the width ratio changes. Adjacent pairs must also pay their leading overlap
Gram mass using the actual prime defect. Distant pairs and pole moments have
separate width comparisons.

## Inputs and status

Searches180,183,187; actual source read in SSHA/TheRobinConstantOfAnAtom and
SSHA/WeilsFormIsContinuousInTheLevyNorm. Draft formalization underway; no result
claimed until Lean and the final individual audit pass.
