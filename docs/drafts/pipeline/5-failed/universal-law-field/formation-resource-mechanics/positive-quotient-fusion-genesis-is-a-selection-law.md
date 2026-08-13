# Failed route: positive quotient--fusion genesis is a selection law

- **Status:** `[FALSIFIED] [POSITIVE SURVIVOR PAPER-PROVED] [LEAN PENDING] [NOT RH]`
- **Parent:** Formation Resource Mechanics

## Conjecture

Because quotient--fusion genesis `Q` is nonnegative and `Q=0` exactly when locally optimal gauges
have one common source realization, its positivity should itself select the neutral displacement.

## Exact failure

Let `Gamma(g)=(N(0,I),N(g,I))` with `Q=||g||^2>0`, and let the fixed source be
`G_b=(N(0,1),N(sqrt b,1))`. For every positive integer

\[
 d\le\left\lfloor{b\over Q}\right\rfloor,
\]

one Markov kernel forms `d` independent copies of `Gamma(g)`. Explicitly, set

\[
 m=(g,\ldots,g),\qquad a={m\over\sqrt b},\qquad
 \Sigma=I-aa^*,qquad Y=aX+Z,
\]

with `Z~N(0,Sigma)` independent. Since `||a||^2=dQ/b<=1`, `Sigma` is positive semidefinite.
Under source mark zero, `Y~N(0,I)`; under mark one, `Y~N(m,I)`. Thus strictly positive genesis is
compatible with every prescribed finite formation depth after choosing finite source budget large
enough.

No sign, positivity, or single finite capacity value can select neutrality.

## Strongest positive survivor

The same calculation gives exact maximum depth and global properness:

\[
 G_b\longrightarrow\Gamma(g)^{\otimes d}
 \iff b\ge dQ.
\]

Therefore one **fixed** finite source forms arbitrarily large independent genesis depth iff
`Q=0`. Combined with a trivial synchronization equalizer, cofinal formation selects neutral source
displacement.

This survivor is proved in
`docs/drafts/pipeline/2-fully-proven/universal-law-field/formation-resource-mechanics/gaussian-quotient-fusion-capital-exact-depth-and-testing-properness-law.md`.

## Lesson

Selection is a global properness statement about a production map. It is not local positivity of a
target obstruction. Any RH application must construct cofinal source-coherent formation before
using the zero classification.
