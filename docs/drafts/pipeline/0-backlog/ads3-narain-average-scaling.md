# One universal arithmetic profile generates every target average

- **ID:** W11-NAS
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Actual target average](../3-formalized/ads3-narain-target-average.md)

## Conjecture

Put `θ(y)=Σ_(n≥1) exp(−πn²y)` and `f(y)=y^(−1/2)θ(y)`.
For every `Y,Z,y>0`, with `A_YZ` the actual double target average,

`A_YZ(y)=YZ A_11(YZy)+2θ(y/(YZ))−2YZθ(YZy)`
`           +2Zf(yZ/Y)+2Yf(yY/Z)−4YZf(YZy)`.

Thus all target dependence of the arithmetic part is a single dilation
and amplitude. The remaining terms are explicit one-dimensional theta
functions. The proposed identity is stronger than equality of pole sets.

## Mechanism

Expand the two constant terms in the proved mean Mellin formula.
The coefficient of `L₋²/L₊` is `2(YZ)^(1−s)`; subtracting
`(YZ)^(1−s) F_11(s)` cancels it exactly. The two remaining completed-zeta
terms are the Mellin transforms of the displayed theta corrections.
The corpus's `poissonThetaTail_mellin` identifies the actual theta tail.
Prove absolute Mellin convergence and use inversion on the difference:
its transform is zero on a vertical line, so vertical integrability is
immediate. Positive-height continuity upgrades equality to every `y>0`.

Jacobi inversion should then give

`yA_YZ(y)−(YZy)A_11(YZy)=Y+Z−2+(YZ−1)y+O(exp(−c/y))`

for some `c>0`, with polynomial factors absorbed into a smaller `c`.
This agrees with the candidate main-constant shift
`B_YZ−B_11=Y+Z−2−(3/π)log(YZ)` and would transfer every exponent below
one between all target averages. It does not prove any new arithmetic
remainder exponent.

## Gates

- [ ] 0 → 1: exact mean expansion and actual theta Mellin inputs audited.
- [ ] 1 → 2: Mellin uniqueness, scaling identity and theta error proved.
- [ ] 2 → 3: Lean formalization and transitive axiom audit.
