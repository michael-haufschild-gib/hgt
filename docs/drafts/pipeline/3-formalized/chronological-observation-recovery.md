# Exact algebraic loss versus uniform recovery

**Status:** fully formalized and axiom-audited. `CubicRecovery` built, nine declarations: the explicit polynomial family, its membership in the observation algebra, the two-sided value bounds, the certified `2/(n+2)` error rate, arbitrary-accuracy physical recovery, and the absence of a positive uniform separation. No quotient norm instance is introduced. This tests the meaning of the completed observation cusp and repair construction. Polynomial approximation is classical; no novelty claim for the iteration below.

## The obstruction

On the physical cubic section, the middle gap satisfies 0≤c≤1. The lost-observation algebra A=ℝ[u,c²,c³] contains c², and c=√(c²) is a continuous function of this observation. Although c is provably absent from A, uniform approximation can recover it. Thus the nonzero algebraic class [c] in B/A cannot carry a positive quotient seminorm induced by the uniform observation norm. The audited quotient, its weights, and its Mellin response remain algebraic statements; they do not by themselves produce a nondegenerate Banach-space defect.

## Constructive positive survivor

Define polynomials P₀=0 and

`P_(n+1)=P_n+(c²−P_n²)/2`.

Every P_n belongs to A by its algebra operations. For every 0≤c≤1,

`0≤P_n(c)≤c`, and `0≤c−P_n(c)≤2/(n+2)`.

Proof: the base case follows from c≤1. If 0≤p≤c≤1, the next value is nonnegative, and

`c−[p+(c²−p²)/2]=(c−p)[1−(c+p)/2]≥0`.

Write e=c−p. Since c+p≥e, the next error is at most f(e)=e−e²/2. This function is increasing on [0,1], as f(a)−f(e)=(a−e)(1−(a+e)/2)≥0 for e≤a≤1. With a=2/(n+2),

`e_next≤2/(n+2)−2/(n+2)²≤2/(n+3)`;

the last inequality is equivalent to (n+1)(n+3)≤(n+2)². This proves the bound without numerical evidence. Consequently, for every positive ε there is P∈A whose physical observation differs from c by less than ε uniformly.

The positive statement is an explicit family of polynomial recovery maps with a certified error bound. It separates exact finite polynomial expressibility from finite-accuracy measurement. Further questions: optimal degree cost of recovery, and whether a degree-sensitive completion retains a meaningful part of the algebraic spectrum. Neither is claimed solved here.

For comparison, approximation using only polynomials in c² is the classical approximation of √x on [0,1]. The abstract of [Carpenter–Varga (1993)](https://doi.org/10.1007/BFb0117488) describes the established power-function approximation problem and Bernstein asymptotics. This comparison does not classify approximation using every generator of A. The next [flow-compatible recovery problem](chronological-equivariant-recovery.md) imposes an additional physical scaling law and has a sharp positive gap on paper.
