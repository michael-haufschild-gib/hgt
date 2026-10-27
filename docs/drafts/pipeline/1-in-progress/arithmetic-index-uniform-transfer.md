# Arithmetic index control across refinement

Status: research. Target is a significant unconditional theorem for Arithmetic Index Descent,
advancing the route to finite off-line support without assuming a global work or index bound.

Existing receivers: finite off-line support iff finite copied energy iff bounded damped source
work iff a uniform index budget on fixed-spline integer-log families. Existing source inputs:
positive independent arithmetic sections and spacing-scale reserves. Existing algebra:
singular range-compatible Schur refinement and finite-rank perturbation inequalities.

Novelty requirement: produce a new source estimate or substantive exact/quantitative transfer;
do not count a repackaged finiteness equivalence or an assumed analytic budget as a contribution.
Current investigation compares compact-tail control, stability of finite-Gram indices without
spectral gaps, and extension of actual positive arithmetic section spaces by signed interactions.

No finiteness conclusion is currently proved. Every claimed theorem will be formalized and
checked individually with lake --old env lean; no full builds or computations.

Selected stronger source contribution: scale increments of arithmetic source work.

New input found in the corpus: every zeta zero with Re>0 has |Im|>=4
(RHTower/ZetaZeroFreeRegionAllZeros). For h_R(t)=R^4/(R²+t²)²,
its R derivative is 4R³ t²/(R²+t²)³. On |t|,|u|>=4 these derivative weights obey
2|v(t)-v(u)| <= |t-u|(v(t)+v(u)). This follows from a factorization of their rational
numerator, using t²>=4t and u²>=4u after replacing heights by absolute values.
The existing near/far reflected-cross estimates then make the R derivative of every
actual reflected pair-work nonnegative. Thus the completed source work is monotone in R.

For an off-line right zero, its self/reflection quartet contributes exactly
h_S(gamma)-h_R(gamma) to the work increment. All other increments are nonnegative.
Target quantitative theorem: for any finite right-zero packet with R<=|gamma|<=2R,
(21/100)*card(packet) <= xiDampedSourceWork(2R)-xiDampedSourceWork(R), R>=4.
The constant is the sharp minimum of 16/(4+x)^2-1/(1+x)^2 for 1<=x<=4.
A telescoping consequence should pay disjoint dyadic shells from accumulated source-work
increments. This supplies a new local quantitative estimate, not another finiteness equivalence.

The source-compatible Schur alternative is parked: useful, but the scale-increment estimate
more directly advances the finite-exception budget. No finiteness bound is assumed or asserted.
