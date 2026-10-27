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

Paper argument (formalization in progress)
-----------------------------------------
Write a=|t|, b=|u|, T=a²+b² and P=a²b². For a,b>=4,
T>=4(a+b) and a⁴+b⁴>=2(a+b)T. Clearing the positive denominator of
v_R(a)-v_R(b), its numerator is (a-b)(a+b)Q, where
Q=R⁶-P(3R²+T). The sum numerator is S=a²(R²+b²)³+b²(R²+a²)³.
Both S-2(a+b)Q and S+2(a+b)Q are sums of nonnegative terms using those
 two inequalities. Hence 2|v_R(t)-v_R(u)|<=|t-u|(v_R(t)+v_R(u)).
The existing near-field estimate |d cross|<=2E and far-field estimate
|cross|<=E imply reflectedWork(v_R(t),v_R(u))>=0. Since
partial_R h_R(t)=4R³v_R(t), pair work is monotone for R>=0.
Actual pair summability for R>=4 permits subtraction of the two tsums.

For each right-hand multiplicity copy p, inject the four ordered pairs in
{p,lineConj(p)}². Each has pair work h_R(height(p)); distinct right copies
produce disjoint quartets. The full nonnegative increment sum, divided by4,
therefore dominates the sum of damping increments over any right packet.

For R<=|t|<=2R, the numerator of h_(2R)(t)-h_R(t)-21/100 is
(4R²-t²)[21t⁶+294R²t⁴+369R⁴(t²-R²)+285R⁶], with positive denominator
100(4R²+t²)²(R²+t²)². This proves the sharp annular quantum; equality
holds at t=2R. Finite tapered source-work increments converge to this full
increment while retaining all exterior rows.

Novelty: the existing corpus proves eventual detection of a fixed finite index
and convergence of work to total energy. The new result controls each finite
scale increment, proves monotonicity at the pair level, and quantifies the work
forced by zeros entering a doubled height annulus. A future arithmetic bound
can target scale differences rather than the absolute source field.
