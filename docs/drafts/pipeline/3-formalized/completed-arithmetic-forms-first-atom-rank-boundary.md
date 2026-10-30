# The first theta atom has no all-order signed-positive center

- **ID:** completed-arithmetic-forms-first-atom-rank-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM

For every real center $x$, some signed reflection moment
$$m_k(x)=(-1)^k\,\partial_t^{2k}[f_1(x+t)f_1(x-t)]_{t=0}$$
is negative. It is a negative diagonal of a finite full signed Hankel section.
Thus no finite source horizon makes every first-atom signed moment nonnegative.

Put $q=\pi e^{2x}$, $B=(2q-3)^2$, and $C=4q^2e^{x-2q}>0$. The literal source identity is
$$f_1(x+t)f_1(x-t)=C e^{-2q(\cosh(2t)-1)}[B-12q(\cosh(2t)-1)].$$
Its entire continuation evaluated at $t=iy$ equals
$$g_x(y)=C e^{-2q(\cos(2y)-1)}[B-12q(\cos(2y)-1)].$$
Odd Taylor derivatives vanish; even derivatives are the signed moments $m_k(x)$.
If every $m_k(x)$ were nonnegative, the globally convergent Taylor expansion would make
$g_x$ nondecreasing on $[0,\infty)$. But
$$g_x(\pi/2)=Ce^{4q}(B+24q)>CB=g_x(\pi).$$
This proves the obstruction for every center without a numerical witness or a rank cutoff.

The positive survivor has the opposite quantifier order. For every fixed shifted rank, the
first-atom balanced Hankel matrix is positive definite on a cofinal source ray. Its entries
converge to the strictly positive Gamma matrix with moments
$$\gamma_s\,16^k(s+\tfrac12)_k,\qquad \gamma_s=16^s(\tfrac12)_s.$$
The threshold necessarily depends on rank and shift. The same fixed-rank limit holds for
the complete native theta source, whose exact limiting successor reserve is
$\gamma_s16^{2N}N!(s+\tfrac12)_N$.

Define the actual first negative order by
$$\nu(x)=\min\{k:m_k(x)<0\}.$$
It is finite at every center, and $\nu(x)\to\infty$ as $x\to\infty$. Indeed every fixed
normalized moment tends to a strictly positive Gaussian moment; multiplication by the
positive source mass and scale makes each fixed raw moment eventually positive. A finite
intersection controls all orders through any prescribed $K$, forcing $\nu(x)>K$.
This is an escaping moment order. The whole mixed form has a distinct invariant:
$$\kappa(x)=\min\{N:H_N(s_x)\text{ is not positive semidefinite}\}.$$
The exact parity split and invertible mass-scale congruence make every fixed full signed
head positive definite on its own cofinal ray. Hence $\kappa(x)\to\infty$.
At every center, all smaller heads are positive semidefinite and $\kappa(x)\le\nu(x)+1$.
The inequality permits mixed-entry failure before a negative diagonal appears.

The obstruction concerns the literal first atom. The complete theta source is analytic on
its source strip; the first atom's entire periodic continuation does not identify the
complete source outside that domain. No all-order sign conclusion for the complete source
follows from this obstruction.

Lean: `CompletedArithmeticForms/FirstAtomRankBoundary.lean`, particularly
`exists_firstAtom_signed_moment_neg`, `exists_firstAtom_signed_head_not_posSemidef`,
`firstAtomSignedHead_posDef_eventually`, `firstAtomNegativeOrder_tendsto`,
`firstAtomSignedHead_posSemidef_below_failureRank`,
`firstAtomFailureRank_le_negativeOrder_succ`, and `firstAtomFailureRank_tendsto`.
Kernel dependencies: `propext`, `Classical.choice`, `Quot.sound`.
