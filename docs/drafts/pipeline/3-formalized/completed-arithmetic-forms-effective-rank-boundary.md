# An effective source-scale bound for the first-atom failure rank

**ID:** completed-arithmetic-forms-effective-rank-boundary  
**Stage:** Formalized in Lean 4  
**Type:** Quantitative source obstruction and rank exhaustion

Let $q=\pi e^{2x}$, $B=(2q-3)^2$, $C=4q^2e^{x-2q}$, and $H=e^{4\pi}$.
For the entire rotated first-atom pair
$$
g_x(z)=C\exp[-2q(\cos(2z)-1)]\,[B-12q(\cos(2z)-1)],
$$
the circle $|z|=2\pi$ has the bound
$$|g_x(z)|\le M=C e^{2q(H+1)}[B+12q(H+1)].$$
Indeed $|\cos(2z)|\le e^{2|z|}=H$; the exponential and affine factors then have
the displayed bounds. Its literal real values satisfy
$$g_x(\pi/2)-g_x(\pi)=C[e^{4q}(B+24q)-B]\ge24qC.$$

If the first $J$ real Taylor derivatives of an entire function are nonnegative, its
Taylor polynomial of degree $J-1$ is nondecreasing on $[0,\pi]$. A circle bound $M$
at radius $2\pi$ bounds either tail at $\pi/2$ and $\pi$ by $2M\,2^{-J}$ through
Cauchy's coefficient estimate and the geometric series. Thus its decrease between these
points is at most $4M\,2^{-J}$.

For the literal first-atom least negative moment order $\nu(x)$, every real Taylor
derivative below $2\nu(x)$ is nonnegative; the odd derivatives vanish. The preceding
bounds with $J=2\nu(x)$ give
$$
2^{2\nu(x)}\le
\frac{e^{2q(H+1)}[(2q-3)^2+12q(H+1)]}{6q}.
$$
This holds at every real center, since $q,C>0$.

For $q\ge1$, $(2q-3)^2\le13q^2$ and $H\ge1$, so the quotient outside the exponential
is at most $7Hq\le e^{7Hq}$. Consequently
$$
\nu(x)\le\frac{9H+2}{2\log2}\,q,\qquad
\kappa(x)\le1+\frac{9H+2}{2\log2}\,q.
$$
In particular these bounds hold for $x\ge0$. Together with $\nu(x),\kappa(x)\to\infty$,
they locate the finite first-atom obstruction on an escaping, at-most-linear physical scale.
The constant is explicit and coarse. No complete-source all-rank sign follows: the infinite
theta remainder has its own rank-dependent error and analytic domain.

The declarations in
`GaloisForLFunctions/CompletedArithmeticForms/FirstAtomEffectiveRankBoundary.lean`
are `entire_decrease_le_of_nonneg_initial_jets`,
`firstAtomRotatedPair_circle_bound`, `firstAtomNegativeOrder_pow_bound`,
`firstAtomNegativeOrder_le_physicalScale`, `firstAtomFailureRank_le_physicalScale`,
and `exists_firstAtom_signed_head_failure_le_scale`.
Their transitive axiom dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.
