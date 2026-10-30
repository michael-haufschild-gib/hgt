# Physical successor mass and weighted tail reserve

**ID:** completed-arithmetic-forms-physical-successor-mass  
**Stage:** Formalized  
**Type:** Exact source-scale transport and integrated quantitative reserve

The full Gaussian head has monic Hermite diagonal $d_j=8^j j!$ and a unit
triangular congruence. Its determinant is $\prod_{j<N}d_j$, so its exact
successor is $d_N$. For $m'_k=c t^k m_k$, $c>0$ and $t\ne0$, the full
head transforms by $cD H D$, $D_{jj}=t^j$, and the exact successor scales
by $ct^{2N}$.

For the literal native source, take $c=\theta_1(x)^2$ and
$t=\sqrt{q(x)}$, $q(x)=\pi e^{2x}$. The balanced full-form estimate
$J_{N+1}/q$ therefore has the physical successor consequence
$$\frac12\theta_1(x)^2q(x)^N d_N
 < S_N(m^{\mathrm{native}}(x))
 <\frac32\theta_1(x)^2q(x)^N d_N$$
on $q\ge Q_{N+1}$. This transports both the literal source mass and the
full monomial scale, including odd-zero moments.

Integrating the monic variational lower bound against $r\sinh(ar)$ on a
tail with $0<a<1/2$ and $R\ge2X_{N+2}$ gives the exact reserve bound
$$S_N(T_{a,R})\ge\frac{d_N}{2}\int_R^\infty
 r\sinh(ar)\theta_1(r/2)^2q(r/2)^N\,dr>0.$$
The positive integrand is dominated by the actual weighted native diagonal,
so its integrability follows from the complete-source integration theorem.
The inverse head in the left side belongs to the integrated tail. No
pointwise inverse is substituted for it. At the actual strict rank-seven
center head, the compact quadratic contribution plus this explicit integral
is a lower bound for the order-seven center successor. Its compact sign
estimate remains open.

**Lean:** `CompletedArithmeticForms/PhysicalSuccessorMass.lean` and
`CompletedArithmeticForms/WeightedSuccessorReserve.lean`.
`rescaledMoment_successorSchur`, `gaussianFull_successorSchur`,
`nativePhysicalSuccessor_half_bounds_of_horizon`,
`integrableOn_nativeWeightedSuccessorReserve`,
`nativeWeightedSuccessorReserve_pos`, `nativeWeightedSuccessorReserve_le_schur`,
and `centerSeventhSuccessor_explicit_compact_allowance`.
The capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
