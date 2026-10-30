# Arithmetic constraints determine an exact quotient dual norm

**ID:** completed-arithmetic-forms-neutral-dual  
**Stage:** 3-formalized  
**Type:** Arithmetic Green projection and actual prime-source comparison

On an increasing arithmetic mesh $0=k_0<\cdots<k_N=Q$, set
$$
\langle b,c\rangle_D=\sum_{i<N}
\frac{(b_{i+1}-b_i)(c_{i+1}-c_i)}{k_{i+1}-k_i},\qquad D(b)=\langle b,b\rangle_D.
$$
Zero endpoint values give the mixed Green identity
$\langle b,c\rangle_D=\sum_{0<i<N}b_i(L_kc)_i$.
For a zero-boundary constraint profile $g$, define
$$
P_gb=b-\frac{\langle b,g\rangle_D}{D(g)}g.
$$
Division by zero is interpreted as zero. If $D(g)=0$, the exact Green inverse and the
zero radical imply $g=0$ at every mesh node, so the same projection formulas remain valid.
Thus
$$
\langle P_gb,g\rangle_D=0,\qquad
D(P_gb)=D(b)-\frac{\langle b,g\rangle_D^2}{D(g)}.
$$
For every coefficient vector satisfying $\sum_i a_i g_i=0$, Schur completion gives
$$
2a\cdot b-F_k(a)\le D(P_gb).
$$
Equality is attained by $a=L_kP_gb$, which satisfies the constraint by mixed Green summation.
This is the exact constrained dual cost, including singular constraint profiles.

For two profiles $g,h$, put $v=P_gh$, $u=P_v(P_gb)$. Both pairings of $u$ with $g,h$
vanish, and
$$
D(u)=D(b)-\frac{\langle b,g\rangle_D^2}{D(g)}
-\frac{\langle P_gb,v\rangle_D^2}{D(v)}.
$$
The constrained supremum over $a\cdot g=a\cdot h=0$ is attained at $L_ku$.
Both degenerate constraints and dependent pairs are covered by the zero-energy identity.

The projected energy never exceeds $D(b)$. Its radical is exactly the constraint span:
$$
D(u)=0\quad\Longleftrightarrow\quad
\exists\alpha,\beta,\quad b_i=\alpha g_i+\beta h_i\quad(0<i<N).
$$
Zero energy makes $u$ vanish by the Green inverse; the explicit projection then gives the
displayed span. Conversely, every admissible coefficient vector annihilates this span.
The attained dual value is therefore nonpositive, and its nonnegative Green energy forces zero.

For an actual neutral prime packet, choose the interior profiles $g_i=1$ and
$h_i=\log k_i$, with zero endpoint extensions. Its mass and logarithmic constraints
leave the coupling unchanged under both projections. The actual prime form dominates
the conductor comparison, hence pays the prescribed coupling by $D(u)$.
No positivity assumption on a missing arithmetic remainder enters this estimate.

Lean: `CompletedArithmeticForms/NeutralPacketDual.lean`,
`meshDirichletPair_eq_sum`, `meshNeutralSchurCost_isGreatest`,
`meshDoubleNeutralSchurCost_isGreatest`, `meshDirichletEnergy_doubleProjection`,
`meshDoubleProjection_energy_eq_zero_iff`, and `primePacket_neutral_mesh_schur_bound`.
Kernel dependencies: `propext`, `Classical.choice`, `Quot.sound`.
