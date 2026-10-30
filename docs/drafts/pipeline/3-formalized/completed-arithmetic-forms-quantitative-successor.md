# Quantitative native successor comparison

**ID:** completed-arithmetic-forms-quantitative-successor  
**Stage:** Formalized in Lean 4  
**Type:** Relative source estimate with explicit rank and center dependence

For a moment sequence $m$, let $H_N(m)=[m_{i+j}]_{i,j<N}$ and
$S_N(m)=m_{2N}-b^TH_N(m)^{-1}b$, $b_i=m_{i+N}$.
If $H_N(m),H_N(n)>0$ and $H_{N+1}(m)-H_{N+1}(n)\ge0$, then
$$S_N(m)\ge S_N(n).$$
Indeed, subtracting $S_N(n)$ from moment $2N$ leaves both preceding heads and
their mixed successor rows unchanged. The adjusted $n$ successor is semidefinite
with Schur coordinate zero. The same adjustment to $m$ remains semidefinite by
the assumed matrix difference; its Schur coordinate is $S_N(m)-S_N(n)$.
This argument includes $N=0$ and requires no sign of either original successor.
Positive scalar multiplication gives $S_N(cm)=cS_N(m)$.

Consequently a complete relative comparison
$$\alpha H_{N+1}(g)\le H_{N+1}(m)\le\beta H_{N+1}(g),\qquad
0<\alpha\le\beta,$$
with strict preceding heads gives
$$\alpha S_N(g)\le S_N(m)\le\beta S_N(g).$$
The cost is measured in the full comparison form, including its mixed row.

For the literal balanced native theta source $\sigma_s(x)$, put
$q=\pi e^{2x}$, $M=N+1$, $L=s+2M$, and
$$\eta_{N,s}(x)=\frac{M\operatorname{tr}(G_{M,s}^{-1})C_L}{q},\qquad
C_L=(2L)!D+27\,24^{2L}\frac{e^{3\pi}}{399}(L+1)!.$$
At $q\ge2L+6$ and $\eta<1$, the exact complete-source entry bound gives
$$(1-\eta)G_{M,s}\le H_M(\sigma_s(x))\le(1+\eta)G_{M,s}.$$
Both preceding heads are strict by principal restriction of the positive lower
comparison. Their exact Gamma successor is
$$C_{N,s}=16^{s+2N}(\tfrac12)_sN!(s+\tfrac12)_N.$$
Therefore
$$|S_N(\sigma_s(x))-C_{N,s}|\le\eta_{N,s}(x)C_{N,s}.$$
In particular $q>2M\operatorname{tr}(G_{M,s}^{-1})C_L$ gives the explicit bounds
$$\tfrac12 C_{N,s}\le S_N(\sigma_s(x))\le\tfrac32 C_{N,s}.$$
The constant retains the literal infinite theta remainder. No rank-independent
fraction of the next diagonal or compact-center integrated sign is asserted.

Lean: `CompletedArithmeticForms/SuccessorComparison.lean`,
`successorSchur_mono`, `successorSchur_const_mul`, and `successorSchur_relative_error`;
`CompletedArithmeticForms/NativeSuccessorHorizon.lean`,
`nativeBalancedSuccessor_relative_error_le`, `nativeBalancedSuccessor_half_bounds_of_scale`,
and `nativeBalancedSuccessor_half_bounds_of_horizon`.
All capstone transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.
