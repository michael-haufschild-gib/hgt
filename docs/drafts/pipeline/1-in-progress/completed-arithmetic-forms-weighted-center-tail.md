# Complete weighted center-tail reserve

**ID:** completed-arithmetic-forms-weighted-center-tail  
**Stage:** In progress  
**Type:** Actual center mixture and compact compensation boundary

For $0<a<1/2$, the actual signed center moments satisfy
$$M_k(a)=\int_0^\infty r\sinh(ar)m_k(r/2)\,dr.$$
Every weighted native jet and every finite weighted native Hankel form are
integrable. These identities are formalized in
`RHTower/ThetaCusp/ThetaCuspCenterMixedAllOrderIntegration.lean`.
The complete rank-seven center head is strict by
`thetaCuspCenterMixedSignedHankel_seven_posDef` in
`RHTower/ThetaCusp/ThetaCuspCenterMixedSeventhRankStrict.lean`.

Let $B_{a,R}$ contain the moment integral on $(0,R]$ and $T_{a,R}$ the integral
on $(R,\infty)$. The quadratic source horizon has the proposed consequence
$$R\ge2X_{N+1}\Longrightarrow H_N(T_{a,R})\succ0,$$
with the same $X_M=\max(0,\tfrac12\log(C_2/\pi)+\log(M+2))$ for every aperture.
The exact source decomposition is $H_N(M(a))=H_N(B_{a,R})+H_N(T_{a,R})$.

For a strict rank-$N$ center head, put
$u=H_N(M(a))^{-1}(M_{i+N}(a))_{i<N}$ and $v=(-u,1)$.
The complete successor has the target decomposition
$$S_N(M(a))=v^{\mathsf T}H_{N+1}(B_{a,R})v+
v^{\mathsf T}H_{N+1}(T_{a,R})v,$$
and the tail term is at least $S_N(T_{a,R})>0$ when $R\ge2X_{N+2}$.
At $N=7$ the required center-head strictness is an established actual-source
theorem. This would localize the first unpaid successor to one compact integral
against its exact global minimizer, with a strictly positive tail allowance.

The full quadratic integrand is essential. The corpus's linear
`thetaCuspNativeSuccessorSource` uses the integrated inverse head and is not
the pointwise Schur complement. Positivity of a local complete head does not
by itself give the sign of that linear integrand.
The weighted tail and fixed-minimizer identities require formalization.

The inherited odd rank-three compensation cannot be extended by a nonnegative
load on the new diagonal: `ThetaCuspInheritedOddCompensation.not_exists_global_inherited_posSemidef`
gives a literal source witness at $q=7$. Its uncorrected source energy is
positive, and the sharp admissible correction interval is
$0<C<\mathrm{correctionBudget}<C_3$.
The coupled correction has an exact determinant identity
$$H\det K=D_{3,\mathrm{corr}}\,\mathrm{gap}-\mathrm{residual}^2.$$
The actual regular direction solves
$x t'+P(x)t=F(x)$ and makes the residual identically zero. Its seam value is
optimal and its seam gap is strictly positive; global gap positivity and a
controlled tail join are separate inputs. These are the exact statements of
`ThetaCuspCoupledOddDirectionTransport.lean` and
`ThetaCuspCoupledOddTransportSchur.lean`.
