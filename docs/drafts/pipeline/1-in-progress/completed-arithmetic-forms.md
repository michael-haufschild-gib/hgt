# Quantitative theory of completed arithmetic forms

**ID:** completed-arithmetic-forms  
**Stage:** In progress  
**Type:** Actual-source comparison, exact dual norms, and simultaneous rank limits

The objects are complete arithmetic or theta quadratic forms, their radicals,
exact successor reserves, and source maps with explicit domain and error costs.
A contribution must retain the literal source, all mixed terms, all omitted-tail
payments, and the precision required by its endpoint.

## Arithmetic Green metric

The complete divisor-conductor kernel is
$$B_Q(i,j)=Q\min(i,j)-ij.$$
For interior coefficients,
$$4E_Q(a)=Q\left[(\sum_i a_i)^2+\sum_i a_i^2\right]+R_Q(a),\qquad R_Q(a)\ge0.$$
Its interior radical is zero. Its inverse is the Dirichlet second difference
 divided by $Q$, and the exact attained coupling cost is
$$\frac1Q\sum_{i=0}^{Q-1}(b_{i+1}-b_i)^2,\qquad b_0=b_Q=0.$$
On irregular nodes $0=k_0<\cdots<k_N=Q$, the minimum extension cost is
$\sum_i(b_{i+1}-b_i)^2/(k_{i+1}-k_i)$, retaining both boundary gaps.
Two neutrality constraints are removed by successive orthogonal projections
in this exact gap metric; their dual radical is the span of the constraints.
For neutral odd-prime packets in $(P,2P]$, $P\ge2$, the literal first-jump
source pays at least half the coefficient square mass.

Lean: `CyclotomicCoercivity`, `DirichletSchurCost`, `IrregularGreen`,
`OptimalInterpolation`, `NeutralPacketDual`, `SeparatedPacketReserve`.

For accumulated increments $c$, the coefficient map $a_j=c_j/j$ gives
$$C_T(c)=\frac{E_{T+1}(a)}{T+1}
=\sum_{n=1}^T\frac{(\sum_{j=1}^n c_j)^2}{n(n+1)}.$$
The exact Euler-deletion source retains every unequal covariance pair and obeys
$$0\le E_{\mathrm{full}}(X,M)-C_T(c^{X,M})\le\frac{(M+1)^2}{T+1}.$$
The upper estimate at the inner cutoff is separate.
Lean: `DivisorCovariance`.

## Complete native rank and successor payment

Put $q=\pi e^{2x}$, $D=50e\exp(2e)$, $A=27e^{3\pi}/399$,
$d_j=8^j j!$, and
$$J_N=16D(N+1)^2+NAe^8.$$
The exact monic Hermite transform has determinant one and sends the full
Gaussian head to $\operatorname{diag}(d_j)$. The literal complete native
balanced head satisfies
$$|v^{\mathsf T}(H_N^{\mathrm{native}}-G_N)v|
\le\frac{J_N}{q}v^{\mathsf T}G_Nv,\qquad q\ge16(N+2)^2.$$
The first atom costs $16D(N+1)^2/q$; the full infinite remainder costs
$NAe^8/q$. The exact Gaussian common-contraction kernel has row mass at most
four, independently of dimension. No inverse-matrix factor enters this bound.

Let
$$Q_M=16(M+2)^2+2J_M,\quad C_2=16+32D+2Ae^8,\quad
X_M=\max\left(0,\tfrac12\log(C_2/\pi)+\log(M+2)\right).$$
Then $Q_M\le C_2(M+2)^2$. Every shifted rank-$N$ head contained in
$M\ge2N+s$ retains the same relative error. At $M=2(N+1)+s$, the exact
native successor has relative error $J_M/q$ against
$$C_{N,s}=16^{s+2N}(1/2)_sN!(s+1/2)_N.$$
For $q\ge Q_M$, its bounds are strict: $C_{N,s}/2<S_N<3C_{N,s}/2$.
Every literal physical native and first-atom signed rank-$N$ head is strict
for $x\ge X_{N+1}$.

The first-atom failure dimension obeys
$$\sqrt{q/C_2}<\kappa(x)+3.$$
For $x\ge0$, $\sqrt q<\nu(x)\le C_*q$ and
$\kappa(x)\le\nu(x)+1\le1+C_*q$, where
$C_*=(9e^{4\pi}+2)/(2\log2)$. Both invariants are finite at every center
and escape to infinity; no common first-atom tail is positive at all ranks.
The Gamma successor fraction of the new diagonal is at most $(2/3)^N$.

Lean: `GaussianJetConvolution`, `GeometricContraction`,
`HermiteContractionPayment`, `GaussianContractionBound`, `NativeQuadraticRank`,
`QuadraticRankHorizon`, `PhysicalQuadraticHorizon`, `FirstAtomEffectiveRankBoundary`.

## Integration, mixtures, and the compact center boundary

Every complete native seam tail head is strict, with an explicit half-seam
neighborhood. The distant tail satisfies
$$r\ge2X_{N+1}\Longrightarrow T_N(r)\succ0,\qquad
2X_{N+1}\le r<t\Longrightarrow T_N(r)-T_N(t)\succ0.$$
The difference is exactly the native form integrated on $(r,t]$.

For strict heads $A_m=H_N(m)$ and $A_n=H_N(n)$, write
$u_m=A_m^{-1}(m_{i+N})_{i<N}$ and $w=u_{m+n}$. Then
$$S_{m+n}=S_m+S_n+(w-u_m)^{\mathsf T}A_m(w-u_m)
 +(w-u_n)^{\mathsf T}A_n(w-u_n).$$
The extra reserve vanishes exactly when $u_m=u_n$. Every monic direction
$(-z,1)$ has energy $S_m+(z-u_m)^{\mathsf T}A_m(z-u_m)$.
Native integrated successors therefore decrease strictly beyond $2X_{N+2}$.

For every $0<a<1/2$, the literal center moments are
$M_k(a)=\int_0^\infty r\sinh(ar)m_k(r/2)\,dr$.
Their compact and tail pieces $B_{a,R},T_{a,R}$ satisfy $M=B+T$ and
$H_N(T_{a,R})\succ0$ for $R\ge2X_{N+1}$, uniformly in aperture.
The actual rank-seven center head is strict. With its global minimizer
$v=(-u_M,1)$ and $R\ge2X_9$,
$$S_7(M)\ge v^{\mathsf T}H_8(B_{a,R})v+S_7(T_{a,R}),\qquad S_7(T_{a,R})>0.$$
The compact contribution remains unpaid. The full quadratic integrand is
required; the linear source expression involving the integrated inverse
need not inherit pointwise positivity from a native head.

Lean: `SeamCoercivity`, `TailRankHorizon`, `SuccessorMixture`, `WeightedCenterTail`.

## Source-clock boundary

The exact clock $u=\operatorname{arsinh}(t/\sqrt q)$ sends the first-atom pair
to $C e^{-4t^2}(B-24t^2)$, $B=(2q-3)^2$. Its signed moments are
$C\gamma_k(B+6k)$. Every clocked finite head is semidefinite exactly when
$B\ge3$. Outside that cone, all individual signed moments remain nonnegative
but some mixed head fails. The physical nonlinear pullback has finite failing
rank at every center. An invertible source clock need not preserve the full
signed Hankel cone.

Lean: `HyperbolicClock`, `GaussianClockCone`, `ScaleJetTransport`.

## Endpoint questions

1. Pay the compact center contribution at the order-seven successor and
   propagate the complete signed hierarchy. Inherited scalar odd compensation
   has a literal obstruction; residual-free moving transport has a strict seam
   gap but requires global gap positivity and an admissible tail join.
2. Compare the complete macroscopic Weil operator at overlap $3/2$ with the
   arithmetic Green metric. The proved prefix index ceiling is not positivity.
3. Bound the actual bandwidth-$4/3$ coalescent surplus by $N/18+o(N)$ in its
   receiver windows. Gauge mean-square bounds do not evaluate the prime source
   at the distinguished gauge point zero.
4. Obtain subpower actual Euler-deletion covariance at the inner cutoff.
5. Pay the complete Suzuki rectangular defect and actual CCM first-clock floor.
6. Exclude every theta-clock guarded zero; their unconditional finiteness makes
   an eventual condition insufficient.
7. Bound the complete arithmetic Hecke defect or index from above.
8. Prove the actual Chebyshev mean-square exponents $5/3+\varepsilon$ or
   $3/2+\varepsilon$, or the corresponding complete detector Gram bounds.
9. Preserve source reserves, radicals, domains, and endpoint tolerances through
   the simultaneous limits required by these questions.

All Lean files above are in `formal/GaloisForLFunctions/CompletedArithmeticForms/`.
The foundational objects, mechanisms, and source connections are in its `README.md`.
