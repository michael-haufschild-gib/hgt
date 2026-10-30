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

Finite-source terminal completion gives
$$\mathcal C_T(c)=C_T(c)+\frac{(\sum c_j)^2}{T+1}
=\sum_{j,k\le T}\frac{c_jc_k}{\max(j,k)}.$$
With $F_j=jb_j$, $F_0=0$, $F_{T+1}=F_T$, its exact attained dual cost is
$D_T(F)$, and its unique optimizer is $c_{*,j}=j(2F_j-F_{j-1}-F_{j+1})$.
The full identity is
$$\mathcal C_T(c)-2\langle c,b\rangle+D_T(F)=\mathcal C_T(c-c_*).$$
The optimizer mass is $F_T$. Source extension changes energy by
$c_{T+1}(2M_T+c_{T+1})/(T+1)$, so its monotonicity has an exact sign boundary.
Lean: `TerminalCompletion`.

The actual Euler source satisfies
$$|E_{\mathrm{full}}(X,M)-\mathcal C_T(c^{X,M})|\le\frac{(M+1)^2}{T+1}.$$
Its complete mixed pairing is bounded by $D_T(F)+(M+1)^2/(T+1)$,
with the additional gain $-(M_T-Tb_T)^2/(T+1)$.
Lean: `EulerTerminalCost`.

For a fixed probe supported through $T$, the exact dual cost over all finite
source supports is $D_T(F)+F_T^2$. A neutral source supported through $T+1$
attains it. Finite-source completion itself equals the literal infinite
accumulation series. The two truncation costs agree exactly at $F_T=0$.
Lean: `SourceProbeBoundary`.

The literal plateau Weil prefix satisfies $A\succeq I/20$ and
$0\le b^{\mathsf T}A^{-1}b\le20\|b\|^2$ beyond one joint horizon,
for $N\ge M$, $c>0$, $cM\le N$. Its complete mixed block gives
$$D-20B^{\mathsf T}B\preceq D-B^{\mathsf T}A^{-1}B\preceq D.$$
The constant remains fixed at $(c,M,N)=(3/2,2K,3K)$.
Lean: `WeilPrefixPayment`.

For the complete tilted-spline matrix, the sharp asymptotic inverse cost is
$E_1(c)^{-1}$, where $E_1(c)>0$ is the completed pole energy. Every larger
constant eventually pays all inverse directions; every smaller positive
constant is eventually violated by a unit eigenvector. One finite cost and
one horizon work uniformly for every bounded interval $0<c\le K$.
Lean: `WeilInverseCost`.

Every fixed normalized Ramanujan mode satisfies
$\|A_N(c)^{-1}r_{m,N}-E_m(c)^{-1}r_{m,N}\|\to0$.
Every fixed finite packet therefore has mixed inverse limit
$\sum_m b_md_m/E_m(c)$. The estimate
$\|A^{-1}v-\lambda^{-1}v\|\le(e\lambda)^{-1}\|Av-\lambda v\|$
retains the complete floor $A\succeq eI$.
Lean: `WeilGreenModes`.

For every profile and fixed positive overlap, the completed conductor heat
series converges exactly for $\beta>1$. The logarithmic lower envelope and
the prime-conductor upper envelope retain the full shell and pole completion.
For the actual positive tilted-spline energies,
$\sum_m E_m(c)^{-k}=\infty$ for every integer $k\ge0$.
Lean: `ConductorHeatThreshold`.

The exact conductor Green operator on complex $\ell^2$ is
$G_ce_m=E_m(c)^{-1}e_m$. It is compact and injective, with exact norm
$E_1(c)^{-1}$ attained at the pole coordinate. None of its integer
coordinate-eigenvalue power sums is finite.
Lean: `ConductorGreenCompletion`.

The literal upward residual satisfies
$\|U_{m,c,N}\|^2\le C_m[c^{10}(\log N/N)^2+c^6/\sqrt{\log N}]$,
with both offset signs and horizon cutoffs retained. Its joint domain is
$c\ge1$, $c/N\le1$, $B=\lceil ec\rceil\le N$, and $2(e+3)cB\le N$,
beyond one conductor-dependent horizon.
Lean: `UpwardSourcePayment`.

The literal Schläfli source has $K_{i\tau}(a)>0$ for $a>0$, $|\tau|\le a$.
Every complex-order zero satisfies $\Re\nu=0$ and $a<|\Im\nu|$.
The energy flux proves zero exclusion throughout this joint argument-order
domain; source reflection and conjugation fix the positive real sign.
Lean: `BesselSpectralBand`.

The same literal source satisfies
$$K'_{i\tau}(a)\ge-(1+1/a)K_{i\tau}(a),\qquad |\tau|\le a,$$
and its full signed radial combination has reserve
$$ (a^2+9)K_{i\tau}(a)+6aK'_{i\tau}(a)
\ge(a^2-6a+3)K_{i\tau}(a)>0\qquad(a\ge6).$$
The decaying barrier flux has negative derivative throughout the band.
Lean: `BesselBarrierPayment`.

The actual radial Wigner transform is exactly
$$\int_{\mathbb R}a^2(a^2+9-6a\cosh(2v))e^{-a\cosh(2v)}e^{2ibv}\,dv
=a^2[(a^2+9)K_{ib}(a)+6aK'_{ib}(a)].$$
At physical center $u\ge0$, each product fibre $k\ge1$ has scale
$a=2\pi k e^{2u}\ge6$. On $|b|\le a$ its sign equals the sign of
$\sum_{nm=k}e^{-ib(\log n-\log m)}$; individual diagonal pairs are positive.
Lean: `WignerSpectralBand`.

For the literal Chebyshev prefix $F(N)=\sum_{2\le d<N}(\psi(d)-d)/\sqrt d$,
let $E(N)=\sum_{2\le n\le N}F(n)^2/n^2$, $c_j=F(j)-F(j-1)$,
and $\mathcal R_N=R_{N+1}(c_j/j)/(N+1)$. Then
$$C_N(c)\le E(N)\le\tfrac43C_N(c),\qquad
0\le\mathcal R_N\le4E(N),\qquad E(N)\le60N+\tfrac13\mathcal R_N.$$
The two explicit coefficient channels cost at most $180N$ in total.
Every uniform power bound with exponent $r\ge1$ is equivalent for $E$ and
$\mathcal R$. The actual remainder therefore carries precisely the
$5/3+\varepsilon$ and $3/2+\varepsilon$ strip questions.
Lean: `ChebyshevCyclotomicCompletion`.

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
The exact full signed physical native successor retains its mass and degree:
$$\tfrac12 f(x)^2q(x)^N8^NN!<S_N(m(x))<\tfrac32 f(x)^2q(x)^N8^NN!,
\qquad x\ge X_{N+1}.$$
Exact moment rescaling $m'_k=ct^km_k$ multiplies $S_N$ by $ct^{2N}$.

The first-atom failure dimension obeys
$$\sqrt{q/C_2}<\kappa(x)+3.$$
For $x\ge0$, $\sqrt q<\nu(x)\le C_*q$ and
$\kappa(x)\le\nu(x)+1\le1+C_*q$, where
$C_*=(9e^{4\pi}+2)/(2\log2)$. Both invariants are finite at every center
and escape to infinity; no common first-atom tail is positive at all ranks.
The Gamma successor fraction of the new diagonal is at most $(2/3)^N$.

Lean: `GaussianJetConvolution`, `GeometricContraction`,
`HermiteContractionPayment`, `GaussianContractionBound`, `NativeQuadraticRank`,
`QuadraticRankHorizon`, `PhysicalQuadraticHorizon`, `PhysicalSuccessorMass`,
`FirstAtomEffectiveRankBoundary`.

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
More generally, $R\ge2X_{N+2}$ gives the explicit payment
$$0<\mathcal B_N(a,R)=\frac{8^NN!}{2}\int_R^\infty
r\sinh(ar)f(r/2)^2q(r/2)^N\,dr\le S_N(T_{a,R}).$$
The compact contribution remains unpaid. The full quadratic integrand is
required; the linear source expression involving the integrated inverse
need not inherit pointwise positivity from a native head.

Lean: `SeamCoercivity`, `TailRankHorizon`, `SuccessorMixture`, `WeightedCenterTail`,
`WeightedSuccessorReserve`.

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
2. Pay the complete Weil source on a prescribed unbounded overlap schedule.
   The tilted unit spline already has positivity and a common spectral floor
   on every bounded overlap interval, including $3/2$; its limiting ground
   energy is the completed pole energy. A growing schedule requires estimates
   relative to that vanishing reserve. Eventual complete nonnegativity for
   $c_N=2(\log N)^\alpha$, $\alpha>1/4$, is equivalent to RH.
   The plateau prefix theorem concerns a
   different profile and does not decide its full macroscopic residual.
3. Bound the actual bandwidth-$4/3$ coalescent surplus by $N/18+o(N)$ in its
   receiver windows. Gauge mean-square bounds do not evaluate the prime source
   at the distinguished gauge point zero.
4. Obtain subpower actual Euler-deletion covariance at the inner cutoff.
5. Pay the complete Suzuki rectangular defect and actual CCM first-clock floor.
6. Exclude every theta-clock guarded zero; their unconditional finiteness makes
   an eventual condition insufficient.
7. Bound the complete arithmetic Hecke defect or index from above.
8. Prove the actual Chebyshev mean-square exponents $5/3+\varepsilon$ or
   $3/2+\varepsilon$. Equivalently, prove those bounds for the normalized
   cyclotomic remainder; the two explicit coefficient channels are paid.
   The corresponding complete detector Gram bounds remain another source route.
9. Preserve source reserves, radicals, domains, and endpoint tolerances through
   the simultaneous limits required by these questions.

All Lean files above are in `formal/GaloisForLFunctions/CompletedArithmeticForms/`.
The foundational objects, mechanisms, and source connections are in its `README.md`.
