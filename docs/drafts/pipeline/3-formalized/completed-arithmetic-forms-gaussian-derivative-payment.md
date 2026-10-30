# Quadratic complete-form rank payment

**ID:** completed-arithmetic-forms-gaussian-derivative-payment  
**Stage:** Formalized in Lean 4  
**Type:** Complete native source estimate and physical rank consequences

Put $q=\pi e^{2x}$, $D=50e\exp(2e)$, $A=27e^{3\pi}/399$, and
$d_i=8^ii!$. The literal normalized first-atom source $F_q$ satisfies
$$\sup_{|z|\le R}|e^{-4z^2}F_q(z)-1|\le DR^4/q,
\qquad R\ge1,\quad q\ge\max(3,4R^2,R^4).$$

For every entire $h$,
$$\partial_z^i\partial_w^j(e^{8zw}h(z+w))_{(0,0)}
=\sum_{r\le\min(i,j)}\binom ir\binom jr d_r h^{(i+j-2r)}(0).$$
With $t=\sqrt{(N+1)/8}$ and $R=4t$, falling-factorial payment gives
$$\frac{\binom ir\binom jr d_r(i+j-2r)!}{R^{i+j-2r}}
\le2^{-(i+j-2r)}\sqrt{d_i d_j},\qquad r\le\min(i,j),\quad i,j\le N.$$
The nonnegative kernel $C=LL^{\mathsf T}$,
$L_{ij}=\mathbf1_{j\le i}2^{-(i-j)}$, has row mass at most four.
Thus the complete first-atom Hermite error satisfies
$$|v^{\mathsf T}(H^{(1)}_{\rm Hermite}-\mathcal D_N)v|
\le\frac{16D(N+1)^2}{q}v^{\mathsf T}\mathcal D_Nv,
\qquad \mathcal D_N=\operatorname{diag}(d_i),\quad q\ge16(N+2)^2.$$

The entire transformed native remainder has entries at most $Ae^8/q$ on this
same domain. Since $d_i\ge1$, its relative form cost is at most $NAe^8/q$.
The exact monic Hermite congruence returns both bounds to every original
balanced moment direction, without an inverse-matrix payment. Consequently
$$|v^{\mathsf T}(H_N^{\rm native}-\mathcal G_N)v|
\le\frac{J_N}{q}v^{\mathsf T}\mathcal G_Nv,
\qquad J_N=16D(N+1)^2+NAe^8.$$

Lean: `GaussianJetConvolution.lean`, `GeometricContraction.lean`,
`HermiteContractionPayment.lean`, `GaussianContractionBound.lean`, and
`NativeQuadraticRank.lean` in `CompletedArithmeticForms/`.
The actual-source capstone is `nativeBalancedFullHead_quadratic_rank_error_le`.
Audited capstones have only `propext`, `Classical.choice`, and `Quot.sound`.

The physical consequences use
$$Q_M=16(M+2)^2+2J_M\le C_2(M+2)^2,\qquad C_2=16+32D+2Ae^8.$$
Principal restriction $i\mapsto2i+s$ retains the error $J_M/q$ for every
shifted rank-$N$ head contained in $M\ge2N+s$. The exact native successor at
$M=2(N+1)+s$ satisfies
$$|S_N-C_{N,s}|\le(J_M/q)C_{N,s},\qquad q\ge16(M+2)^2,\quad q>J_M.$$
On $q\ge Q_M$ its bounds are strict: $C_{N,s}/2<S_N<3C_{N,s}/2$.
These statements and the half-Gaussian reserve of both native and first-atom
shifted heads are formalized in `QuadraticRankHorizon.lean`; all five capstones
have only the standard axioms. The physical center bound is
$$X_M=\max\bigl(0,\tfrac12\log(C_2/\pi)+\log(M+2)\bigr).$$
Every literal native and first-atom rank-$N$ signed head is strict at
$x\ge X_{N+1}$. The first failing physical first-atom dimension satisfies
$$\sqrt{q/C_2}<\kappa(x)+3.$$
These consequences and the quadratic universal envelope are formalized in
`PhysicalQuadraticHorizon.lean`; all five capstones have only `propext`,
`Classical.choice`, and `Quot.sound`.
