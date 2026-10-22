# WS2–theta CDF bridge at Hilbert–Carleman grade

- **ID:** WS2-TQFQ-HS
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); Lean formalization and spectral orientation open
- **Source:** WS2 two-step signed saddle and the literal completed-theta quantile operator
- **Statement:** On a canonical common signed prime/Fourier carrier, a source-defined Hilbert–Schmidt correction gives the exact completed-Xi determinant. In this alignment the correction is not trace class; its essential contribution is nonlocal.

## Proof chain and scope

The [theta CDF-action quotient](theta-quantile-fourier-action-quotient.md) constructs $D=PB|_{e^\perp}$ from the literal theta density, with

\[
D_{mn}=\frac{\Phi_m-\Phi_{n-m}}{2\pi n},\qquad
\Phi_j=\int_{\mathbb R}(1-\cos(2\pi jF(x)))\,dx,\qquad m,n\in\mathbb Z\setminus\{0\}.
\tag{1}
\]

The corpus proves $\det_2(I+zB)=\Xi_C(z)/\Xi_C(0)$. Since $Be=0$ and $B$ has block form $\begin{psmallmatrix}D&0\\\beta&0\end{psmallmatrix}$ on $e^\perp\oplus\mathbb Ce$, its nonzero eigenvalues, with algebraic multiplicity, equal those of $D$. Hence

\[
\det_2(I+zD)=\Xi_C(z)/\Xi_C(0). \tag{2}
\]

Let $S$ be the [WS2 two-step signed saddle operator](../../../../../../formal/GaloisForLFunctions/RHTower/RoutePTwoStepWildSaddleTraceClassRelocation.lean). Identify $e_n$ with the positive coordinate at the $(n-1)$-st prime and $e_{-n}$ with its negative coordinate, for $n\ge1$, using the corpus's nthPrimeEquiv. This Fourier-to-prime basis map is a unitary $U$. Define, **without any Xi zero labels**,

\[
C=UDU^{-1},\qquad K=C-S. \tag{3}
\]

Both $D$ and $S$ are Hilbert–Schmidt, so $K$ is Hilbert–Schmidt. The corrected WS2 operator $S+K=C$ has exact source determinant occurrence:

\[
\boxed{\det_2(I+z(S+K))=\Xi_C(z)/\Xi_C(0).} \tag{4}
\]

This is a source-defined transport of an already exact theta carrier, **not** a derivation of occurrence from the original WS2 diagonal saddle alone. It does not make $C$ selfadjoint and does not prove RH.

## Why the correction is genuinely determinant₂-grade

The Fourier diagonal of $D$ is $d_n=\Phi_n/(2\pi n)$ for $n>0$, while the WS2 positive diagonal at the corresponding prime index is

\[
s_n=\frac{v_{2,n-1}}{2\pi N_{n-1}}
      \sim \frac{\log n}{2\pi n}.
\tag{5}
\]

Here $N_j=\max(e^3,j+1/8)$ and $v_{2,j}=L_j-\log(L_j-\log L_j)$, $L_j=\log(N_j/e)$; therefore $N_{n-1}\sim n$ and $v_{2,n-1}\sim\log n$.

For the actual theta density, $\Phi_n=o(\log n)$. Here is a source-level proof. The corpus's [all-order first-atom approximation](../../../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspFirstAtomAllOrderApproximation.lean) and the explicit first atom give $(\log k)'(x)\to-\infty$ as $x\to+\infty$: its logarithmic derivative is $9/2-2\pi e^{2x}+o(e^{2x})$. Evenness gives the opposite sign at $-\infty$. By log-concavity, for $x$ large with $(\log k)'(x)<0$,

\[
\frac{\int_x^\infty k(y)\,dy}{k(x)}
\le \frac{1}{-(\log k)'(x)}\longrightarrow0.
\]

The left-tail analogue follows by reflection. As $t=F(x)$ and $q(F(x))=M/k(x)$, these are precisely $tq(t)\to0$ as $t\downarrow0$ and $(1-t)q(t)\to0$ as $t\uparrow1$.

Given $\varepsilon>0$, choose $\delta$ so that $q(t)\le\varepsilon/t$ on $(0,\delta)$ and $q(t)\le\varepsilon/(1-t)$ on $(1-\delta,1)$. Splitting the CDF action at $1/n,\delta,1-\delta,1-1/n$, using $1-\cos y\le y^2/2$ in the endpoint intervals and $1-\cos y\le2$ elsewhere, yields

\[
\Phi_n\le 4\varepsilon\log n+O_\varepsilon(1).
\]

As $\varepsilon$ is arbitrary, $\Phi_n=o(\log n)$ and $d_n=o(\log n/n)$. Consequently

\[
\langle e_n,U^{-1}KUe_n\rangle=d_n-s_n
       \sim-\frac{\log n}{2\pi n},
\qquad
\sum_{n\ge1}|d_n-s_n|=\infty.
\tag{6}
\]

The diagonal of a trace-class operator is absolutely summable in every orthonormal basis. Thus

\[
\boxed{K\in\mathcal S_2\setminus\mathcal S_1.} \tag{7}
\]

The explicit opposite-mode entries from (1) are nonzero and skew, so $K$ is also nonselfadjoint. The exact Xi spectrum is carried by a nonlocal, determinant₂-grade correction; no trace-class additive repair exists for **this natural alignment and this exact transported theta operator**.

Away from WS2's own zeros, the standard Hilbert–Carleman product law makes the arithmetic correction explicit:

\[
\frac{\Xi_C(z)}{\Xi_C(0)}
=\det_2(I+zS)\,
  \det_2\!\left(I+z(I+zS)^{-1}K\right)
  \exp\!\left[-z^2\operatorname{tr}\bigl(S(I+zS)^{-1}K\bigr)\right].
\tag{8}
\]

The second determinant is a source-defined *relative* determinant on the resolvent set of $I+zS$. Its behavior there, together with the exponential anomaly, encodes the missing phase; separate factors need not extend meromorphically across a zero of $I+zS$. Equation (8) provides no zero-free or real-spectrum law.

The [theta resistance-network theorem](../../../3-formalized/theta/theta-quantile-resistance-network.md#kron-reduction-exposes-the-universal-clock-port) gives a sharper normal form for the **same** corrected WS2 carrier. In Fourier coordinates let $a_n=-\widehat h(n)>0$, $h_0=\int h$, $J_{mn}=\delta_{mn}/(2\pi n)$, and let $G$ be the positive Schur complement of multiplication by $h$ over the constant mode. With $c_n=1/(2\pi n)$, its exact pencil is

\[
G\,U^{-1}(S+K)U=J-\frac{a\otimes c}{h_0}. \tag{9}
\]

This identifies the determinant-bearing correction as an inverse-network response with one conductance/clock boundary port. $G$ is injective but not bounded below, and the port is singular in its energy completion. Thus (9) gives a concrete target for spectral orientation without turning the Hilbert--Schmidt correction into a bounded self-adjoint similarity. On actual Xi root modes its boundary-work identity reduces to the universal root energy identity, with a weighted Cauchy--Schwarz gap in the metric; a theta-specific constraint must act on the two-ended connection coefficient before root specialization.

## Whole-chain consequence and next conjecture loop

WS2's signed diagonal gives a real-spectrum reference with the correct smooth scale; theta gives exact divisor occurrence. In the natural source-only identification, their difference has a sharp Schatten threshold and cannot be treated as WS2's previously proved trace-class relocation. The next hard conjecture is a theta-specific orientation law for the relative determinant or its equivalent one-port quotient. Test source candidates against the full nonlocal kernel (1), including the compact accumulation point, before attempting a homotopy or positive-metric argument.

The preceding paper proof uses exact corpus source identities but has **not** been checked in Lean. It makes no priority claim and does not amend the read-only frontier map.
