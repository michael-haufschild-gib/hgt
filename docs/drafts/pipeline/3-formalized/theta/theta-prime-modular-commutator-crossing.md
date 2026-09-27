# Ordered prime–modular theta commutator

- **ID:** TPMC-1
- **Stage:** 3-formalized. Lean: `GaloisForLFunctions.RHTower.ThetaDeletionInversionCommutator`, `ThetaQuadratureDefectSpectralKernel`, `ThetaCommutatorKernelInertia`, see `theta-prime-modular-commutator-crossing-formalized.md`
- **Type:** THEOREM (paper and Lean)
- **Source:** The literal Jacobi theta series, deletion of integer atoms divisible by a prime, and theta inversion.
- **Statement:** The commutator has a strict one-crossing source order, yet its two-scale matrix kernel has infinite positive and negative index even on actual prime scales. A positive Gaussian quadrature discrepancy gives its exact rank-one-plus-signed-sine decomposition.

## Source operation and theorem

Put \(\Theta(y)=\sum_{n\in\mathbb Z}e^{-\pi n^2y}\) for \(y>0\), and let

\[
(Sf)(y)=y^{-1/2}f(1/y),\qquad (D_qf)(y)=f(y)-f(qy).
\]

Jacobi inversion is \(S\Theta=\Theta\). For \(q=p^2\), with \(p\) prime, \(D_q\Theta\) deletes precisely the theta atoms whose integer label is divisible by \(p\). The source commutator is

\[
 C_q(y):=(D_q-SD_q)\Theta(y)
       =q^{-1/2}\Theta(y/q)-\Theta(qy)
       =y^{-1/2}\Theta(q/y)-\Theta(qy).                 \tag{1}
\]

**[PROVED HERE]** For every \(q>1\),

\[
 C_q(y)>0\quad(0<y<1),\qquad C_q(1)=0,\qquad
 C_q(y)<0\quad(y>1).                                  \tag{2}
\]

Moreover \(SC_q=-C_q\). The stronger order and exact endpoint are

\[
 \partial_q[-C_q(y)]>0\quad(q\ge1,\ y>1),\qquad
 0<-C_q(y)<1-y^{-1/2},\qquad
 \lim_{q\to\infty}C_q(y)=y^{-1/2}-1.                  \tag{3}
\]

By inversion, \(C_q(y)\) increases strictly in \(q\) for \(0<y<1\), from zero to \(y^{-1/2}-1>0\). Thus the family is strictly ordered on both sides of its sole seam crossing.

Jacobi inversion also gives the unexpected **exchange symmetry**
\[
 F(q,y):=-C_q(y)
   =\Theta(qy)-q^{-1/2}\Theta(y/q)
   =\Theta(qy)-y^{-1/2}\Theta(q/y)
   =F(y,q),\qquad q,y>1.                              \tag{4}
\]
Consequently \(F\) increases strictly in *both* arguments on \((1,\infty)^2\), vanishes on either boundary \(q=1\) or \(y=1\), and has the respective limits \(1-y^{-1/2}\) and \(1-q^{-1/2}\).

In logarithmic coordinates \(a=\log q\), \(b=\log y\), set \(P(t)=e^{t/4}\Theta(e^t)\). Jacobi inversion makes \(P\) even, and the same source kernel has the exact difference-of-scales form
\[
 e^{(a+b)/4}F(e^a,e^b)=P(a+b)-P(a-b).                 \tag{5}
\]
Thus prime scale and modular-clock distance are interchangeable arguments of one symmetric kernel; no Xi zero is needed for this identity.

The kernel has an exact **vacuum versus arithmetic-tail split**. For \(t\ge0\), write
\[
 V(t)=e^{t/4},\qquad
 R(t)=e^{t/4}(\Theta(e^t)-1)
     =2\sum_{n\ge1}e^{t/4-\pi n^2e^t},
 \qquad P(t)=V(t)+R(t).
\]
The arithmetic tail is positive and strictly decreasing on \(t\ge0\), since every summand has logarithmic derivative \(1/4-\pi n^2e^t<0\). Using the evenness of \(P\), equation (5) becomes
\[
 K(a,b):=P(a+b)-P(a-b)
   =\underbrace{V(a+b)-V(|a-b|)}_{K_{\rm vac}(a,b)}
    -\underbrace{[R(|a-b|)-R(a+b)]}_{K_{\rm arith}(a,b)},
 \quad a,b>0.                                        \tag{5a}
\]
Both displayed terms are pointwise positive, and the theorem says \(K_{\rm vac}>K_{\rm arith}\) entry by entry. The vacuum has the explicit positive Gram form
\[
 K_{\rm vac}(a,b)
   =\frac12\int_0^{\min(a,b)}
       e^{(a-s)/4}e^{(b-s)/4}\,ds.                    \tag{5b}
\]
No matrix inequality between \(K_{\rm vac}\) and \(K_{\rm arith}\) follows from entrywise order. This identifies the specific stronger comparison a spectral argument would need, without asserting that the comparison holds.

## Proof

Fix \(y>1\) and write \(F(q,y)=-C_q(y)=\Theta(qy)-y^{-1/2}\Theta(q/y)\). Jacobi inversion gives \(F(1,y)=0\). Termwise differentiation of the normally convergent theta series gives

\[
 \partial_qF(q,y)=2\pi\sum_{n\ge1}n^2
   \left[y^{-3/2}e^{-\pi n^2q/y}
                -y e^{-\pi n^2qy}\right].             \tag{6}
\]

Every bracket is strictly positive for \(q\ge1\). Indeed \(y-1/y>2\log y\) for \(y>1\): the difference vanishes at one and has derivative \((y-1)^2/y^2>0\). Therefore

\[
 \pi n^2q(y-1/y)>2\pi n^2q\log y>\tfrac52\log y,
\]

which is exactly \(e^{\pi n^2q(y-1/y)}>y^{5/2}\), the inequality between the two terms in each bracket of (6). Thus \(F(q,y)>0\) and increases strictly in \(q\). Symmetry (4) gives the strict increase in \(y\). For fixed \(y>1\), both theta factors in \(F(q,y)\) tend to one as \(q\to\infty\), proving (3).

At \(y=1\), (1) vanishes. Since \(S^2=1\) and \(S\Theta=\Theta\), the definition gives \(SC_q=-C_q\). Applying that relation at \(y\) and \(1/y\) transfers the sign, scale monotonicity and endpoint from \(y>1\) to \(0<y<1\), proving (2)–(3).

The series for \(R\) and its derivative converge normally on compact positive intervals, so the termwise monotonicity used in (5a) is justified. Integrating the elementary exponential in (5b) gives \(e^{(a+b)/4}-e^{|a-b|/4}\), proving the Gram identity.

## Two-scale Laplace pairing

The exchange symmetry makes a second exact operation possible. For \(\lambda>1/4\), define
\[
 L(\lambda)=\int_0^\infty e^{-\lambda t}P(t)\,dt,\qquad
 G(\lambda)=\lambda L(\lambda).
\]
The integral converges because \(P(t)=O(e^{t/4})\). For distinct \(\lambda,\mu>1/4\), Fubini and the two regions \(a>b\), \(b>a\) give
\[
\begin{aligned}
 \int_0^\infty\!\int_0^\infty
   e^{-\lambda a-\mu b}[P(a+b)-P(a-b)]\,da\,db
 &=\frac{L(\mu)-L(\lambda)}{\lambda-\mu}
   -\frac{L(\lambda)+L(\mu)}{\lambda+\mu}\\
 &=\frac{2[G(\mu)-G(\lambda)]}{\lambda^2-\mu^2}>0.
                                                        \tag{7}
\end{aligned}
\]
At \(\lambda=\mu\), the quotient has its continuous derivative value. The strict sign follows directly from (5), not from a zero hypothesis. In particular \(G\) decreases strictly on \((1/4,\infty)\).

This transform is tied to the *actual* one-sided theta connection, rather than an auxiliary source:
\[
 L(\lambda)=\frac{1}{\lambda-1/4}+M_{2i\lambda},
 \qquad
 M_z=\int_1^\infty
       y^{iz/2-3/4}(\Theta(y)-1)\,dy.                  \tag{8}
\]
The identity follows from \(y=e^t\), and \(M_z\) is the Mellin branch appearing in the exact formula for \(H(z)\) in the [Abel-pairing card](theta-rational-cusp-boundary-law.md). Thus the ordered prime–modular source becomes a divided-difference kernel of the one-sided connection branch. Positivity of each scalar value in (7) is weaker than positivity of every matrix built from those values; no operator-monotonicity or Xi-zero conclusion is asserted.

The Ward identity for that same branch simplifies further after substituting (8). With \(\Theta_1=\Theta(1)\),
\[
 \boxed{H(2i\lambda)
   =(\lambda^2-1/16)L(\lambda)-\lambda\Theta_1.}     \tag{9}
\]
For \(\lambda>1/4\) this is an equality of convergent integrals; both sides extend meromorphically, with the apparent pole at \(\lambda=1/4\) cancelled by its prefactor. Adding the \(\lambda\) and \(-\lambda\) versions cancels the seam term exactly:
\[
 \boxed{\Xi(2i\lambda)
   =(\lambda^2-1/16)\,[L(\lambda)+L(-\lambda)].}      \tag{10}
\]
Equation (10), interpreted by analytic continuation at the two apparent poles, is an exact two-ended connection formula. It makes the conceptual gap precise: (7) orders \(L\) on the real half-line \(\lambda>1/4\), while RH requires zero control of its *reflected sum* in the complex strip around \(\operatorname{Re}\lambda=0\). The real-axis order alone does not cross that gap.

## Gaussian quadrature defect and signed sine representation

The matrix question for (5) has an exact source answer. For \(t\in\mathbb R\), put \(y=e^{|t|}\) and
\[
 B(t)=e^{-|t|/4}-e^{|t|/4}(\Theta(y)-1).
\]
This is an even, strictly positive, integrable function. More precisely, the Gaussian integral and the unit-interval quadrature identity give
\[
 \begin{aligned}
 B(t)
 &=2y^{1/4}\left[\int_0^\infty e^{-\pi yx^2}\,dx
                    -\sum_{n\ge1}e^{-\pi yn^2}\right]\\
 &=4\pi y^{5/4}\int_0^\infty\{x\}x e^{-\pi yx^2}\,dx>0.       \tag{11}
 \end{aligned}
\]
Here \(\{x\}\) is the fractional part. On each interval \([n-1,n]\), the Gaussian is strictly decreasing, so its integral exceeds its right-endpoint value; summing proves positivity independently of the displayed fractional-part formula. The latter follows by writing \(f(x)-f(n)=\int_x^n[-f'(u)]\,du\) and exchanging the two integrals. Thus \(B\) is the *positive continuum-minus-lattice Gaussian discrepancy*, not an arbitrary correction added to the theta source.

Since \(P(t)=2\cosh(t/4)-B(t)\), equation (10) determines the Fourier transform of this discrepancy exactly. With \(\widehat B(\tau)=\int_{\mathbb R}B(t)e^{-i\tau t}\,dt\),
\[
 \boxed{\widehat B(\tau)=\frac{\Xi(2\tau)}{\tau^2+1/16}}
 \qquad(\tau\in\mathbb R).                                      \tag{12}
\]
Indeed \(L(\lambda)=1/(\lambda-1/4)+\int_0^\infty e^{-\lambda t}R(t)\,dt\). At \(\lambda=i\tau\), the sum of its two analytically continued branches is
\(-[\frac{1/2}{\tau^2+1/16}-2\int_0^\infty R(t)\cos(\tau t)\,dt]=-\widehat B(\tau)\); substituting in (10) proves (12). The distinction between the convergent \(B\)-integral and the analytically continued vacuum integrals is essential.

Fourier inversion now turns the same prime–modular commutator kernel into
\[
 \boxed{K(a,b)=4\sinh(a/4)\sinh(b/4)
       +\frac{2}{\pi}\int_0^\infty
          \frac{\Xi(2\tau)}{\tau^2+1/16}
          \sin(a\tau)\sin(b\tau)\,d\tau.}             \tag{13}
\]
The integral converges absolutely: \(B\) is smooth, its first two derivatives are integrable, and two integrations by parts give \(\widehat B(\tau)=O((1+|\tau|)^{-2})\). Formula (13) follows from
\(2\cosh((a+b)/4)-2\cosh((a-b)/4)=4\sinh(a/4)\sinh(b/4)\) and
\(\cos((a-b)\tau)-\cos((a+b)\tau)=2\sin(a\tau)\sin(b\tau)\).

Consequently, for any finite real coefficients \(c_j\) and positive scales \(a_j\), the full quadratic form is exactly
\[
 \sum_{j,k}c_jc_kK(a_j,a_k)
 =4\left(\sum_jc_j\sinh(a_j/4)\right)^2
 +\frac{2}{\pi}\int_0^\infty
       \frac{\Xi(2\tau)}{\tau^2+1/16}
       \left(\sum_jc_j\sin(a_j\tau)\right)^2d\tau.  \tag{14}
\]
This is a source-derived **rank-one boundary channel plus signed critical-line spectral channel**. It is the matrix-level output of the preceding scalar commutator law. Positivity of \(B\) in (11) means \(\widehat B\) is a positive-definite *function* of frequency; it does not mean \(\widehat B(\tau)\) is pointwise nonnegative. The remaining RH obstacle is to control the analytic continuation of this signed channel together with the boundary rank one, not merely to strengthen the scalar inequality (7). No off-line-zero exclusion follows from (11)–(14).

**[PROVED HERE, using Hardy's sign theorem]** On the full continuum of positive scales, the kernel \(K\) has *infinite positive and infinite negative index*: for every \(m\), some finite Gram matrix \((K(a_j,a_k))\) has a positive definite \(m\)-dimensional subspace, and some finite Gram matrix has a negative definite \(m\)-dimensional subspace. This is compatible with \(K(a,b)>0\) for every \(a,b>0\). The sign input is classical Hardy sign change, stated in [DLMF §25.10](https://dlmf.nist.gov/25.10); the corpus also proves cofinal positive and negative Xi signs through [`false_of_hardyXiDensity_tail_sign`](../../../../formal/GaloisForLFunctions/RHTower/HardyTheorem.lean) and its two Xi sign specializations.

Here is the index proof. Let \(w(\tau)=\widehat B(\tau)\). Continuity and the two Xi signs supply compact intervals \(J_+\), \(J_-\subset(0,\infty)\) and \(\varepsilon>0\) with \(w\ge\varepsilon\) on \(J_+\) and \(w\le-\varepsilon\) on \(J_-\). For real \(g\in C_c^\infty(0,\infty)\), (14) extends by integration to
\[
 Q(g)=4\left(\int_0^\infty g(a)\sinh(a/4)\,da\right)^2
    +\frac2\pi\int_0^\infty w(\tau)
       \left|\int_0^\infty g(a)\sin(a\tau)\,da\right|^2d\tau. \tag{15}
\]
The zero-boundary-moment test functions are dense in \(L^2(0,\infty)\): take any compactly supported smooth test \(g\), then subtract its moment times a smooth bump translated to \(A\) and normalized to have \(\sinh(a/4)\)-moment one. The normalized bump's \(L^2\)-norm tends to zero like \(e^{-A/4}\). The Fourier sine transform is unitary up to normalization, and the multiplier \(w\) is bounded. Hence the signed second term in (15), restricted to zero-moment tests, approximates the strictly positive or strictly negative form on any prescribed finite-dimensional subspace of \(L^2(J_+)\) or \(L^2(J_-)\). Strict definiteness survives sufficiently close approximation. Finally, approximate the finitely many compactly supported test integrals by common Riemann sums; continuity of \(K\) preserves each strict Gram signature and yields finite scale sets. This proves both indices are infinite without computing any Xi values.

The restriction to **actual prime-deletion scales** still has both infinite indices. Set \(a_p=2\log p\). For every \(m\), there is a finite set of distinct primes whose matrix \((K(a_p,a_q))\) has positive index at least \(m\), and there is one whose matrix has negative index at least \(m\). This strengthens the full-scale statement and settles the prime-sampled positivity conjecture for the kernel (5).

To prove it, first use the identity
\[
 K(A+x,A+y)=4\sinh((A+x)/4)\sinh((A+y)/4)
                  +B(x-y)-B(2A+x+y).                 \tag{16}
\]
The convolution form \(B(x-y)\) on \(L^2(0,\infty)\) has both infinite indices. Indeed, for a point \(\tau_0\) inside either strict-sign interval of \(w=\widehat B\), long real wave packets \(g_L(x)=L^{-1/2}\chi(x/L)\cos(\tau_0x)\), with \(\chi\in C_c^\infty(1,2)\), have Fourier mass concentrated at \(\pm\tau_0\). Several distinct \(\tau_0\) in the same interval give arbitrarily large definite subspaces. The subspace of compactly supported tests with \(\int g(x)e^{x/4}\,dx=0\) is dense in \(L^2(0,\infty)\): cancel any such moment with a sufficiently remote, normalized bump whose \(L^2\)-norm tends to zero. Hence the sign survives this one linear constraint.

For a constrained test \(g\), translate its support by \(A\). In the quadratic form of (16), the rank-one term is exactly \(e^{-A/2}(\int g(x)e^{-x/4}\,dx)^2\), because the growing \(e^{A/4}\) component has zero moment. The \(B(2A+x+y)\) term tends uniformly to zero on the fixed compact support. Thus the translated quadratic form tends to the definite convolution form; this holds simultaneously on any chosen finite-dimensional subspace. Approximate its test integrals by finitely many point masses, adjusting one coefficient to preserve the exact \(e^{x/4}\)-moment constraint. The prime number theorem implies that the set \(\{2\log p:p\text{ prime}\}\) becomes an arbitrarily fine net on every fixed-length interval translated far enough right: \(\pi((1+\delta)X)-\pi(X)\sim\delta X/\log X>0\) for fixed \(\delta>0\). The needed prime-counting asymptotic is already in [`tendsto_primeCounting_nat_ratio`](../../../../formal/GaloisForLFunctions/RHTower/WoldBooleanAcceleratedType.lean). Move each point mass to a nearby prime scale, readjust the one coefficient, and use continuity and the strict signature margin. This produces the asserted prime matrices. No numerical zero or prime computation enters the proof.

## Whole-chain consequence and next test

This is a strict, source-native orientation of prime deletion against modular inversion, obtained before any Mellin transform or Xi zero is selected. The theta boundary potential \(Q(r)=\sum_{n\ge1}e^{-i\pi n^2r}/n^2\) from the [rational-cusp and Abel-pairing card](theta-rational-cusp-boundary-law.md) obeys an all-prime trace law, but that law merely reconstructs its coefficients. The commutator (1) instead measures the failure of two source operations to commute at the modular seam. It may feed an ordered two-ended connection argument for WS2 or a source-current argument for L/PSRC/SQB.

The order (2)–(4) and scalar divided-difference sign (7) do **not** imply RH. Equations (11)–(16) identify the precise matrix output and show infinite inertia even at actual prime scales: a rank-one vacuum port and a sine transform weighted by the actual critical-line Xi values. This changes the viable framework from an ordinary positive Gram to a signed spectral space with a boundary port. A useful next conjecture must orient the *complex continuation* of that signed channel using an independent theta or arithmetic identity. Pointwise positivity and scalar monotonicity alone do not constrain common Xi zeros. No zero exclusion is claimed here.

This theorem is formalized in Lean (see the certificate); it has not been independently audited for literature novelty. The frontier map remains read-only.

## Log
- 2026-09-27 — all results formalized unconditionally: commutator formulas, atom deletion, sign pattern, derivative law (6), bounds and limits, exchange symmetry, log-coordinate kernel with vacuum/arithmetic split and Gram form, two-scale Laplace pairing with positivity and diagonal value, Laplace–Mellin identity (8), Ward forms (9)–(10), quadrature defect (11) with fractional-part formula, `B̂ = Ξ(2τ)/(τ²+1/16)` (12), spectral kernel (13)–(15), translated kernel (16), and infinite positive/negative index on the continuum and at prime scales (Hardy sign change, Poisson summation, Cesàro/Toeplitz, PNT short intervals); moved to 3-formalized.
