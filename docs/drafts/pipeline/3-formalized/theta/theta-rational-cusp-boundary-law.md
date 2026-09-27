# Rational-cusp boundary law for the completed theta source

- **Stage:** 3-formalized. Lean: `GaloisForLFunctions.RHTower.ThetaRationalCuspBoundary`, `ThetaCuspOneSidedConnection`, `ThetaCuspAbelBoundaryPairing` (+ `QuadraticGaussSumFourthPower`), see `theta-rational-cusp-boundary-law-formalized.md`
- **Type:** THEOREM (paper and Lean)
- **Route:** TQFQ/WS2 connection coefficient.
- **Scope:** A theorem about the actual completed theta source at its complex-clock boundary. It does not locate Xi zeros.

## Source and exact boundary value

Let

\[
 \vartheta(y)=\sum_{n\in\mathbb Z}e^{-\pi n^2y}\quad(\Re y>0),
 \qquad
 \kappa(y)=y^{5/4}\bigl(2y\vartheta''(y)+3\vartheta'(y)\bigr),
\]

with the principal power in the right half-plane. The source already used in the Xi Fourier representation is exactly
\(k(x)=\kappa(e^{2x})\) for \(|\Im x|<\pi/4\). Indeed, differentiating the absolutely convergent theta series gives

\[
 k(x)=2\pi e^{5x/2}\sum_{n\ge1}n^2
       (2\pi n^2e^{2x}-3)e^{-\pi n^2e^{2x}}.
\]

Fix coprime positive integers \(p,q\) with \(q\) odd, and put
\(y_0=2ip/q\) and
\(G_{p,q}=\sum_{r\bmod q}e^{-2\pi i p r^2/q}\). Then

\[
 \boxed{\displaystyle
 \lim_{\varepsilon\downarrow0}\varepsilon^{5/2}
   \kappa(y_0+\varepsilon)
   =\frac{3G_{p,q}}{2q}\,y_0^{9/4},
 \qquad |G_{p,q}|=\sqrt q.} \tag{1}
\]

In particular, the source is unbounded on approach to each of these rational points of the upper complex-clock boundary. They are dense on that boundary. The lower boundary has the conjugate statement. Hence the strip \(|\Im x|<\pi/4\) is a *natural boundary for the source as a holomorphic function*: it admits no holomorphic continuation across any boundary point. This is stronger than the corpus's existing theorem that the displayed atom series is not summable beyond the strip.

## Proof

At \(y=y_0+\varepsilon\), the phase \(e^{-2\pi i p n^2/q}\) is periodic modulo \(q\). Splitting the Gaussian series into residue classes and applying Poisson summation to each class gives

\[
 \vartheta(y_0+\varepsilon)
 =\frac1{q\sqrt\varepsilon}
   \sum_{\ell\in\mathbb Z}
   G_{p,q}(\ell)e^{-\pi\ell^2/(q^2\varepsilon)},
 \quad
 G_{p,q}(\ell)=\sum_{r\bmod q}
  e^{-2\pi i p r^2/q}e^{2\pi i\ell r/q}.
\]

The \(\ell=0\) term is \(G_{p,q}/(q\sqrt\varepsilon)\). Since \(|G_{p,q}(\ell)|\le q\), the remaining series and its first two \(\varepsilon\)-derivatives are exponentially small compared with every fixed power of \(1/\varepsilon\). Consequently

\[
 \vartheta'= -\frac{G_{p,q}}{2q}\varepsilon^{-3/2}
  +o(\varepsilon^{N}),\qquad
 \vartheta''=\frac{3G_{p,q}}{4q}\varepsilon^{-5/2}
  +o(\varepsilon^{N})
\]

for any fixed \(N>0\) after interpreting the error as the differentiated exponential remainder. Substitution into \(2y\vartheta''+3\vartheta'\) cancels the two \(\varepsilon^{-3/2}\) terms exactly, leaving
\((3G_{p,q}/2q)y_0\varepsilon^{-5/2}\) plus an exponentially small remainder. Since \(y^{5/4}\to y_0^{5/4}\), this proves the limit in (1).

For the magnitude, expand \(|G_{p,q}|^2\) and change variables
\((r,s)\mapsto(u,v)=(r-s,r+s)\) modulo odd \(q\). This is a bijection, and the exponent becomes \(-2\pi i p uv/q\). The inner sum over \(v\) vanishes unless \(u=0\), because \(p\) is invertible modulo \(q\). It equals \(q\) at \(u=0\); hence \(|G_{p,q}|^2=q\). Rational numbers \(2p/q>0\) with odd denominator are dense. The map \(x\mapsto e^{2x}\) is locally biholomorphic at the boundary, so (1) gives the natural-boundary claim.

The same Poisson calculation applies for every coprime \(p,q>0\), with limit \(L_{p,q}=(3G_{p,q}/2q)y_0^{9/4}\), whether or not the Gauss sum vanishes. The [classical quadratic Gauss-sum square law](https://www.mathnet.ru/php/archive.phtml?jrnid=im&option_lang=eng&paperid=9330&wshow=paper) gives \(G_{p,q}^2=q\chi_4(q)\) for odd \(q\), \(G_{p,q}=0\) for \(q\equiv2\pmod4\), and \(G_{p,q}^2=2qi\chi_4(-p)\) for \(4\mid q\), with the last sign depending on the convention in the exponential. The convention-independent fourth-power consequence is
\[
 \frac{L_{p,q}^4}{i}=\frac{81}{16q^2}
     \left(\frac{2p}{q}\right)^9
 \begin{cases}
  1,&q\text{ odd},\\
  0,&q\equiv2\pmod4,\\
 -4,&4\mid q.
 \end{cases} \tag{1a}
\]
Thus the *local* completed-source boundary amplitudes carry a three-valued arithmetic charge modulo four. It is a phase classification, not a positivity statement about their global Abel sum.
At the zero-charge points \(q\equiv2\pmod4\), the \(\ell=0\) Poisson term vanishes and the exponentially small remainder shows \(\kappa(y_0+\varepsilon)\to0\), despite singular behavior at arbitrarily nearby rational points of odd denominator. In particular, the endpoint \(y_0=i\) of the unit-circle arc in (2) is a zero-charge point; the difficulty in taking \(\phi\uparrow\pi/2\) lies along the entire ray, not solely at its initial endpoint.

## What changes in the proof chain

The high-frequency saddle of a single theta atom approaches \(\Im x=\pi/4\), precisely where the completed source has the dense rational-cusp amplitudes (1). Its leading boundary phase is a *quadratic Gauss sum*, not the phase of the first atom. Any contour attack on the left/right connection coefficient must retain these phases and the Abel limit from inside the strip. A pointwise first-atom comparison or a smooth boundary-phase inequality cannot be transported to the saddle.

There is an exact route from this boundary to the existing one-port connection. For
\(H(z)=\int_0^\infty k(x)e^{izx}\,dx\), put
\(F_z(y)=y^{iz/2-1}\kappa(y)\). The real change of variables \(y=e^{2x}\) gives
\[
 H(z)=\frac12\int_1^\infty F_z(y)\,dy.
\]
For every fixed \(0<\phi<\pi/2\), Cauchy's theorem and exponential decay in the closed sub-sector give the **exact** rotated connection branch
\[
 \boxed{\displaystyle
 H(z)=\frac12\left(
   i\int_0^\phi e^{i\theta}F_z(e^{i\theta})\,d\theta
   +e^{i\phi}\int_1^\infty F_z(re^{i\phi})\,dr
 \right).} \tag{2}
\]
The same formula with \(-z\) gives the other branch; \(\Xi(z)=H(z)+H(-z)\), and the two-ended source modes still satisfy
\(U_z(x)-V_z(x)=-ie^{-izx}\Xi(z)\). Thus (2) transports the actual connection coefficient to rays approaching the Gauss-cusp boundary, with no zero assumption. The two terms on the right of (2) have to be kept together as \(\phi\uparrow\pi/2\); (1) precludes a naive pointwise boundary substitution on the ray.

## The global Abel pairing exists after the Ward reduction

The corpus already proves the positive-tail identities
\(T(x)=e^{x/2}(\vartheta(e^{2x})-1)/2\),
\(k=T''-T/4\), and \(T'(0)=-1/4\)
in `ThetaCuspReflection.lean`. Integrating the one-sided connection branch twice by parts gives, for every complex \(z\),
\[
 \boxed{\displaystyle
 H(z)=\frac14+\frac{iz}{2}(\vartheta(1)-1)
       -\frac{z^2+1/4}{4}M_z,
 \quad
 M_z=\int_1^\infty y^{\alpha_z}(\vartheta(y)-1)\,dy,
 \quad \alpha_z=\frac{iz}{2}-\frac34.} \tag{3}
\]
The integral is entire in \(z\), by the Gaussian decay as \(y\to+\infty\). The odd linear seam term cancels between \(H(z)\) and \(H(-z)\), so
\[
 \Xi(z)=\frac12-\frac{z^2+1/4}{4}(M_z+M_{-z}). \tag{4}
\]
The real-frequency cosine version of (4) is already proved in `ThetaCuspFourierXi.lean`; (3) retains the one-sided phase needed by the WS2 connection.

There is now a **global** boundary formula, rather than only the local cusp law (1). For any \(\alpha\) with \(\Re\alpha<0\), put
\[
 A(\alpha)=i\int_0^{\pi/2}e^{i(\alpha+1)\theta}
       (\vartheta(e^{i\theta})-1)\,d\theta,
 \qquad
 I_n(\alpha)=\int_1^\infty r^\alpha e^{-i\pi n^2r}\,dr.
\]
Then the exact contour-rotation identity is
\[
 \boxed{\displaystyle
 M_z=A(\alpha_z)+2e^{i\pi(\alpha_z+1)/2}
          \sum_{n\ge1}I_n(\alpha_z),
 \qquad \Im z>-3/2.} \tag{5}
\]
The oscillatory integral \(I_n\) converges, and its sum converges **absolutely**. Indeed, integration by parts, using \(e^{-i\pi n^2}=(-1)^n\), gives
\[
 I_n(\alpha)=\frac{(-1)^n}{i\pi n^2}
   +\frac{\alpha}{i\pi n^2}
      \int_1^\infty r^{\alpha-1}e^{-i\pi n^2r}\,dr,
 \qquad
 |I_n(\alpha)|\le\frac1{\pi n^2}
        \left(1+\frac{|\alpha|}{-\Re\alpha}\right). \tag{6}
\]
The same bound holds uniformly for the damped ray integrals with
\(e^{-\pi n^2 e^{i\phi}r}\), \(0\le\phi<\pi/2\). Dominated convergence therefore passes the theta series through the limit \(\phi\uparrow\pi/2\). The arc has a finite endpoint: writing \(w=e^{i\theta}-i\), the twisted Poisson identity
\(\vartheta(i+w)=w^{-1/2}\sum_{m\in\mathbb Z}e^{-\pi(m+1/2)^2/w}\)
shows \(\vartheta(e^{i\theta})\to0\) as \(\theta\uparrow\pi/2\), because \(\Re(1/w)\to+\infty\). Cauchy's theorem at each interior angle then proves (5).

Formula (5) applies simultaneously to \(M_z\) and \(M_{-z}\) throughout \(|\Im z|<3/2\), including the full nontrivial Xi zero strip. It retains every integer-square phase. The first boundary term in (6) is explicitly alternating and summable; its sum is \(\sum_{n\ge1}(-1)^n/n^2=-\pi^2/12\). The nonlocal remainder, arc term, and opposite branch remain essential. Thus existence of the Abel pairing is **closed on paper**; its source-specific complex phase orientation is the unresolved producer.

One further integration by parts places the whole boundary arithmetic in an ordinary **continuous** function. Define
\[
 Q(r)=\sum_{n\ge1}\frac{e^{-i\pi n^2r}}{n^2}.
\]
This series converges absolutely and uniformly, so \(Q\) is continuous, bounded and two-periodic. It has period mean zero, \(Q(1)=-\pi^2/12\), and the exact square-frequency parity law
\[
 Q(r+1)+Q(r)=\tfrac12Q(4r). \tag{7}
\]
Fubini is legitimate in the absolutely convergent remainder of (6), giving the stronger form of (5):
\[
 \boxed{\displaystyle
 M_z=A(\alpha_z)+2e^{i\pi(\alpha_z+1)/2}
  \left[\frac{i\pi}{12}
    +\frac{\alpha_z}{i\pi}
        \int_1^\infty r^{\alpha_z-1}Q(r)\,dr\right],
 \qquad \Re\alpha_z<0.} \tag{8}
\]
The final integral is absolutely convergent because \(Q\) is bounded and \(\Re\alpha_z<0\). Thus the dense Gauss-cusp singularities of the source are integrated into a continuous quadratic-phase potential before the source-sensitive connection phase is tested. Equation (7) is a concrete arithmetic constraint on that potential; neither its pointwise sign nor a sign for the weighted integral in (8) has been proved.

Classical theta/Poisson and quadratic Gauss-sum methods underlie the local proof, and the Ward identities used in (3) are already in Lean. No claim of literature novelty is made for the local rational-cusp asymptotic without a separate audit. The global one-sided boundary representations (5) and (8) are formalized; they have not been independently novelty-audited.

## Log
- 2026-09-27 — all displayed results formalized unconditionally: local cusp limit (1) for all p,q>0, |G|=√q, Gauss square law and charge (1a), zero-charge limit, natural boundary on both edges; Ward reduction (3)–(4), rotated branch (2), Abel pairing (5), ray bounds (6), square-phase potential and parity (7), (8), twisted Poisson at y=i, U−V mode identity; moved to 3-formalized.
