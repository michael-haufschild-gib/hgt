# Theta Xi as a positive-renewal phase level

- **Stage:** 2-fully-proven (paper proof; Lean formalization open)
- **Type:** exact two-ended factorization and reflection law
- **Routes:** SQB, WS2; source-side connection for the theta one-port
- **Dependency:** the standard Jacobi theta transformation and the exact Xi Mellin identity in [theta-prime-modular-commutator-crossing.md](theta-prime-modular-commutator-crossing.md).

## Statement

Put \(a=1/4\), \(\Theta(y)=\sum_{n\in\mathbb Z}e^{-\pi n^2y}\),
\(c=\Theta(1)\), and

\[
 P(t)=e^{at}\Theta(e^t),\qquad
 R(t)=P(t)-e^{at}\quad(t\geq0).
\]

The theta transformation makes \(P\) even. Its *renewal increment* is

\[
 \nu(t)=aP(t)-P'(t)
   =2\pi\sum_{n\geq1}n^2e^{(a+1)t-\pi n^2e^t}>0\quad(t\geq0).
\]

Let \(v(t)=e^{at}\nu(t)/c\), \(q=\int_0^\infty v(t)\,dt\), and use ordinary
one-sided convolution to define

\[
 Q(t)=\sum_{m\geq1}\frac{1}{m c^m}\nu^{*m}(t),\qquad t\geq0. \tag{1}
\]

Put \(\beta=\pi-3/2>3/2\). Then \(q<1/6\), \(Q(t)>0\),
\(\int_0^\infty e^{at}Q(t)\,dt=-\log(1-q)<1/5\), and

\[
 0<Q(t)\leq e^{-\beta t}\frac{1-e^{-at}}{t}
       \leq a e^{-\beta t}. \tag{2}
\]

At \(t=0\), the middle expression has value \(a\).
The convolution series has a real-analytic continuation \(Q^\dagger\) along the
whole real axis. Its reflection is **exactly**

\[
 \boxed{Q^\dagger(-t)+Q(t)=\frac{2\sinh(at)}{t}\quad(t>0).} \tag{3}
\]

At zero the right side has value \(2a\). In particular \(Q^\dagger(-t)>0\),
and (2)--(3) give the universal negative-end asymptotic
\(Q^\dagger(-t)\sim e^{at}/t\) as \(t\to\infty\). The positive renewal branch
decays, while its analytic negative branch necessarily carries a growing
boundary datum.

The renewal density also obeys the positive Volterra law
\[
 c\,tQ(t)=t\nu(t)+\int_0^t \nu(s)(t-s)Q(t-s)\,ds. \tag{3a}
\]
Define \(W(t)=e^{-at}/t+Q(t)>0\) for \(t>0\). Equation (3) says that its
analytic continuation across the simple pole at zero is **odd**:
\(W^\dagger(-t)=-W(t)\). The elementary Frullani identity gives
\[
 \eta(\lambda)+S(\lambda)
   =\int_0^\infty W(t)\sinh(\lambda t)\,dt
   \quad(|\operatorname{Re}\lambda|<a), \tag{3b}
\]
with convergence at zero because \(\sinh(\lambda t)=O(t)\). Thus the entire
two-ended zero problem is encoded by one positive, odd boundary kernel.

For \(|\operatorname{Re}\lambda|<a\), define the convergent transforms

\[
 C(\lambda)=\int_0^\infty Q(t)\cosh(\lambda t)\,dt,\qquad
 S(\lambda)=\int_0^\infty Q(t)\sinh(\lambda t)\,dt,
\]

and the principal analytic branch
\(\eta(\lambda)=\tfrac12[\log(a+\lambda)-\log(a-\lambda)]\). Then

\[
 \boxed{\Xi(2i\lambda)=
 \frac{2ac\,e^{-C(\lambda)}}{\cosh\eta(\lambda)}
 \cosh\bigl(\eta(\lambda)+S(\lambda)\bigr).} \tag{4}
\]

The prefactor is analytic and nowhere zero in this strip. Moreover
\(|\operatorname{Im} S(\lambda)|<1/5\). Hence, in its upper half,

\[
 \boxed{\Xi(2i\lambda)=0
 \quad\Longleftrightarrow\quad
 \eta(\lambda)+S(\lambda)=i\pi/2.} \tag{5}
\]

The lower-half condition is the reflected level \(-i\pi/2\). There are no
other hyperbolic-cosine levels available in the critical strip. On the real
frequency axis, (4) becomes the explicit amplitude--phase factorization

\[
 \boxed{\Xi(2\tau)=2c\sqrt{a^2+\tau^2}
  \exp\!\left[-\int_0^\infty Q(t)\cos(\tau t)\,dt\right]
  \cos\!\left[\arctan(\tau/a)
       +\int_0^\infty Q(t)\sin(\tau t)\,dt\right].} \tag{6}
\]

All positive real-frequency Xi zeros are crossings of **one** phase level,
with the negative-frequency zeros obtained by reflection. RH is now the
assertion that the complex level in
(5) has no point away from the imaginary \(\lambda\)-axis. Equations
(1)--(6) do **not** establish that assertion.

## Paper proof

Theta reflection gives \(P'(0)=0\), hence \(v(0)=\nu(0)/c=a\).
Each positive theta summand of \(v\) has logarithmic derivative
\(1+2a-\pi n^2e^t\leq-\beta\) for \(t\geq0\). Therefore
\(0<v(t)\leq a e^{-\beta t}\) and
\(q\leq a/\beta<1/6\). The weighted convolution norm makes (1)
absolutely convergent and gives
\(\int e^{at}Q=\sum_{m\geq1}q^m/m=-\log(1-q)
\leq q/(1-q)<1/5\). Moreover
\(v^{*m}(t)\leq a^m e^{-\beta t}t^{m-1}/(m-1)!\).
Summing these bounds with the coefficient \(1/m\), and then multiplying
by \(e^{-at}\), proves (2).
Multiplying (1) by \(t\) and using
\(t(f*g)=(tf)*g+f*(tg)\) proves (3a) term by term.

For \(\operatorname{Re}\lambda>a\), put
\(L(\lambda)=\int_0^\infty e^{-\lambda t}P(t)\,dt\).
Integration by parts gives

\[
 D(\lambda):=(\lambda-a)L(\lambda)
   =c-\widehat\nu(\lambda)
   =c\exp[-\widehat Q(\lambda)]. \tag{7}
\]

The last equality extends to \(\operatorname{Re}\lambda\geq-a\):
\(|\widehat\nu(\lambda)/c|\leq q<1\), so the logarithmic convolution
series converges uniformly there. In particular \(D\) has no zero in
that half-plane. The exact Mellin formula from the dependency card is

\[
 \Xi(2i\lambda)=(a+\lambda)D(\lambda)
                    +(a-\lambda)D(-\lambda). \tag{8}
\]

Substitute (7), use
\(\widehat Q(\lambda)=C(\lambda)-S(\lambda)\), and note that
\(\tanh\eta=\lambda/a\). This gives (4); its restriction to
\(\lambda=i\tau\) gives (6). In the upper half-strip,
\(0<\operatorname{Im}\eta<\pi/2\), while
\(|\operatorname{Im} S|\leq\int e^{at}Q<1/5\). Only the \(i\pi/2\)
zero of \(\cosh\) lies in that imaginary range, proving (5).

For (3), the series (1) extends real-analytically through zero: write
each convolution as an integral over a fixed simplex after scaling its
variables by \(t\). On compact complex neighborhoods of any real segment,
the theta series is analytic and bounded, while the \(m\)-th simplex
term is bounded by a constant to power \(m\) times
\(|t|^{m-1}/(m-1)!\); thus the logarithmic series converges locally
normally. Since \(P\) is even and analytic at zero, repeated integration
by parts as \(\lambda\to+\infty\) gives

\[
 \lambda L(\lambda)/c
 \sim1+\sum_{j\geq1}\frac{P^{(2j)}(0)/c}{\lambda^{2j}}.
\]

Thus the odd inverse-power coefficients of
\(\log(D(\lambda)/c)=\log(1-a/\lambda)
 +\log(\lambda L(\lambda)/c)\) come entirely from the first term.
On the other hand (7) and the Laplace endpoint expansion give
\(\widehat Q(\lambda)\sim\sum_{j\geq0}Q^{(j)}(0)/\lambda^{j+1}\).
Coefficient comparison yields
\(Q^{(2j)}(0)=a^{2j+1}/(2j+1)\) for every \(j\). Their Taylor series is
\(\sinh(at)/t\). The real-analytic identity theorem extends the resulting
even-germ identity to every real \(t\), proving (3).
Finally \(2\sinh(at)/t\geq2a>a\geq Q(t)\), so (3) makes the
negative branch positive. Equation (2) then gives its stated asymptotic.
The relation \(W^\dagger(-t)=-W(t)\) follows by substituting (3);
integrating \(e^{-at}\sinh(\lambda t)/t\) gives \(\eta(\lambda)\), proving
(3b).

## Modular ODE controls the non-universal germ

The even Taylor germ of \(Q\) is fixed by (3). The first odd coefficient
has a direct source value:
\[
 \boxed{Q'(0)=\frac{a^2}{2}-\frac{P''(0)}{c}
       =\frac{5-\pi^2 c^8}{32}<0.} \tag{9}
\]
Indeed the \(m=1,2\) terms of (1) give
\(Q'(0)=\nu'(0)/c+\nu(0)^2/(2c^2)\); higher convolution powers vanish
to order at least two. Since \(\nu=aP-P'\), \(P'(0)=0\), and
\(\nu(0)=ac\), the first equality follows.

For the second, put \(H(x)=P(2x)\). The [Lean-proved modular differential
closure](../../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaModularDifferentialClosure.lean)
has normalized state variables \(Z,R,S\) with
\(H'=-HS/6\) and
\(S'=3-S^2/3-(3/4)R^2(1-Z^2)\).
At the self-dual point \(x=0\), its initial data are
\(Z=S=0\), \(R=\pi c^4\). Consequently
\[
 \frac{P''(0)}{c}=\frac14\frac{H''(0)}{H(0)}
   =-\frac18+\frac{\pi^2c^8}{32},
\]
which proves (9); \(c>1\) and \(\pi>3\) make its sign strict.
Repeated differentiation of the same finite polynomial ODE, followed
by the formal logarithm in (7), recursively determines **every odd
Taylor coefficient of \(Q\)** from the single self-dual parameter
\(\pi c^4\). This is a paper-level bridge from the existing Lean ODE to
the new renewal phase; the coefficient formula and recurrence have
not been formalized.

## The next producer question

The universal reflection (3) fixes every even Taylor coefficient of
the renewal phase kernel. The theta-specific data are its odd germ,
equivalently the even derivatives of \(P\) at the modular seam; the
existing finite modular ODE generates them all. The
remaining mathematical obstacle is to derive from the literal theta
atoms a complex level-set law excluding
\(\eta(\lambda)+S(\lambda)=i\pi/2\) when
\(\operatorname{Re}\lambda\ne0\), without replacing it by a generic
positivity or real-axis monotonicity statement. The source search found
the existing one-sided Mellin, theta-log-concavity, and prime-translation
identities, but no such level-set law. The theorem above is paper only;
none of (1)--(6) is asserted Lean-closed.
