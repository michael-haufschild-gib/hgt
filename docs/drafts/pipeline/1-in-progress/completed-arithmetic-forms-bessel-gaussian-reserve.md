# A Gaussian lower reserve inside the physical Bessel band

Target for the literal Schläfli source:
\[
K_{i\tau}(a)\ge e^{-\tau^2/a}K_0(a)>0,
\qquad a>0,\quad |\tau|\le a.
\]
This would turn the established positive physical Wigner band into a
quantitative Gaussian density reserve, including its signed argument derivative.

Let $f(x)=K_{i\tau}(x)$, $g(x)=K_0(x)$, and
$h(x)=e^{-\tau^2/x}g(x)$. The argument operator is
\[
L_\tau y=(xy')'-(x-\tau^2/x)y.
\]
Its exact candidate-barrier identity is
\[
L_\tau h=\frac{\tau^2e^{-\tau^2/x}}x
\left[2g'+\left(1-x^{-1}+\tau^2x^{-2}\right)g\right].
\]
The literal integral gives $g'\le-g$, hence $L_\tau h\le0$ on
$x\ge|\tau|$. The Wronskian $W=x(f'h-fh')$ then has
$W'=-fL_\tau h\ge0$. Exponential source decay gives $W(\infty)=0$,
so $f/h$ is nonincreasing. The normalization needed at infinity is
$K_{i\tau}(x)/K_0(x)\to1$ for each fixed real $\tau$.

That normalization follows from concentration at zero of the literal
Schläfli probability density. An exact stronger route is
\[
\int_0^\infty t^2e^{-x\cosh t}\,dt
\le\int_0^\infty t\sinh t\,e^{-x\cosh t}\,dt
=K_0(x)/x,
\]
which, with $1-\cos y\le y^2/2$, gives
$1-\tau^2/(2x)\le K_{i\tau}(x)/K_0(x)\le1$.
The integration-by-parts boundary terms and weighted integrability are
required literal-source obligations.

A linear rank horizon would additionally require a polynomial-weighted
estimate for the signed transform outside this band. The positive-band
lower bound alone does not establish that horizon.

The exact complex-order recurrence can pay the required first moment without
a fresh boundary integration: differentiate
$K_{\nu+1}=K_{\nu-1}+2\nu K_\nu/x$ at $\nu=0$ and use
$K_{-\nu}=K_\nu$. The result is
$\partial_\nu K_\nu(x)|_{\nu=1}=K_0(x)/x$; its literal source derivative is
$\int_0^\infty t\sinh t\,e^{-x\cosh t}\,dt$.

For a polynomial of degree $N$, the Gaussian reserve is concentrated at
frequencies of order $\sqrt{aN}$. The contour shift by $\pi/3$ supplies an
outer-frequency envelope $e^{-a/2-\pi|\tau|/3}$, with the argument derivative
paid by the corresponding order-one integral. At $|\tau|=a$, its exponent
has a strict gap from the central mass $e^{-a}$. A linear rank bound needs
that gap to pay the full degree-$N$ polynomial growth, and must also pay
every non-leading native product fibre. The expected horizon $a\ge C(N+1)$
would match the existing linear upper bound for the first failing moment
order; it is not established by the positive-band theorem.
