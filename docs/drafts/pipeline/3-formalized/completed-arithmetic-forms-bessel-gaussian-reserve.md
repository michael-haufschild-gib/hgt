# A Gaussian lower reserve inside the physical Bessel band

For the literal Schläfli source,
\[
K_{i\tau}(a)\ge e^{-\tau^2/a}K_0(a)>0,
\qquad a>0,\quad |\tau|\le a.
\]
Its full signed radial combination satisfies
\[
(a^2+9)K_{i\tau}(a)+6aK'_{i\tau}(a)
\ge(a^2-6a+3)e^{-\tau^2/a}K_0(a)>0,\qquad a\ge6.
\]

The exact differentiated order recurrence gives
\[
\int_0^\infty t\sinh(t)e^{-a\cosh t}\,dt=K_0(a)/a.
\]
Indeed, differentiating $K_{\nu+1}=K_{\nu-1}+2\nu K_\nu/a$ at
$\nu=0$ and using $K_{-\nu}=K_\nu$ yields
$\partial_\nu K_\nu(a)|_{\nu=1}=K_0(a)/a$.
Literal derivative-kernel integrability identifies this with the integral.
Since $t\le\sinh t$ for $t\ge0$,
\[
\int_0^\infty t^2e^{-a\cosh t}\,dt\le K_0(a)/a.
\]
The cosine defect $1-\cos y\le y^2/2$ then gives, for every real $\tau$,
\[
1-\frac{\tau^2}{2a}\le\frac{K_{i\tau}(a)}{K_0(a)}\le1.
\]
In particular this ratio tends to one as $a\to\infty$ at fixed $\tau$.

Let $f(x)=K_{i\tau}(x)$, $g(x)=K_0(x)$, and
$h(x)=e^{-\tau^2/x}g(x)$. For
$L_\tau y=(xy')'-(x-\tau^2/x)y$, the exact identity is
\[
L_\tau h=\frac{\tau^2e^{-\tau^2/x}}x
\left[2g'+(1-x^{-1}+\tau^2x^{-2})g\right].
\]
The literal integral gives $g'\le-g$, hence $L_\tau h\le0$ on
$x\ge|\tau|$. The Wronskian $W=x(f'h-fh')$ satisfies
$W'=-fL_\tau h\ge0$ and $W(\infty)=0$, so $W\le0$.
Thus $f/h$ is nonincreasing and its limit is one, proving the lower reserve.
The signed radial estimate follows from
$K'_{i\tau}(a)\ge-(1+1/a)K_{i\tau}(a)$.

Lean: `CompletedArithmeticForms/BesselGaussianMoments.lean`,
`integral_bessel_first_moment`, `integral_bessel_second_moment_le`,
`bessel_imaginary_ratio_bounds`, `tendsto_bessel_imaginary_ratio_one`;
`BesselGaussianReserve.lean`, `hasDerivAt_besselGaussianFlux`,
`besselGaussianFlux_nonpos`, `modifiedBesselKOrder_gaussian_lower`,
`besselSignedRadialCombination_gaussian_lower`.

A linear physical rank horizon remains unproved. It requires
polynomial-weighted payment of the signed transform outside this band
and of every non-leading native product fibre.
