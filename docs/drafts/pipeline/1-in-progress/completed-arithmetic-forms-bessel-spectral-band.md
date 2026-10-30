# A positive spectral band for the physical first-atom kernel

**ID:** completed-arithmetic-forms-bessel-spectral-band  
**Stage:** In progress  
**Type:** Source-derived Fourier sign and rank boundary

The corpus Schläfli source is
$$K_\nu(a)=\int_0^\infty e^{-a\cosh t}\cosh(\nu t)\,dt.$$
`HTGeometry/BesselOrderPolyaRealZeros.lean` proves its argument system,
exponential decay, eventual positive real part for each order, and the flux law
$$\frac{d}{dx}\bigl(xK_\nu'(x)\overline{K_\nu(x)}\bigr)
=\frac{\nu^2}{x}|K_\nu(x)|^2+x\bigl(|K_\nu(x)|^2+|K_\nu'(x)|^2\bigr).$$
These inputs expose the stronger target
$$a>0,\quad |\tau|\le a\quad\Longrightarrow\quad K_{i\tau}(a)>0.$$
At a hypothetical zero, the flux starts at zero. Its derivative is
$(x-\tau^2/x)|K|^2+x|K'|^2$, nonnegative for $x\ge a$ and strictly positive
on an interval beyond a point where $K$ is nonzero. The flux therefore has a
strict positive lower bound on a ray, contradicting its decay to zero.
Reality and eventual positivity then determine the sign on the whole ray.

A further comparison target on that ray is
$$K_{i\tau}'(x)\ge-(1+1/x)K_{i\tau}(x).$$
For $g(x)=e^{-x}/x$, its Wronskian with $K$ has derivative
$$\frac d{dx}\bigl(x(K'g-Kg')\bigr)
=-e^{-x}\left(\frac1x+\frac{1+\tau^2}{x^2}\right)K_{i\tau}(x)<0.$$
The Wronskian tends to zero at infinity; its sign gives the derivative bound.
For the first-atom physical pair, the Fourier density is proportional to
$(4q^2+9)K_{i\tau}(2q)+12qK_{i\tau}'(2q)$. The displayed comparison would
make this density positive on $|\tau|\le2q$ for $q\ge3$.
The spectral-band and first-atom transfer targets require Lean formalization.
A rank bound linear in $q$ additionally requires a polynomial-weighted estimate
for the signed spectral tail; positivity of the band alone does not supply it.
