# A positive spectral band for the Schläfli source

**ID:** completed-arithmetic-forms-bessel-spectral-band  
**Stage:** Formalized in Lean 4  
**Type:** Source-derived spectral sign and zero boundary

The corpus Schläfli source is
$$K_\nu(a)=\int_0^\infty e^{-a\cosh t}\cosh(\nu t)\,dt.$$
`HTGeometry/BesselOrderPolyaRealZeros.lean` proves its argument system,
exponential decay, eventual positive real part for each order, and the flux law
$$\frac{d}{dx}\bigl(xK_\nu'(x)\overline{K_\nu(x)}\bigr)
=\frac{\nu^2}{x}|K_\nu(x)|^2+x\bigl(|K_\nu(x)|^2+|K_\nu'(x)|^2\bigr).$$
The literal source satisfies
$$a>0,\quad |\tau|\le a\quad\Longrightarrow\quad K_{i\tau}(a)>0.$$
At a hypothetical zero, the flux starts at zero. Its derivative is
$(x-\tau^2/x)|K|^2+x|K'|^2$, nonnegative for $x\ge a$ and strictly positive
on an interval beyond a point where $K$ is nonzero. The flux therefore has a
strict positive lower bound on a ray, contradicting its decay to zero.
Reality and eventual positivity then determine the sign on the whole ray.

Every complex-order zero therefore satisfies
$$K_\nu(a)=0\Longrightarrow \Re\nu=0,\qquad a<|\Im\nu|.$$
Lean: `CompletedArithmeticForms/BesselSpectralBand.lean`,
`modifiedBesselKOrder_ne_zero_on_band`,
`modifiedBesselKOrder_zero_outside_band`, and
`modifiedBesselKOrder_re_pos_on_band`.

A rank bound linear in $q$ additionally requires a polynomial-weighted estimate
for the signed spectral tail; positivity of the band alone does not supply it.
