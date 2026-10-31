# Elliptic radial kernels are continuous finite local products

- **Stage:** 2-fully-proven
- **Parent:** [Global radial integral](../1-in-progress/elliptic-radial-kernels-integrate-to-the-global-zeta-ratio.md).
- **Statement:** The actual adelic logarithmic height is continuous and is
  the finite sum of local logarithmic heights on each cylinder. Its spectral
  exponential equals the independently defined local product and is integrable
  on every cylinder for `Re(s)>0`.

## Proof

For an integral translation `y`, the ultrametric inequalities applied to
`x+y` and `(x+y)-y` give `max(1,v(x+y))=max(1,v(x))`. The normalized magnitude
is increasing, so the same identity holds for each logarithmic height.
Finite coordinates of an adele are integral outside a finite set; their
logarithmic heights therefore have finite support.

The global height is invariant under the open integral adelic subgroup.
It is locally constant, hence continuous. Its complex exponential is
continuous, and its norm is the real exponential at the real part of the
spectral parameter. On a cylinder all tail heights vanish. Exponentiating
the finite sum gives exactly the local product. The audited measure-preserving
cylinder assembly transfers its audited integrability to ambient Haar.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticRadialKernel.lean`:
`continuous_ellipticAdeleSpectralKernel`, `ellipticAdeleSpectralKernel_cylinder`,
`ellipticAdeleSpectralKernel_integrableOn_cylinder`. Direct audit pending.
