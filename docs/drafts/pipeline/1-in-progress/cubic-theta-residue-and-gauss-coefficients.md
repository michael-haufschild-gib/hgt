# Cubic theta residue and Gauss coefficients

- **ID:** cubic-theta-residue-and-gauss-coefficients
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [metaplectic Möbius descent](metaplectic-mobius-descent.md)
- **Statement:** Construct a nonzero cubic automorphic residual function on hyperbolic three-space whose squarefree primary Fourier coefficients are the actual normalized cubic Gauss sums, with the explicit different-symbol phase.

The arithmetic character and finite-index kernel are constructed locally.
The required analytic source is the residue of the cubic Eisenstein family at
parameter `s=4/3`, with Laplace eigenvalue `s(2−s)=8/9`. The target coefficient
identity is
`conjugate(ρ(p))=C∞ conjugate((1+2ω/p)₃) γ₂((p))`, with `C∞≠0`,
for squarefree primary `p`. Cube indices must satisfy
`ρ(pq³)=‖q‖ρ(p)` and the remaining valuation classes must be controlled.

A concrete spectral construction uses the energy graph and mass inclusion `M`.
Its pencil is `T(z)=Id−(z+1)M* M`. A compact-core estimate gives finite kernel
and closed range at `z=8/9`; self-adjointness identifies the range with the
kernel's orthogonal complement. On the kernel, `M* M=9/17`, so the singular
part is explicit. Inverting the regular restriction near `8/9` supplies the
meromorphic continuation. Fourier analysis of the residual family must then
prove the coefficient identity and nonvanishing.

The actual hyperbolic quotient, upper-coordinate homeomorphism, integral
Ford reduction, and finite compact-core/cusp cover are now formalized; see
[Bianchi reduction](../3-formalized/bianchi-reduction-and-compact-core.md).

The [actual cubic Eisenstein series](../3-formalized/cubic-eisenstein-source-series.md)
is absolutely convergent and holomorphic for `Re s>2`, with the required
character automorphy. This does not yet reach the residual parameter.

The [measurable fundamental selector](../3-formalized/cubic-kernel-measurable-fundamental-domain.md)
is constructed pointwise; the full `SL₂(ℂ)` action preserves the actual
upper-half-space volume.

The [quotient volume](../3-formalized/hyperbolic-volume-and-finite-cubic-quotient.md)
is positive, finite, and independent of the chosen fundamental domain.

The [actual energy space has compact restriction](../3-formalized/cubic-kernel-local-sobolev-compactness.md)
to every compact quotient set. Gradient closability and mass injectivity
are also formalized. The [variational Laplacian](../3-formalized/cubic-quotient-variational-laplacian.md)
is closed, densely defined, nonnegative, and self-adjoint.
The [global Green identity](../3-formalized/cubic-quotient-green-identity.md)
identifies its action with the positive coordinate Laplacian.

The [actual exterior coercivity estimate](../3-formalized/cubic-quotient-exterior-coercivity.md)
is formalized on the completed energy graph, with compact error map.

The [spectral pencil is Fredholm](../3-formalized/cubic-spectral-pencil-fredholm.md)
for `0≤λ<1`, including `λ=8/9`; nonzero kernel is not yet proved.

The [actual resolvent is meromorphic](../3-formalized/cubic-meromorphic-resolvent.md)
at `z=8/9` and after composition at `s=4/3`, with explicit finite-rank singular part.

The [smooth incoming forcing](../3-formalized/cubic-smooth-incoming-forcing.md)
is compactly supported on the quotient and entire as an `L²` family.

The [incoming spectral residue](../3-formalized/cubic-incoming-spectral-residue.md)
is constructed globally in `L²` and locally for the corrected incoming family.
Its nonvanishing is not yet established.

Open inputs: [source matching](../2-fully-proven/cubic-initial-resolvent-matching.md),
[residue nonvanishing](../2-fully-proven/cubic-constant-term-nonvanishing.md), Fourier
identification, and nonvanishing of `C∞`. None is supplied as an assumption
in a local endpoint.
The subsequent uniform mean-square descent remains on the parent card.

Sources: external OpenAI `Eisenstein/FredholmAlternative.lean`,
`MeromorphicResolvent.lean`, `ResidualFourierExpansion.lean`,
`SquarefreeCoefficients.lean`, and `GaussSum/DualKernelSummability.lean`.
