# The half-line logarithmic Green kernel

- **ID:** half-line-logarithmic-green
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual positive-half-line compression of `H=1+(1/2)log(1-D²)` has inverse kernel `G₊(x,y)=∫₀^{min(x,y)}v(x-s)v(y-s)ds` off its potentially singular diagonal, and `V(x)√log(1/x)→1`, where `V(x)=∫₀ˣv`.

## Literal factor and density

Put `Ψ(t)=1+(1/2)log(1+t²)` and
`κ(s)=exp((1/π)∫₀∞s log(Ψ(t))/(s²+t²)dt)` for `s>0`.
For `b=√(1-exp(-2))`, `R=κ(b)(1-b²)/b`, and
`ρ(t)=2κ(t)/((2+log(t²-1))²+π²)`, the exact representation is

`κ(s)⁻¹=R/(s+b)+∫₁∞ρ(t)/(s+t)dt`.

Thus `v(x)=R exp(-bx)+∫₁∞ρ(t)exp(-tx)dt` for `x>0`, and zero otherwise.
It is positive and decreasing on the positive half-line, with total mass one,
Laplace transform `κ(s)⁻¹`, and Fourier transform `κ(2πiξ)⁻¹`.
The continued factor satisfies `|κ(iy)|²=Ψ(y)` at every real frequency.

## Actual inverse and kernel

Bounded holomorphic regularizers `κ(z)/(1+εz)` prove that multiplication by
`κ(2πiξ)` preserves half-line support whenever its result belongs to L².
Consequently causal convolution `W` has range exactly the finite logarithmic
energy domain, and `q(Wu,Wv)=⟨u,v⟩`. Every L² forcing has unique variational
solution `WW*f`.

Compress the literal convolution Schur kernel to positive inputs. Both it
and its adjoint have positive-half-line range. Inner-product adjunction
identifies their restrictions with `W` and `W*`. Schur composition gives
`WW*`; causality reduces its kernel to the stated overlap integral.
For `x<y`, monotonicity bounds the integrand by `v(y-x)v(x-s)`, which is
integrable. Symmetry handles `y<x`. The operator representation is almost
everywhere and makes no finite-diagonal assertion.

Finally `V(x)≤exp(sx)/κ(s)` and
`V(x)≥κ(s)⁻¹-exp(-sx/2)/κ(s/2)`. Set `x=exp(-u)` and choose
`s=exp(u∓√u)`. Since `κ(s)/√log(s)→1`, these bounds give the exact
normalization `V(x)√log(1/x)→1`.

## Lean

Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `TheHalfLineLogarithmicFormHasItsActualInverse.lean`:
  `hasLogarithmicEnergy_iff_mem_range`, `logarithmicHalfLineForm_causalOperator`,
  `existsUnique_logarithmicHalfLine_solution`.
- `TheHalfLineLogarithmicGreenKernelIsExplicit.lean`:
  `logarithmicHalfLineGreenOperator_coeFn`,
  `integrable_logarithmicHalfLineGreenKernel`.
- `TheLogarithmicRenewalMassHasItsExactNormalization.lean`:
  `tendsto_logarithmicRenewalMass_normalized`.

Production plain audits passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports these modules.

The application to [actual Weil Riesz boundary traces](normalized-boundary-traces-of-weil-riesz-vectors.md)
is formalized, including full forcing assembly and continuous representatives.
Aperture variation remains separate.
