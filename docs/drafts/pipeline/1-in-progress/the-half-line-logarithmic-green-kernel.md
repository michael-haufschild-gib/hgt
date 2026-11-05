# The half-line logarithmic Green kernel

- **ID:** half-line-logarithmic-green
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** The half-line compression of `H=1+(1/2)log(1-D²)` has Green kernel `G₊(x,y)=∫₀^{min(x,y)}v(x-s)v(y-s)ds`, with `V(x)=∫₀ˣv` and `V(x)√log(1/x)→1`.

## Role

This is the missing reference kernel for
[normalized Weil boundary traces](normalized-boundary-traces-of-weil-riesz-vectors.md).
The actual bounded Riesz sources must be connected to this kernel through their
operator equation; an abstract kernel premise would not finish that task.
Their literal positive logarithmic Dirichlet equation and bounded full forcing
are [formalized](../3-formalized/the-weil-riesz-equation-is-a-logarithmic-dirichlet-equation.md).

## Explicit factor

Put `Ψ(t)=1+(1/2)log(1+t²)` and

`κ(s)=exp((1/π)∫₀∞s log(Ψ(t))/(s²+t²)dt)` for `s>0`.

Let `b=√(1-exp(-2))`, `R=κ(b)(1-b²)/b`, and
`ρ(t)=2κ(t)/((2+log(t²-1))²+π²)` for `t>1`.
The proposed Stieltjes representation is

`1/κ(s)=R/(s+b)+∫₁∞ρ(t)/(s+t)dt`.

Thus `v(x)=R exp(-bx)+∫₁∞ρ(t)exp(-tx)dt` is positive,
continuous, decreasing, and integrable, with total mass `1/κ(0)=1`.
The unshifted analogue appears in
[Grzywny–Ryznar, Proposition 3.2](https://arxiv.org/abs/1107.0745v1).
Here the boundary jump gives `ρ`, while the simple zero at `-b` gives the
positive residue `R`. These formulas still require proof.

For the complementary causal kernel, the proposed formula is

`k(x)=1+∫₁∞ exp(-tx)/(2tκ(t))dt`,

with Laplace transform `κ(s)/s`; consequently `k*v=1` on the positive half-line.
A Cauchy representation on the slit plane should prove both formulas from the
factor identity. The corpus has Szegő outer-function analyticity, Poisson boundary
modulus, and causal Fourier/convolution infrastructure; no matching complete
factorization has been located.

For the complex extension use
`κ(z)=exp((1/π)∫₀∞√z log(1+(1/2)log(1+zt²))/(z+t²)dt)`.
This is the slit-plane formula in
[Kwaśnicki, Lemma 3.8 and (3.5)](https://arxiv.org/abs/1006.0524).
Analyticity and agreement on positive real parameters identify it with the
right-half-plane Poisson factor. Poisson boundary reproduction then gives
`κ(iy)κ(-iy)=Ψ(y)`; the identity theorem extends this to
`κ(z)κ(-z)=1+(1/2)log(1-z²)` off the real axis.
Thus explicit Cauchy inversion can establish both positive densities above,
without assuming a complete Bernstein representation theorem.

The proposed contour bound follows from concavity of
`x↦1+(1/2)log(1+x)`:
`Ψ(R)t²/(R²+t²)≤Ψ(t)≤Ψ(R)(1+t²/R²)`.
The corresponding rational Poisson factors should give
`√Ψ(|z|)/2≤|κ(z)|≤2√Ψ(|z|)` for `Re z>0`.
Reflection then controls the left half-plane. All complex extension,
boundary reproduction, contour estimates, and inversion steps remain unproved.

## Operator identification

The causal convolution `W` by `v` is bounded on half-line L².
Its inverse is the weak derivative of convolution with `k`.
Prove the exact zero-extension form identity `H₊=B*B`, where `B=W⁻¹`;
then `H₊⁻¹=WW*`, and Fubini gives the kernel formula.
For the actual source equation `Gu=f`, use `Hu=f+u`: the established
boundedness of `u` preserves bounded interior forcing. Thus the fixed shift
avoids an unbounded inverse and any vanishing-regularization limit.
Support preservation of the inverse and form-domain equality must be proved.

The complementary kernel has `k=1+k₀`, with `k₀` supported on the positive
half-line and `∫k₀=∫₁∞1/(2t²κ(t))dt<∞`. Thus the inverse can be written
`Bu=u+(k₀*u)′`. The identity `κ(iξ)=1+iξ k̂₀(ξ)` places `k₀*u` in H¹
whenever the logarithmic form is finite. Causal convolution and locality of
the weak derivative then preserve support. The corpus already identifies
Fourier H¹ with existence of an L² distributional derivative in
`mem_fourierL2H1_iff_exists_weakDerivative`.

## Normalization and remaining obligations

For `φ(w)=log(Ψ(exp w))`, differentiation gives
`0≤φ′(w)≤2`, and `φ′(w)≤1/w` for `w>0`.
Consequently `|φ(w+u)-φ(w)|≤2|u|`, while each fixed increment tends to zero
as `w→∞`. The substitution `t=s exp u` writes the logarithm of
`κ(s)/√Ψ(s)` as `(1/(2π))∫[φ(log s+u)-φ(log s)]/cosh u du`.
The corpus theorem `integrable_logSineSech_abs_pow` supplies the majorant;
dominated convergence gives `κ(s)/√Ψ(s)→1`. The literal Poisson identity
and `κ(s)/√log(s)→1` are
[formalized](../3-formalized/the-logarithmic-poisson-factor-has-its-exact-normalization.md).
The normalization of `V` follows from two direct Laplace bounds:
`V(x)≤exp(sx)/κ(s)` and
`V(x)≥1/κ(s)-exp(-sx/2)/κ(s/2)`.
Choose `s=x^{-p}` with `p<1` for the upper bound and `p>1` for the lower
bound; then let `p→1`. This gives `V(x)√log(1/x)→1`.
Missing proofs: slit-plane factorization, Stieltjes inversion, causal inverse,
exact form identification, and normalized renewal asymptotic.

For exterior forcing, `lintegral_carleman_sq_le` proves the sharp half-line
Carleman bound. `CCMRestrictedWeilGammaBoundaryPairing` already constructs
both literal Gamma boundary actions on arbitrary aperture-supported L² sources
and identifies their mixed forms. Admission to the global multiplier domain
still requires assembling these exterior actions with the interior equation.
