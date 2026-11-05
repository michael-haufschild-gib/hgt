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
The formalized Stieltjes representation is

`1/κ(s)=R/(s+b)+∫₁∞ρ(t)/(s+t)dt`.

Thus `v(x)=R exp(-bx)+∫₁∞ρ(t)exp(-tx)dt` is positive,
continuous, decreasing, and integrable, with total mass `1/κ(0)=1`.
The unshifted analogue appears in
[Grzywny–Ryznar, Proposition 3.2](https://arxiv.org/abs/1107.0745v1).
Here the boundary jump gives `ρ`, while the simple zero at `-b` gives the
positive residue `R`. The continuation, unique simple zero, and residue are
[formalized](../3-formalized/the-logarithmic-factor-has-one-negative-zero.md).
The exact Stieltjes formula and integrability are
[formalized](../3-formalized/the-reciprocal-logarithmic-factor-has-its-positive-measure.md).
The causal mixture, its exact Laplace transform, unit mass, continuity and
monotonicity are [formalized](../3-formalized/the-logarithmic-causal-kernel-is-a-positive-probability-density.md).

For the complementary causal kernel, the proposed formula is

`k(x)=1+∫₁∞ exp(-tx)/(2tκ(t))dt`,

with Laplace transform `κ(s)/s`; consequently `k*v=1` on the positive half-line.
A Cauchy representation on the slit plane must still prove the complementary
formula. The corpus has Szegő outer-function analyticity, Poisson boundary
modulus, and causal Fourier/convolution infrastructure; no matching complete
factorization has been located.

For the complex extension use
`κ(z)=exp((1/π)∫₀∞√z log(1+(1/2)log(1+zt²))/(z+t²)dt)`.
This is the slit-plane formula in
[Kwaśnicki, Lemma 3.8 and (3.5)](https://arxiv.org/abs/1006.0524).
Slit-plane analyticity, agreement on positive real parameters, and conjugation
symmetry are formalized in `TheLogarithmicFactorExtendsToTheSlitPlane`.
The right-half-plane identification, pointwise Poisson boundary reproduction,
and exact identity `κ(z)κ(-z)=1+(1/2)Log(1-z²)` off the real axis are
[formalized](../3-formalized/the-logarithmic-factor-has-its-reflection-identity.md).
Explicit Cauchy inversion proves the reciprocal representation; the complementary
representation remains open.
For the reciprocal factor, analytic pole subtraction, the exact upper cut jump
`-2πiρ(t)`, continuity at the branch endpoint, and boundedness of the positive
density are [formalized](../3-formalized/the-reciprocal-logarithmic-factor-has-its-cut-density.md).
Bounded density makes each subtracted Stieltjes integral absolutely integrable.
The positive differences
`ρ(t)(1/(t+s)-1/(t+S))`, `S>s>0`, increase to `ρ(t)/(t+s)`.
Reciprocal decay sends the remainder at `S` to zero; monotone convergence
supplies integrability and the unsubtracted identity together.

Uniform contour control follows from the proved modulus identity.
The elementary bound `Ψ(t)≤Ψ(R)(1+t²/R²)` and
`(Im z+Re z·u)²≤|z|²(1+u²)` give `|κ(z)|²≤CΨ(|z|)` for a finite
universal constant. When `Im z≥0`, the interval `1≤u≤2` gives
`|κ(z)|²≥exp(log Ψ(|z|)/(5π))`; conjugation treats the other sign.
Hence the reciprocal tends uniformly to zero at infinity on the right.
Reflection controls the left. These bounds and uniform reciprocal decay are
formalized in `TheReciprocalLogarithmicFactorVanishesAtInfinity`.
Complementary Stieltjes inversion remains unproved.

## Operator identification

The causal convolution `W` by `v` is bounded on half-line L². Its inverse
has Fourier multiplier `κ(iξ)`. The proved boundary modulus gives the exact
zero-extension form identity `H₊=B*B`, once support preservation of `B` is
established; then `H₊⁻¹=WW*` and Fubini give the Green kernel.

For `ε>0`, `κ(z)/(1+εz)` is bounded and holomorphic through the closed right
half-plane. Indeed `|κ(z)|²≤(C+1)(1+|z|²)` and
`|1+εz|²≥1+ε²|z|²`. Rotate to the upper half-plane and apply the corpus theorem
`ClosedUpperHalfPlaneMultiplier.boundaryMul_mem_hardy`. On the actual form
domain, dominated L² convergence as `ε↓0` identifies the limit with `B`;
closedness of half-line support proves causality. This route does not require
the complementary Stieltjes representation.

For the actual source equation `Gu=f`, use `Hu=f+u`: established boundedness
of `u` preserves bounded interior forcing. The fixed shift avoids an unbounded
inverse and a vanishing-regularization limit for the source equation.
Support preservation on the full actual multiplier graph domain is
[formalized](../3-formalized/the-logarithmic-factor-preserves-half-line-support.md).
Actual convolution-multiplier identification and form-domain equality remain open.

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
Set `x=exp(-u)` and choose `s=exp(u-√u)` for the upper bound,
`exp(u+√u)` for the lower. The normalized factor ratios tend to one;
the upper exponential tends to one and the discarded tail to zero.
Squeezing gives `V(x)√log(1/x)→1`. Both bounds and the exact normalization
are [formalized](../3-formalized/the-logarithmic-renewal-mass-has-its-exact-normalization.md).
Missing proofs for the Green kernel: causal inverse and exact form identification. Complementary Stieltjes inversion is an
independent stronger formula.

For exterior forcing, `lintegral_carleman_sq_le` proves the sharp half-line
Carleman bound. `CCMRestrictedWeilGammaBoundaryPairing` already constructs
both literal Gamma boundary actions on arbitrary aperture-supported L² sources
and identifies their mixed forms. Admission to the global multiplier domain
still requires assembling these exterior actions with the interior equation.
