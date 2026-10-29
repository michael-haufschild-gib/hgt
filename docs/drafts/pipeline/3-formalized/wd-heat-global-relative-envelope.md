# Global relative envelope for the Riemann heat flow

- **ID:** wd-heat-global-relative-envelope
- **Stage:** 3-formalized
- **Source:** [mean-field persistence](wd-mean-field-heat-persistence.md)
- **Lean:** `formal/GaloisForLFunctions/RHTower/HeatRelativeGlobalBounds.lean`
- **Main declaration:** `RHTower.DeBruijn.exists_riemannHeat_global_relative_bound`

## Statement

There are absolute constants `C>0` and `X₀≥4096` such that, for
`X≥X₀`, `0≤t≤1/8`, and `t log X≤1`,

\[
 |H_t(x+iy)|\le |\xi(33/2+iX)|
   \exp\bigl(C\log X(1+|x-X|)\bigr)
\]

for every real `x` and every `|y|≤1`. All source bounds are discharged
for the actual Riemann kernel and heat flow, including the zero-time endpoint.

## Proof

Put `L=log X` and `N_x=|xiLine x 16|`. For `X≥4096`, `L≥20`, and
`2048≤x≤X²`, the existing Euler-region logarithmic derivative estimate
bounds the derivative in height by `2L` times the modulus. Indeed,
`log(s/(2pi))≤log s≤2L` throughout the segment joining `X` and `x`,
and `(16+1/2)/(2s)≤1`. Grönwall gives

\[
N_x\le N_X e^{2L|x-X|}.
\]

The kernel integral gives a fixed strip bound `|H_t(z)|≤M` whenever
`0≤t≤1/8` and `|Im z|≤1`. One may take

\[
M=1+\int_{\mathbb R}\Phi(u)e^{u^2/8}e^{|u|}\,du>0.
\]

Super-exponential decay proves integrability; positivity and exponent
monotonicity prove the uniform bound.

If `|x-X|≤X/2`, then `2048≤x≤X²`. The actual Gaussian envelope at
height `x` has slope
`B_x=(log x+xiSliceGlobalConstant)/2≤2L`. For `|y|≤1`,
`B_x|y|+y²+2t B_x²≤1+10L`. Combining the envelope with the height
comparison and `4≤exp 4` yields

\[
|H_t(x+iy)|\le N_X e^{15L+2L|x-X|}.
\]

The same bound holds at `t=0` by the direct `ξ` envelope.

For the complementary heights put `N_*=N_{2048}>0` and `Q=M/N_*`.
The height comparison implies `N_*≤N_X e^{2LX}`; also `Q≤e^Q`.
Consequently

\[
|H_t(x+iy)|\le M\le N_X e^{2LX+Q}.
\]

Here `X≤2|x-X|` and `L≥20`. Taking `C=Q+20` and
`X₀=4096+exp 20` absorbs both cases into the claimed envelope.

## Validation and limits

Passed without warnings:

```sh
cd formal
lake --old env lean GaloisForLFunctions/RHTower/HeatRelativeGlobalBounds.lean
```

Wired into `RHTower.lean`; umbrella not compiled. No web, novelty, or
axiom checks performed, as instructed.

This discharges the global growth input to the translated reverse
Gaussian argument. The complete persistence theorem is recorded in the
linked card; a heat zero-count upper bound and WD extinction remain open.
