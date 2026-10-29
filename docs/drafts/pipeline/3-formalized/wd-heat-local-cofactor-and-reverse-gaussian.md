# Local heat cofactors and reverse Gaussian averaging

- **ID:** wd-heat-local-cofactor-and-reverse-gaussian
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [WD source investigation](../1-in-progress/wd-directed-source-extinction.md)
- **Statement:** The actual heat flow has uniformly controlled local cofactors for `t log X≤1`, and its reverse Gaussian integral admits arbitrary complex contour translation and exact linear-slope cancellation.

## What this discharges

The mean-field persistence argument needs local logarithmic control and
an exact reverse-heat representation of the actual function. Both inputs
are now formalized. No heat Hadamard product or zero ODE is assumed.
Persistence still needs the zero-free-window estimates, a global relative
growth bound, a saddle construction, and the full Gaussian error estimate.
WD extinction remains open.

## Cofactor theorem

Module: `RHTower/HeatLocalCofactor.lean`.

- `exists_riemannHeat_local_cofactor` gives explicit bounds under
  `X≥4096`, `log X≥20`, `alpha≥8`, `0≤t≤1/8`, and `t log X≤1`.
- `exists_uniform_riemannHeat_local_cofactor` removes the auxiliary
  height conditions: absolute `C>0` and `X₀≥4096` work for all
  `X≥X₀`, `0≤t≤1/8`, and `t log X≤1`.

Put `c=X-16i` and `N=|xiLine X 16|`. The uniform theorem constructs
a finite set `T`, multiplicities `m_a`, and an entire cofactor `g` with

\[
H_t(c+z)=\prod_{a\in T}(z-a)^{m_a}g(z),\qquad |a|\le18.
\]

The cofactor is nonzero on `|z|≤18`. Writing `n=Σ m_a`,

\[
n\le C\log X,\quad
|g'/g|\le C\log X\quad(|z|\le17),\quad
|(g'/g)'|\le C\log X\quad(|z|\le67/4).
\]

It also proves

\[
|g(z)|\ge\frac{N}{8\,18^n}e^{-C\log X}\qquad(|z|\le17).
\]

If `d≥0` and `|z-a|≥d` for each extracted factor with positive
multiplicity, then

\[
|H_t(c+z)|\ge\frac{d^nN}{8\,18^n}e^{-C\log X}.
\]

Zero-exponent factors require no distance condition.

### Proof

The earlier Euler-anchor theorem gives `N≤8|H_t(c)|`, with `N>0`.
The radius-40 disk about `c` lies in the proved source rectangle, so
`|H_t(c+z)|≤NB/8`, where `B=32 exp(4096+264 log X)`.

Extract the zeros of the radius-18 disk using
`exists_zero_free_cofactor_bounds`. The resulting entire `g` is zero-free
on that closed disk and satisfies `|g|≤NB/(8·22^n)` on the radius-40
disk. At zero, the product has modulus at most `18^n`; hence
`|g(0)|≥N/(8·18^n)`. The maximum-to-anchor ratio for `g` is therefore
at most `B(18/22)^n≤B`.

`sum_multiplicity_mul_log_le` gives `n log(11/9)≤log B`.
`norm_logDeriv_le`, with radii `18`, `35/2`, and `17`, gives
`|g'/g|≤140(log B+1)`. Cauchy's derivative estimate on a radius-`1/4`
disk gives `|(g'/g)'|≤560(log B+1)` on `|z|≤67/4`.
`norm_lower_bound_of_ball`, with radii `18` and `17`, gives
`|g(z)|≥N/(8·18^n) exp(-34(log B+1))`.

For `X≥4096+2pi exp20`, all source range conditions hold and
`log B+1≤(log32+4361)log X`. A single absolute constant absorbs the
degree, derivative, and minimum-modulus coefficients. Finally, each
positive-multiplicity factor contributes at least `d^{m_a}` away from its
root; multiplying these inequalities gives the stated lower bound for
the actual heat flow. The proof includes `t=0` through its exact Euler
anchor identity.

## Reverse Gaussian theorem

Module: `RHTower/HeatReverseGaussian.lean`.

- `riemannHeat_sub_eq_integral_gaussian`:
  `H_(t-tau)(z)=∫ g_tau(u) H_t(z+u) du`, for `t≥0`, `tau>0`.
- `riemannHeat_sub_eq_integral_complex_shift`:
  the same integral may be evaluated at `u+b` for every `b∈ℂ`, using
  the complex Gaussian weight.
- `integrable_cgauss_mul_heat_shift`:
  the translated complex integrand is absolutely integrable.
- `riemannHeat_sub_eq_reverse_saddle`:

\[
H_{t-\tau}(z)=e^{-\tau a^2}
\int_{\mathbb R}g_\tau(u)e^{-ua}H_t(z+2\tau a+u)\,du
\]

  for every `a∈ℂ`.
- `riemannHeat_zero_eq_reverse_saddle` specializes this identity to
  `tau=t>0`, recovering the unheated function from positive heat.

### Proof

The actual kernel `Phi(x) exp(t x²)` remains superexponentially
integrable by `riemannKernel_superExp.mul_exp_sq`. Fubini is justified
by integrating the absolute value of the product of this Fourier
integrand and the real Gaussian. The Gaussian characteristic function
contributes `exp(-tau x²)`, giving time `t-tau` exactly.

`norm_riemannHeat_le_strip_integral` bounds `H_t` on a horizontal strip
by the positive-kernel exponential integral. The complex Gaussian has
modulus proportional to `exp(((Im v)²-(Re v)²)/(4tau))`. On each fixed
strip this product is bounded by a constant times `exp(-|Re v|)`.
The existing horizontal-contour theorem therefore permits any vertical
translation; real translation invariance then permits any complex
translation. The same decay proves absolute integrability there.

At translation `b=2tau a`,

\[
-\frac{(u+2\tau a)^2}{4\tau}
=-\frac{u^2}{4\tau}-\tau a^2-ua.
\]

This exact identity gives the completed-square formula. It imposes no
saddle equation and makes no assertion that the remaining integral is
nonzero; those are the next parts of the persistence proof.

## Verification

Both final plain-file checks passed without warnings, from `formal/`:

```text
lake --old env lean GaloisForLFunctions/RHTower/HeatLocalCofactor.lean
lake --old env lean GaloisForLFunctions/RHTower/HeatReverseGaussian.lean
```

Both modules are wired into `GaloisForLFunctions/RHTower.lean`.
The umbrella was not compiled.
