# Denjoy–Carleman rough-regime positivity

- **ID:** denjoy-carleman-rough-regime
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-0111/route-obstacles.md`, A3.
- **Target:** A fixed nonnegative logarithmic Denjoy–Carleman profile on `[0,1]`
  and a constant `ε>0` for which the complete Weil matrix is eventually positive
  definite uniformly on `1≤c≤ε L(log L)²`, where `L=loglog N`.

## Analytic input

The existing smooth exponential-tilt theorem proves real Fourier nonvanishing
by avoiding a countable set of horizontal lines. It gives no quantitative
lower bound as frequency grows. The sinc-product profile has the required
derivative bounds and integrated Fourier tail, but has real Fourier zeros.
Neither statement alone supplies the growing Gamma reserve.

Let `f=sincProfile`, `h=f*reflect(f)`, and
`g(x)=∫₁² h(x/s)/s ds`. Then
`ĝ(t)=∫₁² |f̂(st)|² ds = t⁻¹∫ₜ²ₜ |f̂(u)|² du` for `t>0`.
The existing band-energy theorem therefore gives the pointwise floor
`ĝ(t)≥exp(-C t/log²t)` for large `t`. Compact support makes `f̂` analytic;
its unit mass excludes vanishing on any interval, so `ĝ(t)>0` everywhere.
Autocorrelation and averaging dilations `1≤s≤2` preserve the logarithmic
Denjoy–Carleman derivative class. Translate and dilate `g` to `[0,1]`.
This replaces the qualitative tilt by a profile with a quantitative floor.

For `φ(x)=8g(8(x−1/2))`, the derivative bound is
`‖φ⁽q⁾‖₁≤32·96^q·dcLogWeight(q)` and
`|paperFT φ(r)|=|ĝ(r/(16π))|`. Put
`b(c)=exp(-202C·(c/(16π))/log²(c/(16π)))` and `M=∫φ²`.
For sufficiently large `c`, the band `[c,101c]` has squared-transform floor
`b(c)`. The Montgomery–Vaughan band estimate gives Gamma coefficient
`24cb(c)/(πM)` with physical mass cost `O(c)`, uniformly for `N≥c`.
Every completed conductor energy has floor `2cb(2πc)/M`.

Both inverse floors and polynomial overlap costs are eventually bounded by
powers of `T(c)=exp(Bc/log²c)` for a fixed `B>0`. The spectral argument must
retain this auxiliary bound separately from actual overlap. For sufficiently
small `ε>0`, `c≤ε L(log L)²` implies `T(c)≤(log N)^α`, where the existing
power-of-logarithm assembly requires `α<1/59`.

## Remaining proof obligations

1. Prove the scale-averaged autocorrelation's smoothness, derivative bounds,
   transform identity, and pointwise Fourier floor.
2. Derive the Gamma reserve and completed-conductor floor for this profile.
3. Track dependence on these floors through spectral confinement and residual
   assembly; choose a positive `ε` satisfying every resulting exponent bound.
4. Formalize the concrete positivity theorem without analytic assumptions.

## Gates

- [x] Precise target and existing inputs identified.
- [ ] Dependency-closed paper proof.
- [ ] Direct Lean checks, transitive axiom audit, umbrella integration.
