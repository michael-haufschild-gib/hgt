# Denjoy–Carleman rough-regime positivity

- **ID:** denjoy-carleman-rough-regime
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0111/route-obstacles.md`, A3.
- **Statement:** A fixed nonnegative logarithmic Denjoy–Carleman profile on `[0,1]`
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
`ĝ(t)≥exp(-C t/log²t)` for large `t`, with `C=8π/3+3000`. Compact support makes `f̂` analytic;
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

Take `α=1/256`, low-conductor exponent `q=1/16`, and quotient parameter `k=8`.
The complete form retains `aT⁻⁷` of the prime defect at mass cost `CT⁹` once
`N≥HT⁸`. Thus bounded-energy vectors have defect `O(T¹⁶)` and admit a
conductor cutoff with `log R≤C_R T¹⁶+log Q`, `Q=⌊(log N)^q⌋`.
For large `N`, `1+log R≤(log N)^(1/4)`, so the orthogonal cross error is
bounded independently of actual overlap. The residual budget is controlled by
`5q+19α+1/k<1`; intermediate-band leakage by `8α<q`; and the coercivity
gap by `q/4>α`. These inequalities hold for the stated parameters.
Low-band decoupling sends any nonpositive unit vector to an orthogonal unit
vector of energy at most `2`. Confinement retains squared norm at least `3/4`
and energy at most `3`; intermediate-band coercivity instead gives energy at
least `(1/4)log Q−log c−C_coerc`, eventually larger than `3`.
This contradiction proves positivity on every nonzero vector.
The critical coefficient is
`ε=(1/256)/(4B)`, with `B=808C`. Bounded overlaps use the existing uniform
zero-free-profile theorem. Since `sincCriticalOverlap N≤96e·dcScale N`
eventually, replacing `ε` by `ε/(96e)` gives the exact critical-scale version.

## Lean declarations

Namespace `GaloisForLFunctions.TransMetzlerWeilPositivity`.
Modules lie in `formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ReceiverRate/`.

- `TheZeroFreeLogarithmicProfile.lean`: `zeroFreeLogProfile`,
  `integral_abs_iteratedDeriv_zeroFreeLogProfile_le`,
  `paperFT_zeroFreeLogProfile_ne_zero`.
- `TheLogarithmicProfileIsPositiveBelowCriticalOverlap.lean`:
  `exists_zeroFreeLogProfile_positive_power_budget`,
  `exists_zeroFreeLogProfile_completeWeilMatrix_posDef_critical_overlap`,
  `exists_zeroFreeLogProfile_completeWeilMatrix_posDef_sincCritical_overlap`.

All three final theorems passed a direct Lean check, with transitive axioms
`[propext, Classical.choice, Quot.sound]` only. All twelve modules are imported
by the programme umbrella. Direct final checks of the eleven dependency
modules remain pending.

## Gates

- [x] Precise target and existing inputs identified.
- [x] Dependency-closed paper proof.
- [ ] Direct Lean checks, transitive axiom audit, umbrella integration.
