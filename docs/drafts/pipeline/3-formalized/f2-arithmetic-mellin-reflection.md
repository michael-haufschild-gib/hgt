# F2 — arithmetic reflection of actual theta fields

- **Stage:** 3-formalized
- **Result:** A universal antiunitary on logarithmic Haar `L²` exchanges Gamma-normalized resonant theta fields. Actual Cauchy-averaged PM cores obey the corresponding Mellin identity with an extra explicit multiplier.
- **Scope:** Actual fields and core transforms. This does not identify the coefficient Krein form with a positive physical metric or intertwine the full Mayer transfer family.

## Proof

Let `w=2s`, `w♯=1−conjugate(w)`, and `G_s(a)=Γℝ(w)fieldCore_w(a)`. The theta integral gives

`M G_s(u)=4ξ(u)ξ(w−u)/[u(u−1)(w−u)(w−u−1)]`

on the initial Mellin strip. At a resonance, the ordinary integral extends holomorphically to `Re w−1<Re u<1`. Continuity therefore gives the polynomial-cleared identity on `u=it`. For `t≠0`, all denominator factors are nonzero. The functional equation and conjugation law of xi give

`M G_(s♯)(it)=S(t) conjugate(M G_s(it))`,

`S(t)=((it+1)/(it−1)) ξ(it)/ξ(−it)`.

Xi has no zero on the imaginary axis. Thus `S` is continuous and `|S(t)|=1`; continuity proves the reflection identity also at `t=0`.

The resonant endpoint bound and reciprocity bound `G_s(a)` by a constant times `min(a⁻¹,a^(1−Re w))`. Hence `g_s(v)=G_s(exp(−v))` is bounded and integrable, therefore square-integrable. Its Fourier transform is `M G_s(2πiξ)`.

On frequency space define `T F(ξ)=S(2πξ) conjugate(F(ξ))`; set `J=Fourier⁻¹ T Fourier`. Unimodularity gives `J²=Id`, norm preservation and conjugate linearity on all `L²(ℝ)`. The literal Fourier representatives prove `Jg_s=g_(s♯)`.

For `a_s(t)=symbol(2s,it)/Γℝ(2s)`, absolutely convergent Cauchy convolution gives `M core_s(it)=a_s(t)M G_s(it)`. The symbol never vanishes on this line. Therefore

`M core_(s♯)(it)=[a_(s♯)(t)/conjugate(a_s(t))] S(t) conjugate(M core_s(it))`.

The Gamma normalization and Cauchy symbol are retained exactly.

## Lean

Module: `RenormalizedIntersectionTheory/MayerScattering/ArithmeticMellinReflection`.

Endpoints: `mayerFieldMellin_reflect`, `mayerFieldLog_memLp`, `norm_mayerFieldReflection`, `mayerFieldReflection_involutive`, `mayerFieldReflection_add`, `mayerFieldReflection_smul`, `mayerFieldReflection_column`, `mayerPeriodCore_hasMellin_imaginary`, `mayerPeriodCore_mellin_reflect`.

Final individual plain Lean audit passed without warnings. All eleven printed public endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`. The module is imported by the RIT umbrella.

The extra Cauchy factor’s sharp norm and domain classification is tracked [separately](../1-in-progress/f2-cauchy-reflection-order.md).
