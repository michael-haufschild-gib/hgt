# F2 — actual Cauchy averaging forces the reflection boundary

- **Stage:** 3-formalized
- **Result:** Compatibility with the actual unweighted logarithmic Cauchy operator forces a unique correction. A bounded compatible conjugate-linear reflection exists exactly for `Re s≥1/4`.
- **Scope:** Source averaging, actual theta-field and PM-core columns. Full Mayer transfer intertwining and Krein positivity remain open.

## Proof

For `0<Re s<1/2`, put `s♯=1/2−conjugate(s)`. In logarithmic Haar coordinates, actual normalized Cauchy averaging is convolution by `k_s(x)=Γℝ(2s)⁻¹K_(2s)(exp(−x))`. Its zeroth absolute Mellin moment is finite. The literal Fourier transform is `a_s(2πξ)`, where `a_s(t)=symbol(2s,it)/Γℝ(2s)`. Thus convolution defines a bounded operator `A_s` on all `L²(ℝ)`. The symbol is continuous and nowhere zero. Both `A_s` and its adjoint are injective, hence both have dense range.

The arithmetic field antiunitary has Fourier action `F(Jf)(ξ)=phase(2πξ) conjugate(Ff(ξ))`, with unimodular phase. Its phase cancels in `J A_s J`, giving the actual adjoint `A_s†`. Therefore `R_s A_s=A_(s♯) J`, with `R_s=T_s J`, is equivalent to `T_s A_s†=A_(s♯)`.

No multiplier form is assumed for `T_s`. After conjugation by Fourier transform, test the factorization on an interval indicator near frequency `ξ₀`. If `|a_(s♯)(2πξ₀)|>‖T_s‖|a_s(2πξ₀)|`, continuity gives constants `L>‖T_s‖U` on a small interval, with the numerator at least `L` and denominator at most `U`. The indicator then has image norms satisfying `L‖f‖≤‖T_s‖U‖f‖`, a contradiction. Consequently `|B_s(t)|≤‖T_s‖`, where `B_s=a_(s♯)/conjugate(a_s)`.

The sharp Gamma-quotient classification gives necessity `Re s≥1/4`. In that half-strip, the Fourier multiplier `B_s(2πξ)` constructs `T_s` and satisfies the exact factorization. Dense range of `A_s†` gives uniqueness. The interval-test lower bound and symbol upper bound give `‖T_s‖=|B_s(2 Im s)|`.

Every actual upper-resonant core has integrable logarithmic representative by its imaginary-axis Mellin convergence. Its two endpoint bound makes that representative bounded, hence also `L²`. The literal core Mellin identity proves `A_s g_s=c_s` for actual normalized theta-field and core columns. Together with `Jg_s=g_(s♯)`, compatibility gives `R_s c_s=c_(s♯)` wherever the bounded reflection exists.

On `Re s=1/4`, the reflected parameter equals `s`, so `B_s=a_s/conjugate(a_s)` is unimodular. The corrected Fourier conjugation therefore squares to the identity and preserves the physical Haar norm. This is an actual core-compatible antiunitary on the entire line.

## Consequence

The fixed-Haar obstruction is forced by the actual averaging bridge, not by a multiplier ansatz. This does not exclude operators on a different weighted Lewis space or prove positivity of the PM coefficient pairing.

## Lean

Module: `RenormalizedIntersectionTheory/MayerScattering/CauchyCompatibleReflection`.

Endpoints: `mayerFieldReflection_cauchy_adjoint`, `mayerCauchy_bounded_factorization_iff`, `mayerCauchy_factorization_unique`, `norm_mayerCauchyReflectionCorrection`, `mayerCauchyHaarOperator_column`, `mayerCauchyReflection_column`, `mayerCauchy_bounded_compatible_reflection_iff`, `mayerCauchy_compatible_reflection_unique`, `mayerCauchyReflection_involutive_critical`, `norm_mayerCauchyReflection_critical`.

Final plain `lake --old env lean` check passed without warnings. All nineteen printed endpoints depend only on `propext`, `Classical.choice`, `Quot.sound`.
