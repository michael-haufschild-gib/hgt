# F2 — Cauchy reflection has a sharp regularity boundary

- **Stage:** 3-formalized
- **Result:** The core reflection correction has exact order `1/2−2 Re s`. Its bounded `L²` realization exists exactly when `Re s≥1/4`; both directions are bounded exactly on `Re s=1/4`.
- **Scope:** The explicit Mellin correction of actual PM cores. This does not exclude other Mayer intertwiners or prove Krein positivity.

## Proof

For `0<Re s<1/2`, set `s♯=1/2−conjugate(s)`, `a_s(t)=symbol(2s,it)/Γℝ(2s)` and `B_s(t)=a_(s♯)(t)/conjugate(a_s(t))`. The actual core Mellin identity is proved in `ArithmeticMellinReflection`. The factors also make sense away from resonances.

All Gamma arguments have positive real part. Cancelling the common factor `Γ((1+it)/2)` in the two Cauchy symbols gives

`|B_s(t)|=C(s)|Γ(b+iτ)|/|Γ(a+iτ)|`,

where `a=Re s+1/2`, `b=1−Re s`, `τ=Im s−t/2`, and

`C(s)=|Γℝ(2s)Γ(s+1/2)| / |Γℝ(2s♯)Γ(s♯+1/2)| > 0`.

When `b≤a`, the vertical Gamma-ratio inequality gives the attained maximum `C(s)Γ(b)/Γ(a)` at `t=2 Im s`. The Gamma-ratio asymptotic gives

`|B_s(2(Im s−τ))| τ^(2 Re s−1/2) → C(s)`.

When `a<b`, the reciprocal Gamma ratio tends to zero. Any finite bound for `B_s` would then force `C(s)≤0`, a contradiction. Hence boundedness is equivalent to `Re s≥1/4`. Applying the same classification to `s♯` gives the two-direction criterion.

The symbol is continuous. A bounded multiplication operator must dominate its pointwise modulus, by testing interval indicators. Conversely the bounded symbol constructs the operator on all `L²(ℝ,dt)`. Its operator norm equals the attained maximum. Taking `s=1/8+i` excludes a bounded multiplication family throughout the full strip without any resonance assumption.

## Positive survivor

Exact norm, exact order, a sharp bounded half-strip and a constructed operator with its exact norm. The normalized theta fields still admit the universal physical antiunitary proved in `ArithmeticMellinReflection`. Off the critical line, this averaging correction requires a restricted domain or a change of function space.

## Lean

Module: `RenormalizedIntersectionTheory/MayerScattering/CauchyReflectionOrder`.

Endpoints: `norm_mayerCoreReflectionFactor`, `mayerCoreReflectionFactor_sharp_bound`, `mayerCoreReflectionFactor_frequency_order`, `mayerCoreReflectionFactor_bounded_iff`, `mayerCoreReflectionFactor_both_bounded_iff`, `norm_mayerCoreReflectionMultiplier`, `mayerCoreReflection_bounded_multiplier_iff`, `mayerCoreReflection_no_bounded_multiplier_family`.

Final plain `lake --old env lean` audit passed. All ten printed public endpoints depend only on `propext`, `Classical.choice`, `Quot.sound`. No added analytic premises.
