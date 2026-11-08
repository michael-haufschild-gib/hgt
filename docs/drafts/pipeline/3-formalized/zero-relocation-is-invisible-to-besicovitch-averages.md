# Rational zero relocation is invisible to mean spectra

- **ID:** zero-relocation-is-invisible-to-besicovitch-averages
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The literal symmetric rational relocation multiplier preserves zeta's mean-square class and Fourier means above the critical line, while destroying every absolutely convergent ordinary Dirichlet-series realization.

## Exact result

Let `R=zeroRelocationFactor ρ γ₁ γ₂` and `F=ζR`, using the monic normalization `R(σ+it)→1`.
For every `σ>1/2`, `σ≠1`,

`(1/T) ∫₀ᵀ |F(σ+it)−ζ(σ+it)|² dt → 0`.

For every real frequency `λ`, the Fourier mean of that difference is zero.
For `1/2<σ<1`, the perturbed function has exactly the Carlson mean
`Σ_(n≥1) n^(-2σ)`, coefficient `n^(-σ)` at frequency `log n`, and zero coefficient elsewhere.
When `Re ρ>1/2`, on every line `σ>1` the same perturbed function is not Bohr almost periodic and admits no absolutely convergent ordinary Dirichlet series.

No RH assumption is used. The result is about the literal multiplier on the stated vertical lines; it does not construct an AAL counterexample for actual zeta.

## Proof

If continuous `f,g≥0` satisfy bounded Cesàro means for `f` and `g(t)→0`, split the integral at a fixed height `L`. The prefix contributes `O(1/T)`. Above `L`, choose `g≤ε`, so the tail is bounded by `ε` times the bounded mean of `f`. Hence the mean of `fg` tends to zero.

Apply this to `f=|ζ|²`, first with `g=|R−1|²`, then with `g=||R|²−1|`. Carlson's theorem supplies the bounded means in the strip; absolute convergence supplies them for `σ>1`. The first choice gives zero square-mean error; the second preserves square means.

The inequality `x≤a/2+x²/(2a)`, integrated and then sent to `a→0`, turns zero square mean into zero mean absolute mass. Every unit-modulus character therefore has zero pairing with the error. Existing zeta Fourier means give the exact coefficients. Finally, the existing Bohr-rigidity theorem excludes an exact ordinary Dirichlet representation of the perturbed function despite the identical limiting means.

## Scope corrections

- Integrals start at `0`, so `σ=1` is excluded: the pole obstructs a finite square mean on that interval.
- The argument needs only `R→1`; it does not assert finite total `L²` transient energy or require an `O(t^-2)` estimate.
- A separate condition `R(1)=1` is not automatic. Rescaling to impose it changes the vertical limit unless it already holds.
- Mean-spectrum invariance does not imply blindness of every high-height statistic: [quadratic and quartic vertical traces](the-vertical-trace-of-zero-relocation.md) detect every off-line target.

## Lean certificate

Module: `ArithmeticPositiveDuality/FiniteZeroRelocationPreservesTheMeanSpectrum.lean`.
Capstones: `relocatedZeta_error_meanSquare`, `relocatedZeta_meanSquare`,
`relocatedZeta_error_fourierMean`, `relocatedZeta_fourierMean_log`,
`relocatedZeta_fourierMean_off_spectrum`,
`zeroRelocation_meanInvisible_but_not_dirichlet`.

The final direct `lake --old env lean` check passed without warnings.
All six capstones have exactly `propext`, `Classical.choice`, `Quot.sound`.
The module is imported by its umbrella. The invariant-mean mechanism is standard analysis; the certified application identifies precisely which zeta data the literal relocation preserves.
