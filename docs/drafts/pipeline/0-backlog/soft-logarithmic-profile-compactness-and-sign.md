# Soft logarithmic profile compactness and sign rigidity

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Target:** B16, B17; signed ground states and the shape behind the confining margin.
- **Statement:** The closed half-line form with Fourier symbol `log|ξ|` and potential `8(-u)` has a unique unit minimizing line with a nonnegative representative. Rescaled actual confining minimizers converge in `L²` to this line.
- **Status:** Unproved; not counted. The universal soft logarithmic limit is a prerequisite still undergoing Lean verification.

## Corpus connection

`FourierFirstMomentWindow` excludes spectral concentration at zero under a bounded physical first moment. Optimizing its cutoff should also control the negative logarithmic Fourier tail. Positive logarithmic Fourier energy and physical confinement would then give compactness.

The concrete candidate bound, for unit profiles with first moment at most `M`, is
`∫_{|ξ|≤exp(-T)}(-log|ξ|)|Fourier(f)|²≤(8+2M)(T+2)exp(-T/2)` for `T≥0`.
Choose the physical cutoff `H=exp(t/2)` in the window bound, then integrate the resulting spectral distribution tail. At `T=0` this would give `Q(f)≥L₊(f)+4M(f)-16`, where `L₊` is positive logarithmic Fourier energy. Thus bounded limiting energy would control both confinement and high-frequency tails. The extension to the unitary `L²` Fourier transform must allow profiles outside `L¹`.
The layer-cake API is `MeasureTheory.lintegral_eq_lintegral_meas_lt`; its integrable real-valued version is `MeasureTheory.Integrable.integral_eq_integral_meas_lt`. Apply it to the measure with Fourier square density.

`CriticalArithmeticCorrelationTheory.isCompact_closure_of_uniform_physical_and_fourier_tails` already supplies compactness from the two tails, without compact support. Its compact cutoff approximation uses `f-PQf=(f-Pf)+P(f-Qf)` and contractivity of the physical cutoff.

`CanonicalSystemOfTheWindowTower.hasLogarithmicEnergy_cutoff` preserves the closed `L²` logarithmic domain under bounded Lipschitz multiplication. `logarithmicCutoff_translation_loss_le` supplies a common integrable jump majorant. Recovery can use dominated convergence of those jump losses, followed by comparison of the positive reference weight with `log⁺|ξ|`.

`suzukiFinitePartEnergy_absolute_split` identifies the loss under modulus with a positive cross-sign interaction for the exact `1/|x-y|` kernel. `suzukiFinitePartEnergy_absolute_lt_of_sign_change` proves strict loss on a bounded smooth core. `SuzukiLimitingLogClosedMarkov` transfers contractions to a closed form on a fixed interval.

## Missing bridges

1. Construct the closed soft half-line domain; derive the two uniform tails and cutoff recovery. Compact physical cutoffs with finite logarithmic energy already belong to the trial class; smoothness is unnecessary for comparing its infimum. Do not assume that the limiting minimizer has an exponential moment.
2. Transfer the exact logarithmic modulus identity from bounded cores to this domain; prove strict loss for two nonzero sign parts.
3. Use rescaled near-minimality from the universal confinement limit to obtain convergence to the unique minimizing line.

The limiting domain may be larger than the union of positive exponential domains used for trial functions. Attainment in that trial class is not part of the conjecture.
