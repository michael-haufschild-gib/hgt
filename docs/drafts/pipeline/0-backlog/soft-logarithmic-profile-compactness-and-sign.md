# Soft logarithmic profile compactness and sign rigidity

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Target:** B16, B17; signed ground states and the shape behind the confining margin.
- **Statement:** The closed half-line form with Fourier symbol `log|ξ|` and potential `8(-u)` has a unique unit minimizing line with a nonnegative representative. Rescaled actual confining minimizers converge in `L²` to this line.
- **Status:** Unproved; not counted. The universal soft logarithmic limit is a prerequisite still undergoing Lean verification.

## Corpus connection

`FourierFirstMomentWindow` excludes spectral concentration at zero under a bounded physical first moment. Optimizing its cutoff should also control the negative logarithmic Fourier tail. Positive logarithmic Fourier energy and physical confinement would then give compactness.

`suzukiFinitePartEnergy_absolute_split` identifies the loss under modulus with a positive cross-sign interaction for the exact `1/|x-y|` kernel. `suzukiFinitePartEnergy_absolute_lt_of_sign_change` proves strict loss on a bounded smooth core. `SuzukiLimitingLogClosedMarkov` transfers contractions to a closed form on a fixed interval.

## Missing bridges

1. Construct the closed soft half-line domain and prove compactness and compact-core recovery. Do not assume that its minimizer has an exponential moment.
2. Transfer the exact logarithmic modulus identity from bounded cores to this domain; prove strict loss for two nonzero sign parts.
3. Use rescaled near-minimality from the universal confinement limit to obtain convergence to the unique minimizing line.

The limiting domain may be larger than the union of positive exponential domains used for trial functions. Attainment in that trial class is not part of the conjecture.
