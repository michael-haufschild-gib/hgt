# Soft logarithmic profile compactness and sign rigidity

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Target:** Review-1311 A158, B16, B17; attainment in the closed limiting domain and convergence of the rescaled profiles.
- **Statement:** The closed half-line form with Fourier symbol `log|ξ|` and potential `8(-u)` has a unique unit minimizing line with a nonnegative representative. Rescaled actual confining minimizers converge in `L²` to this line.
- **Status:** Unproved; not counted. The [universal soft logarithmic limit](../3-formalized/universal-soft-logarithmic-confinement-limit.md) is verified; compactness, domain recovery, and sign rigidity remain missing.

## Corpus connection

`FourierFirstMomentWindow` excludes spectral concentration at zero under a bounded physical first moment. Optimizing its cutoff should also control the negative logarithmic Fourier tail. Positive logarithmic Fourier energy and physical confinement would then give compactness.

The concrete candidate bound, for unit profiles with first moment at most `M`, is
`∫_{|ξ|≤exp(-T)}(-log|ξ|)|Fourier(f)|²≤(8+2M)(T+2)exp(-T/2)` for `T≥0`.
Choose the physical cutoff `H=exp(t/2)` in the window bound, then integrate the resulting spectral distribution tail. At `T=0` this would give `Q(f)≥L₊(f)+4M(f)-16`, where `L₊` is positive logarithmic Fourier energy. Thus bounded limiting energy would control both confinement and high-frequency tails. The extension to the unitary `L²` Fourier transform must allow profiles outside `L¹`.
The layer-cake API is `MeasureTheory.lintegral_eq_lintegral_meas_lt`; its integrable real-valued version is `MeasureTheory.Integrable.integral_eq_integral_meas_lt`. Apply it to the measure with Fourier square density.

For the `L²` extension, split `f=P_Hf+(1-P_H)f` directly in the unitary
Fourier space. Only the compact part needs an ordinary Fourier integral;
Cauchy–Schwarz gives its `L¹` bound, while unitarity controls the far part.
The existing spatial first-moment tail estimate is unchanged.

Closed attainment can instead start with rescaled actual minimizers from
`universal_softLogarithmic_confinement_limit`. They already lie in `L¹`,
their limiting energies approach `μ`, and their first moments approach
`1/8`. The existing Fourier-window estimate therefore applies to the whole
approximating sequence. Uniform negative-logarithmic tails bound the
negative part; the known energy and first-moment limits then bound the
positive logarithmic part. These bounds and physical tightness would give
an `L²` limit. Fatou controls
its positive logarithmic energy and first moment; uniform integrability
passes the negative logarithmic term. Compact cutoff recovery then proves
the reverse variational inequality. This route does not require a separate
window theorem for arbitrary nonintegrable `L²` profiles before compactness.

The negative-logarithmic estimate has a homogeneous, adjustable form.
Writing `m=‖f‖₂²` and `M=∫|u||f(u)|²du`, use the cutoff
`H=c exp(t/2)`, with `c>0`, to obtain the candidate bound
`L₋(f)≤16cm+4M/c`. Thus the negative logarithmic part should have arbitrarily
small relative bound against the physical first moment. These bounds and
the limiting-domain passage remain unformalized.

`CriticalArithmeticCorrelationTheory.isCompact_closure_of_uniform_physical_and_fourier_tails` already supplies compactness from the two tails, without compact support. Its compact cutoff approximation uses `f-PQf=(f-Pf)+P(f-Qf)` and contractivity of the physical cutoff.

`CanonicalSystemOfTheWindowTower.hasLogarithmicEnergy_cutoff` preserves the closed `L²` logarithmic domain under bounded Lipschitz multiplication. `logarithmicCutoff_translation_loss_le` supplies a common integrable jump majorant. Recovery can use dominated convergence of those jump losses, followed by comparison of the positive reference weight with `log⁺|ξ|`.

`suzukiFinitePartEnergy_absolute_split` identifies the loss under modulus with a positive cross-sign interaction for the exact `1/|x-y|` kernel. `suzukiFinitePartEnergy_absolute_lt_of_sign_change` proves strict loss on a bounded smooth core. `SuzukiLimitingLogClosedMarkov` transfers contractions to a closed form on a fixed interval.

## Missing bridges

1. Construct the closed soft half-line domain; derive the two uniform tails and cutoff recovery. Compact physical cutoffs with finite logarithmic energy already belong to the trial class; smoothness is unnecessary for comparing its infimum. Do not assume that the limiting minimizer has an exponential moment.
2. Transfer the exact logarithmic modulus identity from bounded cores to this domain; prove strict loss for two nonzero sign parts.
3. Use rescaled near-minimality from the universal confinement limit to obtain convergence to the unique minimizing line.

The limiting domain may be larger than the union of positive exponential domains used for trial functions. Attainment in that trial class is not part of the conjecture.

## Stronger questions exposed by the domain distinction

The original exponential-moment trial class may have no minimizer. The
finite-part `1/|x-y|` interaction suggests an algebraic tail for the closed
ground state. A proposed contradiction to exponential decay tests its weak
equation against a nonnegative compact bump translated far into the half-line:
the distant interaction with fixed positive mass is of order `-1/x`, while
the local linear-potential pairing would decay exponentially. This requires
an actual off-support logarithmic-operator formula and modulus rigidity;
neither has yet been transferred to the full half-line domain. No no-go is
claimed, and the positive survivor to prove is attainment and uniqueness in
the closed domain.

An alternative could avoid modulus rigidity in this nonattainment step.
Expanding the far-bump logarithmic kernel to every inverse power would
force all signed moments of an exponentially decaying weak eigenfunction
to vanish. `HTGeometry.ae_eq_zero_of_forall_moment_eq_zero` then supplies
rigidity: use the finite measure `exp(-c|x|)dx` and density
`F(x)exp(c|x|)`, choosing `c` below the available square-moment exponent.
The off-support operator formula, all-order expansion, and exponentially
small tail pairing still require proof; this is only an alternative route.

Modulus rigidity may also pass through the actual Gamma form. Compress a
trial profile, use the Lévy contraction inequality, then take the verified
Gamma/logarithm limit. Opposite-sign mass on two separated bounded sets
gives a fixed positive jump loss under this rescaling, so strictness should
survive the limit. The audited `HalfLineGammaContractions` module supplies
the needed nonlinear-domain bridge.

If closed attainment and cutoff recovery hold, dilation of a limiting
minimizer forces its first moment to be `1/8`. Together with the universal
actual-moment limit, compactness should upgrade convergence to both the
first-moment weighted norm and the positive logarithmic Fourier norm. These
stronger convergence claims remain conjectures.
