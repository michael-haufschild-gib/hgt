# Soft logarithmic profile compactness and sign rigidity

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** Review-1311 A158, B16, B17; attainment in the closed limiting domain and convergence of the rescaled profiles.
- **Statement:** The closed half-line form with Fourier symbol `log|ξ|` and potential `8(-u)` has a unique unit minimizing line with a nonnegative representative. Rescaled actual confining minimizers converge in `L²` to this line.
- **Status:** Full statement unproved; not counted. The [universal soft logarithmic limit](../3-formalized/universal-soft-logarithmic-confinement-limit.md) and compact `L²` closure of every unit Rayleigh sublevel are verified. Closed-domain attainment, sign rigidity, and profile convergence remain open.

The [closed-attainment paper proof](../2-fully-proven/soft-logarithmic-ground-state-attainment.md)
is followed by Lean formalization; its assembly remains unverified.

## Corpus connection

`FourierFirstMomentWindow` excludes spectral concentration at zero under a bounded physical first moment. Its optimized cutoff controls the negative logarithmic Fourier tail. Positive logarithmic Fourier energy and physical confinement give compactness.

For unit `L¹∩L²` profiles with first moment at most `M`, the verified bound is
`∫_{X>T}X|Fourier(f)|²≤(8+2M)(T+2)exp(-T/2)`, where
`X(ξ)=max(-log|ξ|,0)` and `T≥0`. The full negative part is integrable and
at most `16+4M`.
Choose the physical cutoff `H=exp(t/2)` in the window bound, then integrate
the resulting spectral distribution tail. The resulting verified coercivity
inequality is `Q(f)≥L₊(f)+4M(f)-16`, where `L₊` is positive logarithmic
Fourier energy: split `L=L₊-L₋` and use `L₋≤16+4M` against the potential
`8M`. `CausalReflection/SoftLogarithmicHalfLineCoercivity` proves the
decomposition, coercivity, and bounds on both nonnegative parts of every
unit Rayleigh sublevel. Its final plain source audit passes without warnings
and with exactly the standard three axioms; it is wired.
The closed-domain passage remains open; the
unitary `L²` limit must allow profiles outside `L¹`.
The layer-cake API is `MeasureTheory.lintegral_eq_lintegral_meas_lt`; its integrable real-valued version is `MeasureTheory.Integrable.integral_eq_integral_meas_lt`. Apply it to the measure with Fourier square density.

`HTGeometry/HardyBoundary/ExponentialDistributionTails` verifies the general
layer-cake step: `ν{X>t}≤C exp(-t/2)` gives
`∫_{X>T}X dν≤C(T+2)exp(-T/2)` for `T≥0`.
Both declarations pass final plain source audits with exactly the standard
three axioms and are wired. `FourierNegativeLogarithmicTail` also passes its
final plain source audit without warnings and with exactly those axioms;
all six declarations are wired. It proves the superlevel estimate, extended
and real tail bounds, integrability, and the full negative-part bound.
These supporting estimates are not counted as a separate contribution.

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

`HTGeometry.fourierMulCLM` realizes every capped negative-logarithm symbol
as a bounded operator on complex `L²`; continuity of its quadratic pairing
handles each fixed cap. An almost-everywhere Fourier subsequence and Fatou
transfer the uniform tail bound to the limit. Removing the caps passes
the negative term without requiring an ordinary Fourier integral for the
limit. These passages are verified in `SoftLogarithmicNegativePartContinuity`.

`HTGeometry.exists_subseq_ae_tendsto` supplies the almost-everywhere
subsequence directly from complex `L²` convergence. Applying it in physical
and unitary Fourier coordinates allows Fatou to preserve both positive
moments and each negative-logarithmic tail bound. Bounded nonnegative
weights define continuous quadratic forms through their square-root
multipliers; the uniform tail bound then removes the negative-logarithm cap.
This avoids any assumed `L¹` convergence of the limiting profile.

`HTGeometry/HardyBoundary/WeightedL2Fatou` verifies preservation of a
convergent upper bound on a nonnegative weighted square moment, including
the sum of two moments under separate strong `L²` limits. All four
declarations pass final plain source audits with the standard three axioms;
the module is integrated. `WeightedL2MomentContinuity` also passes its final
plain source audit with those axioms and is integrated. It proves
continuity for bounded weights, passage through uniform weighted tails,
and moment convergence from vanishing weighted error. Applying these
lemmas to the joint signed energy and proving recovery remain open.
`SoftLogarithmicNegativePartContinuity` is now audited and integrated with
the standard three axioms: bounded physical first moments give convergence
of the negative Fourier logarithmic energy along strong limits of unit trials.

`SoftLogarithmicClosedDomain` is audited and integrated with the standard
three axioms. It defines the literal finite-energy half-line domain in
complex `L²`, with almost-everywhere reality and support. Trial
representatives retain their energy. No exponential moment of the closed
profile is required.

The negative-logarithmic estimate has a homogeneous, adjustable form.
Writing `m=‖f‖₂²` and `M=∫|u||f(u)|²du`, use the cutoff
`H=c exp(t/2)`, with `c>0`, to obtain the candidate bound
`L₋(f)≤16cm+4M/c`. Thus the negative logarithmic part should have arbitrarily
small relative bound against the physical first moment. These bounds and
the limiting-domain passage remain unformalized.

`CriticalArithmeticCorrelationTheory.isCompact_closure_of_uniform_physical_and_fourier_tails` already supplies compactness from the two tails, without compact support. Its compact cutoff approximation uses `f-PQf=(f-Pf)+P(f-Qf)` and contractivity of the physical cutoff.

Every unit Rayleigh sublevel of the trial domain is relatively compact in `L²`.
The physical cutoff error squared is at most `M/H`; the Fourier cutoff
error squared is at most `L₊/log T`. The latter already has its exact
unitary identity in
`norm_sq_sub_fourierCutoff_central_eq_tailIntegral`. No exponential moment
bound uniform over the sublevel is needed. `SoftLogarithmicSublevelCompactness`
proves `isCompact_closure_softLogarithmicRayleighSublevel` using the literal
`L²` representatives. Its final plain source audit passes without warnings
and with exactly the standard three axioms; it is wired. The
general helper `HTGeometry/HardyBoundary/LogarithmicMomentCompactness`
passes its final plain source audit without warnings and with exactly the
standard three axioms; it is wired. These compactness results are not counted
separately from the remaining attainment problem.

The finite trial infimum supplies normalized trials with energies in
`[μ,μ+1/(n+1)]`. Compactness of the sublevel `μ+1` gives a strongly
convergent minimizing sequence with unit limit. The uniform rescaled-energy
limit also places every sufficiently confined actual minimizer in this
same sublevel; the entire family has compact `L²` closure.
`SoftLogarithmicCompactProfiles` proves both unconditional statements:
`exists_softLogarithmic_strong_minimizingSequence` and
`exists_isCompact_closure_rescaledConfiningMinimizerFamily`. Its final plain
source audit passes without warnings, with exactly the standard three
axioms; it is integrated. Neither theorem identifies the limit's energy.

`CanonicalSystemOfTheWindowTower.hasLogarithmicEnergy_cutoff` preserves the closed `L²` logarithmic domain under bounded Lipschitz multiplication. `logarithmicCutoff_translation_loss_le` supplies a common integrable jump majorant. Recovery can use dominated convergence of those jump losses, followed by comparison of the positive reference weight with `log⁺|ξ|`.

For recovery choose cutoffs equal to one on `[-N,0]`, zero below `-2N`,
bounded by one, and with Lipschitz constant at most one. For `N≥2`, the
existing choice `χ_N(u)=logarithmicEndpointCutoff N (-u)` has these properties.
The error
`(1-χ_N)f` tends to zero in `L²`; at each fixed shift its translation
defect tends to zero by the unitary bound `‖T_hg-g‖≤2‖g‖`. Thus dominated
convergence is needed only in the shift variable. The existing loss inequality bounds its squared
defect by `2‖T_hf-f‖²+2h²‖f‖²`. This is integrable against the reference
Lévy density `exp(-h)/(2h)`. Dominated convergence would therefore give
convergence in the positive logarithmic form norm. The first-moment term
converges by physical domination, and the negative logarithmic term by the
uniform tail estimate. No exponential moment of the limit is needed.

`MeasureTheory.tendsto_lpBoundedMulCLM_apply` supplies the strong cutoff
convergence directly from the bounded pointwise multipliers.

Normalize the compact cutoffs after their `L²` norms approach one. Their
first moments stay bounded, so the verified unit `L¹∩L²` negative-tail
estimate applies throughout recovery. This removes the need for a separate
Fourier-window estimate on arbitrary nonintegrable `L²` profiles.

`suzukiFinitePartEnergy_absolute_split` identifies the loss under modulus with a positive cross-sign interaction for the exact `1/|x-y|` kernel. `suzukiFinitePartEnergy_absolute_lt_of_sign_change` proves strict loss on a bounded smooth core. `SuzukiLimitingLogClosedMarkov` transfers contractions to a closed form on a fixed interval.

## Missing bridges

1. Pass signed energy to the strong limit and prove cutoff recovery in the constructed closed domain. Compact physical cutoffs with finite logarithmic energy already belong to the trial class; smoothness is unnecessary for comparing its infimum. Do not assume that the limiting minimizer has an exponential moment.
2. Transfer the exact logarithmic modulus identity from bounded cores to this domain; prove strict loss for two nonzero sign parts.
3. Use rescaled near-minimality from the universal confinement limit to obtain convergence to the unique minimizing line.

The limiting domain may be larger than the union of positive exponential domains used for trial functions. Attainment in that trial class is not part of the conjecture.

An alternative uniqueness route uses causal reflection. The verified
`realCausalReflection_weighted_energy` preserves mass and gives exact
exponential-mass loss. Its derivative at zero suggests
`M(F)-M(H)=(2a/π)∫K²`, with `H` the reflected profile and `K` its causal
resolvent. Fourier modulus preservation would then give strict soft-energy
loss at a positive real Laplace zero. The existing Laplace-ratio argument
would imply uniqueness of the minimizing line without first proving sign
rigidity. The derivative identity remains unformalized. The dominated
Laplace-derivative proof in `LaplaceTransformMomentDerivative` supplies a
mechanism using a smaller exponential rate.

The weighted identity already applies to arbitrary complex `L²` inputs
(`integral_weighted_causalBlaschkeStep_energy`). For a causal profile with
a Laplace zero, use damping `x<0`, then let `x↑0`. Nonnegative difference
quotients should first bound the reflected first moment by the original
one, then identify their difference as `(2a/π)‖K‖₂²`. This avoids any
exponential moment of a closed profile. `causalExponential_op_fourier`
provides the nonvanishing resolvent multiplier, hence injectivity and
Fourier-modulus preservation for the reflection. The moment-limit and
closed-domain bridges remain unformalized.

For nonnegative `w,q`, the quotient `(1-exp(-tw))q/t` lies between zero
and `wq` and tends pointwise to `wq` as `t↓0`. Dominated convergence
recovers a finite first moment; Fatou first supplies finiteness if the
quotient integrals are uniformly bounded. This applies to the reflected
profile before its first-moment integrability is known. The elementary
exponential slope proof in `HilbertMetric/GaussianJetPositivity` supplies
the pointwise limit; the integral bridge remains unformalized.

More precisely, for `0<t<a` let `W_t(G)=∫exp(2πtu)|G(u)|²du` and
`A_t(G)=(‖G‖₂²-W_t(G))/t`. Equal ordinary masses and the exact reflection
identity give `A_t(F)=A_t(H)+4aW_t(K)`. Hence
`A_t(H)≤2πM(F)`. Fatou yields `M(H)<∞`; dominated convergence then gives
`2πM(F)=2πM(H)+4a‖K‖₂²`. Fourier-modulus preservation would yield
`Q(F)-Q(H)=(16a/π)‖K‖₂²`. Injectivity of the resolvent makes this strict
for nonzero `F`, excluding a Laplace zero of a unit ground state.

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
