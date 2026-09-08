# HB original joint response: causal Laplace identification

- **Stage:** 1-in-progress.
- **Goal:** unconditional formal RH proof/falsification; open.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

The [causal Laplace kernel](../3-formalized/hb-joint-causal-laplace-kernel.md)
is constructed in the original spatial Hilbert space. For every fixed spatial
F, one frequency-independent K_F vanishes almost everywhere before time zero,
admits every positive exponential L² damping on positive time, and has an
absolutely convergent Bochner Laplace transform equal to the original spatial
response throughout `Re(w)>0`.

The proof identifies the response with its actual form-pencil inverse,
derives Hardy estimates from the proved resolvent bound, and applies the
corpus's Paley–Wiener theorem. Fourier/probe compatibility and Bochner tensor
totality assemble one vector kernel. Laplace injectivity proves independence
of every auxiliary damping choice, removing the temporary restriction to a
smaller half-plane. Classical coordinate regularity is not a prerequisite for
this time-support and transform identity.

The [original time-source identification](../3-formalized/hb-original-time-source-onset-identification.md)
retains the fixed delayed onset and its actual derivative. The original reduced
frequency polynomial is affine; its slope is twice the explicit lift's radial
derivative. The actual full angular time-source identity, its convergent
Laplace transform, and the differentiated lift's transform are proved. The
native square remainder is an admitted spatial L² vector at every time and
vanishes before static time zero.

The [horizon-decay and joint Bochner theorem](../3-formalized/hb-original-source-horizon-bochner-transform.md)
proves that both reduced radial coefficients contain the exact horizon factor
`exp(2t)`. The actual native source vector is strongly continuous and satisfies
`||S(tau)|| <= C_c exp(-c tau)` for every `c<2`. Its Bochner Laplace integral
converges in norm throughout `Re(w)>-2` and equals the literal frequency source
with its original amplitude, physical onset transform and native angular
remainder retained. Absolute Fubini against every radial L² test supplies the
joint integral/completion interchange for this channel.

The [principal causal evolution and cutoff-source transform](../3-formalized/hb-principal-causal-evolution-and-cutoff-source.md)
constructs all three principal time families from their actual amplitudes,
native delayed forcing and complex potentials. The physical sine operator is
`sin(2*pi*tau*<D>)/(2*pi*<D>)`; multiplication by
`(2*pi)^2+k*(k-1)*sech(t)^2` supplies the bounded perturbation. The construction
retains the original Fourier normalization and the exact odd extension of the
negative-ray source. Each response is continuous, causal, unique among
continuous integral solutions, C¹ in time, and has zero Cauchy data. It gains
an exact spatial inverse-frequency factor and has a norm-convergent Bochner
transform in a common nonempty right half-plane.

All three original cutoff commutators, horizon factors and angular completion
maps are retained. Their sum with the native square remainder is one admitted,
continuous causal spatial source. Its Bochner transform is proved equal to the
native transform plus all three constructed cutoff-response transforms.

The immediate hard obligation is equality of the constructed principal
Laplace transform with `principalDifference` at the original onset transform.
The original second-order radial equation and endpoint trace must be proved
first. Oddness of an L² class alone supplies no pointwise trace. Until this
identification is closed, the assembled transform is not identified with
`cuspResidualVector`.

The [second time derivative and spatial-range theorem](../3-formalized/hb-principal-causal-second-order-wave.md)
proves that the actual native source is C¹ in the original L² norm. Its
derivative retains both onset jets and the full `exp(2t)` horizon bound.
Consequently the effective forcing `G=F+W*U` is C¹. Two exact integrations by
parts, with the initial boundary terms retained and then evaluated from the
proved zero data, establish continuous `U''` and
`U=A^(-2)[F+W*U-U'']`, where `A=2*pi*<D>`. This twice-regularized wave identity
is proved for every actual principal channel, without additional regularity
premises.

The next obligation is to identify this spatial range with the original
radial differential expression and construct its continuous representative
and endpoint trace. The existing Schwartz Fourier identity fixes the exact
`4*pi^2` normalization. Then identify the negative-ray restriction of
`principalTimeLaplace` with `principalDifference` at the original onset
transform. This trace and Green comparison remains open. The immediate construction identifies
`kgFreqInvOp` with the actual Bessel potential on tempered distributions.
The second-order graph then gives the original distributional radial equation
and Sobolev admission; Fourier L¹ synthesis will supply the continuous
representative required to turn the proved spatial oddness into a zero trace.

Convolution of the complete source with the original joint causal response,
metric finite propagation, modular patching and constrained Einstein sectors
still need their physical identifications. Continue the resulting response to
the physical left-QNM pairing and evaluate the retained spin-two/AIME source.
Independent Hawking-clock extinction remains open. The Volterra estimate
allows exponential growth; it supplies no Xi-zero selection. The enlarged
native source chamber `Re(w)>-2` does not continue the response inverse there.

No numerical experiment is indicated; the construction uses analytic estimates
and the existing Fourier, Klein–Gordon and Volterra corpus. The frontier map
remains read-only.
