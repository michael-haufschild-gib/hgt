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

The [original causal cusp-source transform](../3-formalized/hb-original-causal-cusp-source-transform.md)
closes the endpoint Green comparison. Each actual principal Laplace profile
equals `principalDifference` at the original onset transform, pointwise on the
negative ray and almost everywhere in the original L² class. Consequently the
complete causal source's absolutely convergent Bochner transform equals
`cuspResidualVector` throughout
`Re(w)>max(causalPrincipalThreshold q, principalThreshold q)`.
The original joint causal response to this identified complete time source is
constructed below. Its physical QNM continuation and left pairing remain open.

The [second time derivative and spatial-range theorem](../3-formalized/hb-principal-causal-second-order-wave.md)
proves that the actual native source is C¹ in the original L² norm. Its
derivative retains both onset jets and the full `exp(2t)` horizon bound.
Consequently the effective forcing `G=F+W*U` is C¹. Two exact integrations by
parts, with the initial boundary terms retained and then evaluated from the
proved zero data, establish continuous `U''` and
`U=A^(-2)[F+W*U-U'']`, where `A=2*pi*<D>`. This twice-regularized wave identity
is proved for every actual principal channel, without additional regularity
premises.

The [original radial equation and endpoint-trace theorem](../3-formalized/hb-principal-original-radial-equation-and-trace.md)
identifies `kgFreqInvOp` with the actual distributional Bessel potential.
The exact `4*pi^2` normalization turns the proved spatial graph into
`U''-Delta U=F+V U`, with the original complex potential and no auxiliary
mass. Every actual time slice belongs to spatial Sobolev order two and has a
unique continuous representative. Its proved oddness gives zero pointwise
trace and zero negative-ray boundary limit. Interior Schwartz tests recover
the original negative-ray weak equation with the literal delayed source.

The [transformed equation, domain and endpoint theorem](../3-formalized/hb-principal-laplace-equation-domain-and-trace.md)
proves `w^2*Uhat-Delta Uhat=Fhat+V Uhat` throughout the original strict
Laplace half-plane. Each spatial Schwartz pairing has controlled acceleration
from the literal wave equation. The mean value bound controls its velocity;
weighted integrability derives the infinity boundary limits. Two integrations
by parts retain the initial data and then use their proved zero values.
Bounded probes commute with the actual Bochner integrals, and the original
source transform keeps `onsetTransform(2*physicalRate,w)` exactly.

The transformed equation identifies `Delta Uhat` as an actual L² class.
`euclidean_sobolev_gain_two` gives Sobolev order two; the actual transformed
oddness gives a continuous representative with zero original endpoint trace
and negative-ray boundary limit. Its negative-ray weak frequency equation
retains the literal source and spatial L² admission. No boundary limit is
exchanged with an improper time integral.

The endpoint uniqueness proof uses the actual transformed Sobolev profile and
the original Green integrals. Compact Schwartz pairings and two local
constant-function classifications give actual classical spatial derivatives.
The Sobolev Fourier representation bounds the profile; the Green endpoint
limits and the exact lift give a bounded comparison. Its original homogeneous
equation and the componentwise Landau estimate bound its first jet near the
horizon. The actual horizon mode and its first tortoise jet decay there, so
their constant Wronskian with the comparison is zero. The second physical mode
has exact Wronskian `-connection`. The Cramer identity, zero comparison endpoint
trace and nonzero horizon-mode endpoint coefficient force the comparison to
vanish. No horizon phase or derivative bound is assumed.

The actual cutoff operators preserve the original horizon factors, negative
restriction and angular commutators. Product-measure equality and the finite
three-channel sum identify the complete Bochner source transform. This source
identity closes the causal-to-Green source comparison in the stated half-plane.

The [original joint causal forced-response theorem](../3-formalized/hb-original-joint-causal-forced-response.md)
constructs one frequency-independent spatial-vector response to the complete
source. With `c=causalGreenThreshold q+1`, it vanishes almost everywhere before
time zero and admits exponential time L² damping at `c+1`. Its Bochner Laplace
transform converges absolutely for `Re(w)>c+1` and equals the original joint
response to the literal residual at the original onset transform. The transformed
vector belongs to the actual unbounded operator domain and solves its complete
forced equation.

Absolute convergence at one real frequency bounds the source transform and
controls its frequency derivative through the strict exponential margin.
Bochner holomorphy and the original inverse estimate provide vector vertical
L² and scalar Hardy bounds. Fourier naturality and Bochner probe totality give
one causal vector, and its absolutely convergent transform identifies the
original source-resolvent product. No pointwise operator-valued representative
of the fixed-datum kernel is required.

The next physical obligation is continuation of this identified original
response to the QNM divisor and construction of its advanced/adjoint left
residue, with all source channels retained. Metric finite propagation, modular
patching and constrained Einstein identifications remain to be discharged where
needed for this continuation and spin-two/AIME evaluation. Pointwise time
regularity does not follow merely from the new weighted L² statement.
Independent Hawking-clock extinction remains open. The causal estimates supply
no Xi-zero selection; the enlarged native source chamber `Re(w)>-2` does not
continue the response inverse there. A different energy branch is not yet the
physical continuation of the constructed causal response.

No numerical experiment is indicated; the construction uses analytic estimates
and the existing Fourier, Klein–Gordon and Volterra corpus. The frontier map
remains read-only.
