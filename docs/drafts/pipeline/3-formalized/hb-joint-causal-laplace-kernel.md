# HB original spatial response as a causal Laplace transform

- **Stage:** 3-formalized; scratch, canonical leaf and new-declaration axiom audits passed.
- **Type:** THEOREM (Lean).
- **RH status:** open. Causal inversion does not supply coefficient extinction.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

## Exact result

For every fixed F in the original spatial Hilbert space, Lean constructs one
frequency-independent function `K_F : R -> SpatialSpace` such that:

1. `K_F(t)=0` for almost every `t<0`.
2. For every `c>0`, `exp(-ct)*K_F(t)` belongs to spatial-vector-valued L² on
   positive time.
3. For every `Re(w)>0`, its Bochner Laplace integral is absolutely convergent and

   `integral_(0,infinity) exp(-wt)*K_F(t) dt`
   `= jointEmbedding (jointWaveResponse w hw F)`.

The right side is exactly the previously constructed original joint response.
No causal-support premise, new inverse, or separately assigned probe output is
supplied. The construction gives one vector kernel; all continuous spatial
probes observe that same kernel. Auxiliary positive Fourier-line damping
choices give equal kernels almost everywhere on the whole time axis.

This identifies the **spatial value** of the original completed energy response
with a time-causal Laplace transform. It does not assert that each time slice
of K_F belongs to the completed energy domain, has a classical coordinate
representative, or satisfies finite propagation in the original metric.

## Dependency-closed proof

Write V for the actual completed energy space, H for the spatial Hilbert space,
and `J:V->H` for its proved contractive embedding. The original form pencil is

`A(w)=I+(w²-1)J*J`.

The existing rotated coercivity theorem constructs a two-sided bounded inverse
of `conj(w) A(w)` for every `Re(w)>0`. Cancelling the nonzero scalar factor
proves A(w) is a unit in the Banach algebra of bounded operators on V. Banach
algebra inversion is holomorphic at units, so the actual formula

`R(w)=J A(w)^(-1) J*`

is holomorphic on the right half-plane. Its V-valued preimage solves the
original form equation; uniqueness identifies it with the original selected
response. The existing mass estimate therefore gives

`norm(R(w)F) <= norm(F)/(Re(w)*norm(w))`.

Fix `delta>0` and a continuous complex linear probe ell on H. The function
`p_delta(w)=ell(R(w+delta)F)` is holomorphic, and

`norm((w+delta)*p_delta(w)) <= norm(ell)*norm(F)/delta`.

The corpus's Cauchy kernel `(w+delta)^(-1)` is a half-plane Hardy function with
mass bound `1/(2*delta)`. Bounded holomorphic multiplication therefore puts
p_delta in Hardy space with mass bound
`(norm(ell)*norm(F)/delta)^2/(2*delta)`. The proved Paley–Wiener theorem
constructs its scalar inverse-Fourier datum, proves negative-time vanishing,
and identifies its Laplace transform.

The same resolvent estimate proves actual vector L² membership on every line
`delta+sigma+2*pi*i*xi`. Let Q_delta,sigma be the Hilbert-valued inverse Fourier
transform of this vector boundary function. Continuous linear probes commute
with the actual L² Fourier transform: prove this first on Schwartz functions
by commuting the probe with the convergent Fourier integral, then pass through
Schwartz density and continuous extension. Consequently each probe of Q is
the already identified scalar Hardy preimage.

Scalar probe support implies actual vector support. This is proved without a
separability premise: pure Bochner tensors have inner product equal to the
corresponding scalar probe pairing; their dense span separates vector L².
Apply this totality to the restriction of Q to negative time. No common
pointwise exceptional set is assumed across all probes.

Define

`K_delta(t)=exp(2*delta*t)*Q_delta,delta(t)`.

It vanishes at negative times. Its probes equal `exp(delta*t)` times the
scalar Hardy data. The damped kernel `exp(-2*delta*t) K_delta` is actual
vector L², so Cauchy–Schwarz proves absolute Bochner Laplace integrability for
`Re(w)>2*delta`. Commuting each probe with this integral and applying scalar
Paley–Wiener identifies the vector integral with R(w)F.

For two choices delta and epsilon, choose a common damping
`c=2*delta+2*epsilon`. Both damped kernels are vector L² on positive time.
Every probe of their difference has zero Laplace transform, since both
transforms equal the same probe of R(w+c)F. The corpus's L² Laplace
injectivity theorem kills each scalar difference; Bochner probe totality
kills the vector difference. The exponential damping never vanishes, so the
undamped kernels agree on positive time. Their causal support and the null
singleton at zero extend this equality to the whole time axis.

Fix `K_F=K_1`. For an arbitrary `Re(w)>0`, compare it with
`K_epsilon`, where `epsilon=Re(w)/4`. The latter has an absolutely convergent
transform at w, equal to R(w)F; almost-everywhere equality transfers both facts
to the fixed K_F. Comparing with `epsilon=c/4` similarly proves L² membership
under every positive damping c. The final theorem has no extra half-plane
restriction.

## Lean surface

Route namespace: `RHTower.D4BMJointWave`. Canonical prefix:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJoint`.

| Module suffix | Public theorems | Content |
|---|---:|---|
| AnalyticInverse | 8 | Original pencil inversion, holomorphy and response identity |
| HardyResponse | 6 | Derived scalar Hardy membership and causal Laplace data |
| VectorBoundary | 4 | Actual vector boundary L² and probe identities |
| CausalKernel | 6 | One vector time kernel and actual causal support |
| CausalLaplace | 7 | Absolute Bochner integral and initial transform identity |
| KernelDamping | 2 | Common damping and shifted transforms |
| KernelCoherence | 3 | Damping independence and every positive damping |
| CausalRightHalfPlane | 5 | Full right-half-plane original-response identification |

Generic namespace: `GaloisForLFunctions.HTGeometry`.

| Module suffix | Public theorems | Content |
|---|---:|---|
| HilbertL2FourierNaturality | 4 | Continuous probes commute with L² Fourier inversion |
| BochnerL2ProbeTotality | 3 | Scalar probes detect vector L² and measurable support |

Total: ten leaves, forty-eight public theorems. Main endpoints are
`jointCausalKernel_support`, `jointCausalKernel_memLp_pos`,
`jointCausalKernel_integrable`, and
`jointCausalKernel_originalResponse_rightHalfPlane`.

## Audit

All ten canonical leaves passed individual `lake build <module>` audits in an
isolated package using existing dependency caches: two jobs per leaf, no
warnings. The 723 source lines and twenty installed `.olean`/`.ilean` artifacts
match their audited copies. Each leaf is imported exactly once by its area
umbrella; neither umbrella was built.

A scratch `lake env lean` audit printed axioms for all forty-eight new public
theorems. Every result contains only `propext`, `Classical.choice`, and
`Quot.sound`; no added axiom or computational certificate occurs. Missing older
dependency caches were restored only as needed for this import check, without
a broad rebuild. Existing theorem axioms were not re-audited.

The source index was refreshed. `scripts/formal_tools.py lint --check-generated`
passed with 141 large-file warnings and no other findings. Scoped whitespace,
source/artifact equality and umbrella-wiring checks passed. No numerical
experiment was run.

## Remaining hard obligations

F is fixed while transform frequency varies. Applying this impulse kernel to
the actual smooth-onset source still requires its vector time dependence,
convolution and transform interchange, all onset terms, and the explicit cusp
principal correction. The theorem does not silently identify a
frequency-dependent spatial residual with a fixed forcing.

Transfer to classical coordinate equations, finite propagation, modular
patches, radial endpoint traces, and the constrained Einstein correction
sectors remains distinct. In particular, the proof does not continue the
response to the physical left-QNM boundary value or evaluate the augmented
retained spin-two/AIME pairing. Independent Hawking-clock extinction remains
unproved. A causal linear response exists for every spatial F here, so its
existence alone imposes no restriction on Xi zeros.

The new result uses the existing operator estimate and proved Fourier/Hardy
corpus. No external novelty claim, numerical experiment, or computational
certificate is involved. No new route-independent RH law follows; universal-law
STATUS and the frontier map were not edited by this work.
