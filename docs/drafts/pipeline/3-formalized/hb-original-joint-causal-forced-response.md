# HB: original joint causal response to the complete cusp source

- **Stage:** formalized in Lean 4.
- **RH:** unproved; the physical QNM continuation and extinction remain open.
- **Input:** the literal continuous causal cusp source, including the native
  square remainder and all three cutoff-commutator channels.
- **Frontier map:** read-only for this work.

## Exact closed statement

Write `c = causalResponseShift q = causalGreenThreshold q + 1`. For every actual
Xi copy `q`, physical branch and amplitude, `causalJointForcedResponse` is one
frequency-independent function into the original joint spatial Hilbert space.
It vanishes almost everywhere before time zero, and `exp(-(c+1)t) U(t)` belongs
to spatial-vector-valued time L² on the whole real line.

For every independent frequency with `Re(w)>c+1`, its positive-time Bochner
Laplace integral converges absolutely and equals the original
`jointEmbedding (jointWaveResponse w ... F(w))`, where

`F(w) = cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w) ...`.

The same transformed vector belongs to `jointEnergyOperator.domain` and satisfies

`jointEnergyOperator Uhat + (w^2-1) • Uhat = Laplace(causalCuspSourceVector)(w)`.

The domain, source transform, causal support, norm convergence and Hardy bounds
are proved from the actual objects. No causal response, source-family bound,
frequency analyticity or inverse is supplied as an extra RH premise.

The capstone is `RHTower.D4BMJointSource.causalCuspSource_original_joint_response`.
The literal residual identification is
`RHTower.D4BMJointSource.causalJointForcedResponse_laplace_original`.

## Proof

Absolute convergence at `c` bounds the source transform throughout `Re(w)>=c`
by the integral of the weighted source norm. At an interior frequency, leave a
strict real margin `epsilon`. The derivative multiplier is controlled by
`t exp(-epsilon*t) <= 1/epsilon`; dominated differentiation therefore proves
Bochner holomorphy without differentiating the physical time source.

Apply the original operator-valued form inverse to this transform. Its proved
bound `||R(w)F|| <= ||F||/(Re(w)*||w||)` gives a common Cauchy bound after shifting
by `c`. Every continuous scalar probe consequently lies in half-plane Hardy
space. The same bound admits the actual vector vertical Fourier boundary to L².
Continuous probes commute with its inverse Fourier transform. Scalar
Paley–Wiener support and Bochner tensor totality give causal support for that
single vector, without a separability assumption or pointwise operator-valued
kernel. Cauchy–Schwarz proves absolute vector Laplace convergence; all continuous
probes identify its integral with the original source-resolvent product.

Undo the fixed shift. The already proved complete source-transform theorem
identifies the forcing with the literal residual. The original inverse theorem
then gives the actual unbounded-operator domain and forced equation.

## Files and audit

General leaves in `formal/GaloisForLFunctions/HTGeometry/`:

- `BochnerLaplaceHolomorphy.lean`
- `HilbertHalfPlaneBoundary.lean`
- `HilbertHalfPlaneCausal.lean`

Physical leaves in `formal/GaloisForLFunctions/RHTower/`:

- `ThetaCuspHawkingBMJointSourceForcedBoundary.lean`
- `ThetaCuspHawkingBMJointSourceForcedCausal.lean`

Five individual canonical `lake build <module>` audits passed without warnings.
All 28 new public theorems passed scratch `#print axioms`: only `propext`,
`Classical.choice`, `Quot.sound`. Audited sources total 459 lines. Ten installed
olean/ilean artifacts are byte-identical to those audits. Every new leaf is
wired directly into its area umbrella. No full or umbrella build was run.
No numerical experiment or computational proof certificate was used.

Repository-wide `formal_tools.py lint --check-generated` reports no errors in
these new leaves. Its global gate is not clean: concurrent unwired modules
`SelbergMaassTraceRegularized`, `SelbergModularArcIntegration`,
`SelbergNodalCurvature`, and `FokasLenellsLeftJost`, plus generated-index drift,
are reported outside this work. There are 141 existing large-file warnings.
Those concurrent sources were preserved.

## Remaining physical obligation

This constructs the original forced causal response in a convergence half-plane.
It does not prove a meromorphic continuation of that response to the physical
QNM divisor, its advanced/adjoint left residue, or extinction of the retained
spin-two/AIME coefficient. It does not assert pointwise time regularity or
finite propagation from the weighted L² conclusion. Those physical
identifications must precede the independent Hawking-clock extinction argument.
Changing the energy branch across the frequency boundary is not a proved
continuation of this causal response.
