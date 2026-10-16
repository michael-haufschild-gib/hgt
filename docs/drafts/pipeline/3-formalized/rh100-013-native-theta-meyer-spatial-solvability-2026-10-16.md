# Contribution 013: native theta–Meyer spatial solvability

Status: **formalized and audited**. One contribution, seven leaf modules.
The 100-contribution goal remains active; completed count is **13/100**.

## Structural result

The original affine theta equation now has a single intrinsic linear spatial
realization. Write `L=k'/k` for the original theta logarithmic derivative and
`tau(f)=lim_atTop f` for the function's actual tail trace. Then

`A f = i (f' + L (f - tau(f)))`.

On the literal span of the actual parameter jets, this expression is a linear
endomorphism. For `F_n(z)=partial_z^n q_z/n!`,

`A F_0(z)=z F_0(z)` and `A F_(n+1)(z)=z F_(n+1)(z)+F_n(z)`.

Every finite set of actual Xi support points, with every full multiplicity,
has a faithful native realization. Its dimension is exactly its number of
full-multiplicity slots. It is linearly equivalent to the corresponding
original Meyer source classes, intertwining the actual centered generator
and every finite word of scalar shifts.

For every finite real list `t_j` and every forcing in that admitted finite
packet, `product_j (A-i t_j) u=f` has exactly one solution **within the same
packet**. Its compact representative is actually absolutely continuous and
agrees with the literal function under the original theta quantile.

Main theorems:

- `meyerThetaFiniteEquiv_literal_word`
- `thetaSpatialWord_existsUnique_admitted`
- `thetaFiniteSynthesis_finrank`

The missing strong spatial derivative and the common affine source term were
real obstacles to one native Jordan action. The tail trace removes that term
using data intrinsic to the function. This supplies actual inhomogeneous
native solutions, rather than an estimate, RH equivalence, or assumed-domain
receiver. Finite AC synthesis alone is a helper, not the counted contribution.

## Current-corpus inputs

- RN: `PaperThetaParameterAnalytic`, `PaperThetaParameterVariation`, and
  `PaperThetaParameterTraces` give entire parameter dependence, the decreasing
  actual variation budget, and exact endpoint traces.
- RN: `PaperThetaCutSourceEquation` gives the literal source ODE.
  `PaperThetaConfluentCut` and `PaperThetaConfluentAdmission` pay global BV and
  compact AC admission at every order below the actual Xi multiplicity; the
  terminal cut retains its nonzero connection charge.
- HF: `DeningerMeyerXiCausalChains`, `DeningerMeyerFiniteXiCausalSplitting`, and
  `DeningerMeyerHedenmalmSourceRealization` give actual all-weight source
  classes, their full-multiplicity independence, and the centered-generator
  recurrence with its exact phase.
- `CentralReciprocalMoments.xi_divisor_support_im_ne_zero` supplies actual
  real-axis nonvanishing. The centered spectral coordinates therefore have
  nonzero real part, without RH or simplicity.

## Dependency-closed paper proof

1. The native ODE is `q_z'=-iz q_z-L(q_z+1)`. The existing variation budget
   bounds this actual derivative uniformly on one parameter circle and a
   compact spatial neighborhood. Cauchy's coefficient formula and dominated
   differentiation transfer the strong spatial derivative to every parameter
   jet. No joint differentiability premise is introduced.
2. Every finite linear combination has a finite tail limit. Uniqueness of
   limits makes the trace linear. Subtracting it homogenizes the source
   equation, closes the literal span under `A`, and gives the Hasse-normalized
   unit lowering recurrence.
3. The actual bottom trace is `-1`, so the bottom vector is nonzero. Repeated
   lowering proves independence of every chain; independence of generalized
   eigenspaces keeps distinct spectral blocks independent together.
4. Original Meyer classes `H_(n+1)` satisfy exactly the same recurrence.
   Reverse the existing causal-chain index and retain `i^(n+1)` to prove
   source synthesis injective. Shared chain coordinates give an equivalence
   and an exact intertwiner for every finite shift word.
5. A shift by `i t` retains a nonzero bottom in every actual Xi chain because
   its spectral coordinate has nonzero real part. The shifted family remains
   independent. Its finite-module action is therefore injective and hence
   bijective. Composition gives unique solutions for every finite word and
   arbitrary forcing in the packet.
6. Multiplicity-exact compact admission makes every participating closed jet
   AC. Their finite linear synthesis is the actual compact representative of
   the solution and agrees pointwise with its native quantile pullback.

## Conjecture loop and lessons

A simple source differential pencil was rejected as the contribution: the
corpus already contains `HedenmalmThetaSourceDifferentialPencil`, its rank-one
mean correction, and a substantial Green theory. That proposal was not counted.

Broad corpus searches returned weak matches; exact source-name searches and
Lean reads isolated the missing spatial mixed derivative. The Jordan-chain
deep search was partial because its local judging stage returned malformed
JSON. Available Lean hits were checked directly; no search-completeness claim
was used. No web, external novelty search, numerical experiment, or subagent
was used.

A further conjecture is exposed but unclaimed: extend this comparison using
native Hasse variation control and original Meyer Hilbert decay. The direct
inference is unpaid. This finite comparison uses causal-chain coefficients,
whereas Hilbert admission controls Mellin Hasse evaluations. Their finite
change of coordinates involves actual leading Xi jets. A bounded inverse or
infinite native admission does not follow from the finite equivalence alone.

## Verification

Final direct audits passed for all seven files using
`lake --old env lean -o <leaf.olean> <leaf.lean>` from `formal/`:

- `HTGeometry/EntireParameterSpatialDerivative.lean`
- `HTGeometry/LoweringChainIndependence.lean`
- `RHTower/PaperThetaSpatialJets.lean`
- `RHTower/PaperThetaSpatialModule.lean`
- `RHTower/PaperThetaFiniteSpatialRealization.lean`
- `RHTower/PaperThetaMeyerSpatialTransport.lean`
- `RHTower/PaperThetaSpatialSolvability.lean`

The `/tmp` axiom audit passed for all **57 public declarations**. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. Both main theorem
signatures were checked. No added axioms, proof holes, opaque/unsafe
declarations, numerical proof evaluations, or heartbeat overrides occur.

All seven modules are imported exactly once by their theorem-area umbrellas;
all seven leaf artifacts are fresh. No full or umbrella build ran.

Global `scripts/formal_tools.py lint` was run and **does not pass**: it reports
two unrelated concurrent HT modules missing umbrella imports,
`AnalyticTodaMultiplicity` and `HankelHeatToda`. Neither is part of this
contribution. They were left untouched. Existing large-file warnings also
remain. The seven owned modules have no reported lint errors.

Owned `/tmp/hgt_rh013*` API, search, and audit scratch files were removed after
the results were recorded. No commit or push was made.

## Scope

No BV-norm holomorphy, arbitrary infinite-packet admission, completion-level
spatial intertwiner, positive Hodge structure, RH, or directed nonlinear /
prime–Gamma work orientation is asserted. The larger right-tail module
contains modes at arbitrary complex parameters; the proved imaginary-shift
invertibility and uniqueness concern the admitted finite Xi packets.
Routine finite-space compatibility, further shift-word consequences, or
finite AC combinations must not be counted as another contribution.
