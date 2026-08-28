# FZZ-P fixed-reporter uniform cone escape

- **ID:** FZZ-P-HC7
- **Stage:** 3-formalized
- **Type:** THEOREM / uniform fixed-reporter dynamical no-go
- **Source:** HC3 sharp Hermitian detector cone + HC5 stabilized generator + HC6 exact flow
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityFixedReporterUniformConeEscape`
- **Statement:** At every positive source scale, one source-defined positive time sends every fixed
  Hermitian reporter that initially lies in the reciprocal-radius detector cone outside that cone.

## Main theorem

For the HC6 stabilized flow, write

`e=exp(Pt)`, `k=(Q/R)(e-1)`.

The pullback of every Hermitian reporter `(a,b,c,d)` has exact coefficients

`(e^2 a-2 e k b+k^2 d, e b-k d, e c, d)`.

The literal Fermi source is strictly decreasing across the two relevant scales, hence

`alpha=Q/R>1`.

Define

`E_beta=2 alpha/(alpha-1)`

and the uniform escape time

`U_beta=log(E_beta)/P`.

Then `E_beta>1`, `U_beta>0`, and `exp(P U_beta)=E_beta`.  If an arbitrary fixed reporter lies in
HC3's detector cone at time zero, its pullback at `U_beta` is not in the cone.  Consequently no
fixed Hermitian reporter remains universally reciprocal-radius separating for all nonnegative
times.

Moreover, adding any real counterterm to the pulled-back first-coordinate coefficient cannot
repair escape.  This includes arbitrary scalar first-coordinate renormalizations at the uniform
escape time.

## Paper proof

Direct expansion of the triangular flow gives the coefficient action above.  HC3 says that cone
membership depends only on

`d!=0` and `(e b-k d)^2+(e c)^2<=d^2`;

the first coefficient is irrelevant.

At time zero, cone membership implies `|b|<=|d|`.  If the same fixed reporter remains in the cone
at a later multiplier `e`, then

`|e b-d alpha(e-1)|<=|d|`.

The triangle inequality yields

`|d| alpha(e-1)<=e|b|+|e b-d alpha(e-1)|<=(e+1)|d|`.

Since `d!=0`, cancellation gives the necessary condition

`alpha(e-1)<=e+1`.

For `e=E_beta`, field algebra gives

`alpha(E_beta-1)-(E_beta+1)=alpha-1>0`,

contradicting that condition.  The selected time depends only on `P,Q,R`, never on reporter
coefficients.  Finally, HC3's cone equivalence is independent of `a`, proving the arbitrary
first-coordinate-counterterm no-go.

## New route knowledge

- exact stabilized flow acts affinely on the full four-dimensional Hermitian reporter space;
- literal Fermi monotonicity gives the decisive source slope `Q/R>1`;
- one positive source time defeats every initially valid fixed reporter simultaneously;
- escape is not an artifact of unit diagonal energy or a poorly chosen reporter;
- scalar or first-coordinate renormalization cannot repair the failure;
- surviving dynamics must use a genuinely moving reporter, reset/composition law, nonlinear
  feedback, singular interaction, or nonlocal mode-sensitive structure.

This closes the entire fixed Hermitian quadratic family under the HC5 stabilized semigroup as an
all-time FZZ-P orientation mechanism.  It does not exclude time-dependent reporters or interacting
GFZZ dynamics and does not prove RH.

## Corpus audit

Mandatory searches on 2026-08-28:

- `scripts/formal_tools.py research "FZZ stabilized diagonal flow fixed Hermitian reporter all time cone invariant classification"`
- `scripts/formal_tools.py research "triangular source flow Hermitian observable pullback universal reciprocal radius detector all time"`
- `scripts/formal_tools.py research "FZZ P Q R ratio Q over R monotonic parity delay source moment"`
- `scripts/formal_tools.py research "rank one semigroup invariant quadratic form Lorentz cone fixed reporter no go"`

Corpus returned HC3, HC5, HC6, and source-ratio infrastructure, but no arbitrary-reporter pullback
law, uniform escape time, or all-fixed-reporters no-go.

## Literature boundary

Primary and close neighbors checked:

- Hikida--Schomerus, FZZ duality and correlation matching, arXiv:0805.3931:
  https://arxiv.org/abs/0805.3931
- Mostafazadeh, Krein-space and pseudo-Hermitian formulation, arXiv:quant-ph/0606173:
  https://arxiv.org/abs/quant-ph/0606173
- Constantinescu--Gheondea, invariant Hermitian kernels and semigroup actions,
  arXiv:math/0007183:
  https://arxiv.org/abs/math/0007183
- Abraham--Bhagwat, `2x2` pseudo-Hermitian matrix quadrics, arXiv:2410.18530:
  https://arxiv.org/abs/2410.18530
- Argue--Kılınç-Karzan--Wang, rank-one generated cones, arXiv:2007.07433:
  https://arxiv.org/abs/2007.07433

Exact-object searches found no FZZ source-specific affine reporter action, uniform cone-escape
time, or simultaneous fixed-reporter obstruction.  Status is “no collision located,” not an
absolute priority claim.

## Lean closure

Main declarations:

- `fzzCigarParityDilatedSecondDiagonalStabilizedFlow_hermitian_pullback`
- `fzzCigarParityHermitianUniversalRadialReflectionSeparating_congr_first`
- `fzzKreinQAt_gt_fzzKreinRAt`
- `fzzCigarParityDilatedStabilizedFlowSlope_gt_one`
- `fzzCigarParityDilatedFixedReporterEscapeMultiplier_gt_one`
- `fzzCigarParityDilatedFixedReporterEscapeTime_pos`
- `fzzCigarParityDilatedFixedReporterEscapeTime_exp`
- `fzzCigarParityDilatedFixedReporterEscapeMultiplier_source_strict`
- `fzzCigarParityDilatedFixedReporter_uniform_escape`
- `fzzCigarParityDilatedFixedReporter_uniform_escape_firstCounterterm`
- `not_fzzCigarParityDilatedFixedHermitianReporter_allTimeSeparating`

Verification on 2026-08-28:

- direct `lake env lean` passed;
- targeted module build passed;
- axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`;
- scoped forbidden-token and `git diff --check` audits passed;
- module wired into `GaloisForLFunctions.RHTower` umbrella;
- frontier map untouched.

## Gates

- [x] 0 -> 1 in-progress: source-pure conjecture frozen after corpus search
- [x] 1 -> 2 fully-proven: coefficient action and uniform escape proof complete
- [x] 2 -> 3 formalized: unconditional Lean theorem package and audit
- [ ] 3 -> 4 publication-ready: independent specialist priority/physics audit

## Log

- 2026-08-28 — Conjectured after HC6 found a finite horizon for unit diagonal energy.
- 2026-08-28 — Uniform all-fixed-reporter escape and counterterm no-go proved and formalized.
