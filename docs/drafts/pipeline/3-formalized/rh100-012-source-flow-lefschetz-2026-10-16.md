# Contribution 012: the original Meyer flow has an arithmetic Lefschetz trace

Status: **formalized and audited; contribution 12/100**. One contribution,
not seven contributions for its seven modules. No RH, simplicity, positivity,
source-admission or trace-class premise remains in the main theorem.

## Obstacle and structural change

`DeningerArithmeticLefschetz` previously proved the complete prime/Gamma scalar
identity while explicitly leaving source-to-trace transport open: its middle
trace was defined from the divisor copies. The new construction identifies
that distribution with the ordinary operator trace of actual compact smooth
averages of the original Meyer dilation flow on its faithful full-Hasse
Hilbert completion. Every nilpotent term at every repeated zero is retained.

The new class consists of all smooth compactly supported positive-time
averages of this actual flow. They are genuine Schatten-1 operators, agree
with the literal dilation action on every original source class, and satisfy
the complete prime, Gamma and endpoint Lefschetz formula. RN's literal
theta cut-current factors determine these operators uniquely on the whole
completion. This removes an actual source-to-trace obstruction; it is neither
a strengthened estimate nor a conditional receiver or RH equivalence.

## Corpus inputs and paper proof

HF supplies whole-source normalized Hasse admission, injectivity and density
(`DeningerMeyerHasseHilbertAdmission`, `DeningerMeyerHasseHilbertDensity`), the
original dilation jet formula (`DeningerMeyerXiSpectralInclusion`), and the
actual centered generator's Hilbert--Schmidt inverse
(`DeningerMeyerHasseResolvent`, `DeningerMeyerClosedHasseGenerator`). RN supplies
totality of the literal current factors (`PaperThetaCutHasseCompletion`).
The independent Euler/archimedean route supplies the complete scalar identity
(`DeningerArithmeticLefschetz`). The trace-ideal theory supplies basis invariance
for genuine products of Hilbert--Schmidt operators.

1. Write `U(t) = diag(exp(t*rho)) exp(t*N)`, with the actual bounded Hasse shift
   `N`. The Xi strip bounds the diagonal locally in time. Its strong continuity
   follows from square-summable dominated convergence. The bounded exponential
   is continuous, and its finite coordinate expansion is exactly the original
   normalized dilation-jet formula. Dense source admission transfers the
   original group law to the whole completion.
2. Define `S(phi)x = integral phi(t) U(t)x dt` as a Bochner integral. Compact
   support and strong continuity prove integrability and bounded linearity.
   Its action on every original Meyer class is the integral of its original
   dilation action after the faithful embedding.
3. Every coordinate has derivative `rho*(U(t)x)_q + (N U(t)x)_q`, even when
   `x` is outside the unbounded generator's domain. Coordinate integration by
   parts gives `rho*(S(phi)x)_q + (N S(phi)x)_q = -(S(phi')x)_q`.
4. Put `L(phi)=phi'+phi/2`. The exact inverse equation for the actual centered
   generator gives `S(phi)=i K S(L(phi))`, hence
   **`S(phi)=(-K)(K S(L(L(phi))))`**. Both factors are Hilbert--Schmidt. Thus
   every average is Schatten-1, including its full Jordan action.
5. The nilpotent terms vanish on the canonical basis diagonal, so the genuine
   basis-independent operator trace is the full multiplicity-exact Laplace
   sum. The independent scalar explicit formula evaluates it arithmetically.
   Its equality to the existing H1 distribution proves continuity in the full
   test-function topology.
6. RN's literal cut-current factors have dense linear span in this same
   completion. Their original dilation averages therefore have a unique bounded
   extension, and the construction above supplies its unconditional trace-class
   Lefschetz realization.

## Lean deliverables

All paths below are under `formal/GaloisForLFunctions/RHTower/`:

- `DeningerMeyerHasseFlowCoefficients.lean`: full normalized Jordan expansion.
- `DeningerMeyerHilbertFlow.lean`: faithful strongly continuous original flow.
- `DeningerMeyerHilbertFlowDerivative.lean`: all-vector coordinate derivative.
- `DeningerMeyerFlowSmoothing.lean`: actual bounded Bochner averages.
- `DeningerMeyerFlowTraceClass.lean`: exact inverse factorization and Schatten-1.
- `DeningerMeyerFlowLefschetz.lean`: ordinary operator trace and full arithmetic law.
- `PaperThetaCutFactorLefschetz.lean`: unique realization from literal RN factors.

Main results: `deningerMeyerFlowSmoothing_factorization`,
`deningerMeyerFlowSmoothing_memSchattenClass_one`,
`deningerMeyerSourceFlowLefschetz`, and
`PaperThetaEndpoint.cutFactorHilbert_lefschetz_existsUnique`.

## Conjecture loop and limits

The selected source-flow trace conjecture succeeded. The finite-measure BV
current candidate was not selected: it needed a distinct signed or causal
payoff beyond contribution 011. Critical-band projection was already in the
corpus and was not counted. These are candidate-selection decisions, not
new no-go theorems.

Elaboration failures exposed two implementation requirements: explicitly fix
the real-to-complex map in compact-support transport, and use the scalar-tower
chain rule for operator-valued exponentials. Generic continuity helpers and
explicit scalar-family types removed timeouts without heartbeat overrides.

The theorem concerns the faithful Hasse **Hilbert completion**. Bochner
averaging inside the original Frechet source and a Frechet nuclear trace are
not asserted. Identifying the global Paugam pairing with the arithmetic
cup/trace, positive Hodge compatibility, self-adjointness and RH remain open.
The trace law does not give directed nonlinear RN current-work orientation.

## Audit

Seven new leaves and the documentation-updated `DeningerArithmeticLefschetz`
passed direct `lake --old env lean` audits. The mathlib API scratch passed.
All 56 public declarations audited through `/tmp` `#print axioms` use only
`propext`, `Classical.choice`, and `Quot.sound`. All seven new umbrella imports
occur once; all leaf artifacts are fresh. No full or umbrella build, numerical
experiment, added axiom, proof hole or heartbeat increase was used. Owned
scratch files were removed and their absence verified.

Global `scripts/formal_tools.py lint` reported exactly four missing umbrella
imports in separate concurrently edited files: `CHMDCardinalOrbitEnergy`,
`CHMDPolarGraphMoments`, `ThetaCardinalOrbitReadout`, and
`ThetaDivisorCardinalSource`. It reported no error for the seven contribution
leaves. Those other files were left untouched; global lint is not claimed to
pass.
