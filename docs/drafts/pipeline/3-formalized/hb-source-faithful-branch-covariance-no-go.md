# HB source-faithful branch covariance no-go

Status: formalized
Route: HB
Started: 2026-08-28
Completed: 2026-08-28

## Conjecture HC15

For nonzero seed amplitude, equality of canonical global left-coordinate sources
`plusSource(reflect q) = minusSource(q)` holds exactly on the critical line. Consequently every
quadratic branch lift that realizes those literal residuals and obeys
`p(reflect q) = m(q)` forces `Re(q) = 1/2`, independently of branch square-root choice, quadratic
map, Peierls pairing, propagator, cyclicity, or skewness.

## Significance target

Upgrade HC14 branch-choice classification to a representation-independent physical no-go. If
proved, no two-branch source-faithful Einstein--Teukolsky action can derive the missing covariance
off critical. The only survivor is a larger FE--Schwarz real-closure packet with modified
orbit-level, rather than individual-fibre, incidence.

## Result

HC15 is true, and its scope is stronger than the original branch-square-root obstruction. For
every nonzero seed amplitude,

`plusSource(reflect q) = minusSource(q) ↔ Re(q) = 1/2`.

Therefore an arbitrary complex field space, arbitrary bilinear quadratic residual, and arbitrary
two branch families cannot simultaneously realize the literal canonical sources and obey the
reflection branch swap at a tilted Xi zero. No symmetry, cyclicity, Peierls form, propagator,
radial basis, or square-root representation enters the proof.

Global source fidelity plus branch covariance implies `RiemannHypothesis`. Combined with the
existing real-closure theorem, every tilted source-faithful continuation must leave the two-branch
model and use at least four FE--Schwarz sectors.

## Main Lean theorems

- `hbXiPeierlsPlusSource_reflect_eq_minusSource_iff`
- `hbXiPeierls_sourceFaithful_branchCovariance_forces_criticalLine`
- `hbXiPeierls_tilted_no_sourceFaithful_branchCovariance`
- `hbXiPeierls_sourceFaithful_global_branchCovariance_forces_rh`
- `hbXiPeierls_tilted_sourceFaithful_noGo_and_realClosure_ge_four`

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSourceFaithfulBranchCovarianceNoGo.lean`

## New knowledge

The obstruction is source-semantic, not representational. Any quadratic Einstein--Teukolsky
realization of the two literal Peierls source packets inherits the same critical-wall rigidity,
even after replacing every part of the previously constructed carrier and action. Off wall,
source-faithful reflection covariance cannot be repaired inside two branches; FE--Schwarz real
closure forces a four-sector packet. This identifies orbit-level landing on that quartet as the
minimal surviving HB proof architecture.

## Literature audit through 2026-08-28

Primary literature contains second-order Schwarzschild perturbation formalisms, covariant
gauge-invariant source constructions, and Kerr QNM currents with discrete reflection symmetries,
but the audit found no representation-independent theorem equating source-faithful branch
covariance with a critical spectral wall, and no Xi-divisor four-sector necessity theorem:

- Gleiser et al., *Second order perturbations of a Schwarzschild black hole*,
  https://arxiv.org/abs/gr-qc/9510049
- Spiers--Pound--Wardell, *Second-order perturbations of the Schwarzschild spacetime: practical,
  covariant and gauge-invariant formalisms*, https://arxiv.org/abs/2306.17847
- Campanelli--Lousto, *Second order gauge invariant gravitational perturbations of a Kerr black
  hole*, https://arxiv.org/abs/gr-qc/9807077
- Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*,
  https://arxiv.org/abs/2210.15935

Novelty claim is the source-semantic critical-wall classification and its formal combination with
four-sector FE--Schwarz real-closure minimality, not existence of nonlinear perturbation sources or
reflection symmetries separately.

## Verification

- Direct: `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSourceFaithfulBranchCovarianceNoGo.lean`
- Target audit: `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFaithfulBranchCovarianceNoGo`
- Build result: success, 11892 jobs after shared dependency replay
- `#print axioms` on four endpoints: `[propext, Classical.choice, Quot.sound]` only
- Forbidden-token scan: clean
- Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run
- Global lint reports only unrelated pre-existing/unowned umbrella reachability failures; this
  module is reachable and has no lint finding

## Remaining HB burden

Construct the minimal four-sector FE--Schwarz real-closure Peierls packet and determine its exact
orbit-level cubic landing. Individual-fibre source incidence is now proved impossible off wall;
only an orbit-valued action can remain source-faithful without assuming RH.
