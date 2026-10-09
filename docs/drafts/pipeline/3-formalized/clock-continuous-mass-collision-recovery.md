# Continuous scale recovery through scalar mass collisions

- **ID:** clock-continuous-mass-collision-recovery
- **Stage:** 3-formalized
- **Type:** PROVED / CORPUS BRIDGE
- **Source:** `ClockContinuousPotentialDetermination`, `ConformalClockMatrixRecovery`.
- **Statement:** Continuous real scale fields observed through projective mixed-potential
  matrices are determined exactly on the closure of the nonscalar mass locus.

## Exact statement and paper proof [PROVED HERE]

Let X be a normal T1 space, M(x) any complex N-by-N matrix field, N>=1, and
s:X→R continuous. Define O_M(s)(x)=projectiveDelayPanel(s(x)M(x)). Any independently
varying common scalar defect is invisible by the existing projective panel theorem.
Let E={x : M(x) is not a scalar matrix}.

The algebraic classification gives O_M(t)=O_M(s) iff t=s on E. For continuous
t,s, this is equivalent to equality on closure E. Thus at a point x the compatible
values are {s(x)} if x lies in closure E and all of R otherwise. For the latter
case, separate x from closure E by a continuous real f equal to one at x and zero
on closure E, and use t=s+(v-s(x))f. This preserves the entire projective observation
and realizes the arbitrary value v. Consequently global continuous scale recovery
is equivalent to density of E.

The same exact criterion holds for the positive conformal scale exp(2 sigma), with
sigma continuous: equality of exponentials is equality of sigma at every nonscalar
point. Perturbing sigma by the separator preserves strict positivity of the physical
scale. Thus the classification is not an artifact of allowing negative scales.

No continuity of M is required for this observation theorem; smooth physical mass
fields are a special case. No PDE probe existence, regularity of an eigensystem,
nonzero gap at the target point, or spectral diagonalization is assumed.
This is an exact uniqueness theorem, not a stable reconstruction estimate. A small
or vanishing local gap can still prevent pointwise division or amplify error.

## Corpus audit

`research "continuous mass matrix scalar collision scale determination" --no-refresh --json`
completed with older-generation coverage and unmeasured semantic coverage. Candidates
include the newly constructed continuous potential and projective matrix interfaces;
unrelated collision-mass objects do not establish this theorem. Exact text searches
found no prior nonscalar-density clock result. No external search or reading.

## Plan

- [x] State exact observation, domain and full-value classification; complete paper proof.
- [x] Search corpus and inspect parent theorem applicability.
- [x] Formalize exact compatibility, value-fiber, pointwise and global classifications.
- [x] Direct module/axiom audit, umbrella/index integration, authoritative lint.

## Lean audit (2026-10-08)

`formal/GaloisForLFunctions/HTGeometry/ConformalClockContinuousMatrixRecovery.lean`
contains seven theorems and two definitions. Direct `lake --old env lean` with
leaf object emission passed. Imported `#print axioms` checks for every theorem
and both definitions use only `propext`, `Classical.choice`, and `Quot.sound`.
The umbrella imports this leaf exactly once. Index regeneration passed; all seven
theorems and `clockNonscalarMassSet` have generated API rows. The standalone
`noncomputable def mixedClockScaleObservation` lacks a generated API row, matching
the existing omission of standalone `noncomputable def tentFn`; its source,
compiled declaration, and axiom audit are present. No generator code was changed.

Global lint failed on eight unrelated unreachable modules, recorded on the companion
`clock-matrix-scale-projective-recovery.md` card. No owned leaf had proof-debt or
reachability errors. No full or umbrella build was run.

## Next conjecture

The sharp quantitative loss at a vanishing gap is tracked separately in
`clock-collision-sharp-stability.md` and is now formalized for every positive integer
order under a classified Lipschitz error budget. Exact continuous uniqueness alone
does not supply that regularity budget.

## Significance boundary

This combines two corpus mechanisms and reduces the mass-gap burden from pointwise
nondegeneracy to dense nonscalarity for continuous uniqueness. It does not establish
external novelty, a source-specific RH bound, or numerical stability.
