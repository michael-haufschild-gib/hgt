# SQB entire Casimir transform

Status: formalized; targeted module and axiom audits passed. Repository-wide lint
currently reports one unrelated concurrent wiring error. RH remains open.

Intended chain: original Maass source → modular curvature and exact total mass →
quarter domination → Selberg gap → independently constructed Xi occurrence → RH.
This card develops a nonpolynomial transform compatible with the proposed
occurrence interface. It does not construct that occurrence or prove the gap.
The frontier map is read-only for this task.

## Source and search

Broad whole-corpus OR searches covered source lifts, automorphic periods,
operator domains, entire descent, and operator mapping, followed by a broad
square-factor/cosh/Casimir/monodromy search. Search coverage concerns declaration
metadata; selected proof bodies were then inspected. No numerical experiment
or computation supplies a proof premise.

The constructive source is `HTGeometry.EvenEntireSquareFactor`: an even entire
function descends through squaring with an entire power series. The previous
`SelbergScatteringPolynomialReality` classification excludes every nonconstant
polynomial real on the critical scattering parabola. Entire periodic functions
can escape its polynomial-period rigidity step.

## Exact paper construction

Write k(z) = 3/16 + z²/4 + iz/4 = 1/4 + (z+i/2)²/4.
Let F(λ) be the even-entire square descent of w ↦ cosh(8πw), evaluated at
λ−1/4. Thus F(1/4+w²) = cosh(8πw), without selecting a global square-root branch.
It is entire. Substitution w=(z+i/2)/2 and the 2πi period of cosh give
F(k(z)) = cosh(4πz). In particular all critical real parameters map to real
values at least one; nonzero parameters map strictly above one. F is not a
polynomial, by the previous polynomial classification and these differing values.

For real λ≥1/4, use w=√(λ−1/4) to obtain F(λ)=cosh(8π√(λ−1/4))≥1.
For real λ≤1/4, use w=i√(1/4−λ) to obtain
F(λ)=cos(8π√(1/4−λ))∈[−1,1]. Consequently F(λ) is real for every real λ,
and F(λ)>1 iff λ>1/4. Non-strict threshold inversion is false:
F(3/16)=F(1/4)=1. These are exact symbolic identities.

For z=t+iδ with t≠0 and |δ|<1/2,
Im cosh(4πz)=sinh(4πt) sin(4πδ). If this vanishes, the nonzero sinh factor
forces sin(4πδ)=0. Its cosine is ±1. A transformed real part ≥−1 excludes
cosine −1 since cosh(4πt)>1. Cosine +1 and |4πδ|<2π imply δ=0.
Conversely δ=0 gives a real value >1. Hence membership in the real half-line
[−1,∞) detects the critical line throughout this open strip away from t=0;
so does membership in [1,∞). This is an exact pointwise classifier, not an
admitted spectral correspondence.

The expression resembles a doubled trace of constant-term exponents. No source
monodromy or operator functional calculus is claimed until explicitly constructed
with its domains and occurrence map. In particular the above elementary entire
function does not transport scattering poles into self-adjoint spectrum.

## Stronger real-preimage classification

For every real native parameter λ, every z in the open centered strip with
Re z≠0 satisfies

F(λ)=F(k(z)) iff Im z=0 and λ=1/4+(Re z)²/4.

Necessity first uses the real-native lower bound −1 and the strip classifier.
The resulting critical value is strictly above one, so the strict threshold
forces λ>1/4. Equality of the two real hyperbolic cosines implies equality of
their arguments' absolute values. Squaring and canceling the nonzero π² factor
gives λ=1/4+(Re z)²/4. Conversely substitution of that real parameter gives
the same hyperbolic cosine directly by square descent. Thus existence and
uniqueness are both proved; the alias at t=0 is excluded precisely by Re z≠0.

In the original exponent coordinate, F(s(1−s))=cos(8π(s−1/2)). For every actual
multiplicity-marked Xi zero rho, the existing corpus proves 0<Re rho<1 and
Im rho≠0, so the classifier applies without RH. Its real-preimage condition at
s=rho/2 is exactly Re rho=1/2, with unique λ=1/4+(Im rho)²/4. No premise states
that this preimage exists. Constructing it for all zeros would supply the still
missing critical-placement result; the entire transform alone does not do so.

## Work checklist

- [x] Broad corpus search; check algebra, sign, strict threshold, alias.
- [x] Verify API names and proofs with `lake env lean` scratch files.
- [x] Formalize exact entire descent, native range, strip classifier, and unique real preimage.
- [x] Wire finished modules into RHTower; audit only individual modules.
- [x] Audit all exports' axioms; run formal lint and document its unrelated wiring failure and the exact remaining mathematical gap.

## Lean artifacts and audit

Both modules use namespace `RHTower.SelbergScatteringEntireTransform`:

- `formal/GaloisForLFunctions/RHTower/SelbergScatteringEntireTransform.lean`:
  16 public declarations, entire construction, native formulas, exact alias,
  nonpolynomiality, and both strip classifiers.
- `formal/GaloisForLFunctions/RHTower/SelbergScatteringEntirePreimage.lean`:
  8 public declarations, constructive native partner, strict quarter bound for
  nonzero ordinates, complete preimage classification, original exponent formula,
  and actual-Xi necessity and sufficiency.

Each scratch and source check used `lake env lean`. Final audits used only
`lake build GaloisForLFunctions.RHTower.SelbergScatteringEntireTransform` and
`lake build GaloisForLFunctions.RHTower.SelbergScatteringEntirePreimage`.
Read-only `--no-build` preflights confirmed that each target alone was stale;
only one Lean compiler process ran per final build. No umbrella or full build
ran. Both targets are imported exactly once by RHTower. The endpoint import
was reduced to the already-proved Xi strip source rather than the larger
scattering incidence module.

All 24 public exports were checked with `#print axioms` in a `/tmp` scratch:
only `propext`, `Classical.choice`, and `Quot.sound`. No new axiom, proof hole,
RH assumption, external numerical certificate, or computational proof input was
introduced. Exact arithmetic tactics only normalize symbolic proof terms.
The research index contains every public export. New modules emit no warnings;
the endpoint build replays existing dependency tactic suggestions.

Repository lint currently fails only because concurrent module
`HTGeometry.FokasLenellsCompatibilityMoment` is unreachable from its own umbrella.
That unrelated in-progress source was not modified by this task. Existing large
file warnings are also reported. The SQB modules have no lint errors.

## Reproducible broad search coverage

All searches used `research`, `--any`, unrestricted module scope, `--per-module 0`,
and a sufficient return limit. Counts refer to returned declaration metadata,
not inspection of every proof. Follow-up proof inspection selected the actual
square-descent, polynomial-period, native-coordinate, and Xi-strip sources.

| OR query | Declarations | Modules |
| --- | ---: | ---: |
| "symmetric square" "tensor product" "Eisenstein" "spherical transform" "automorphic lift" "intertwiner" "spectral multiplier" | 2895 | 408 |
| "relative trace" "Rankin Selberg" "period integral" "Hecke correspondence" "cuspidal projection" "spectral projection" "residue" "Poincare series" | 7502 | 1629 |
| "nonlinear eigenfunction" "product Laplacian" "gradient variance" "square root" "spectral admission" "boundary condition" "domain intertwining" | 1937 | 939 |
| "cosh" "cosine" "even entire" "square descent" "square root descent" "entire descent" "Chebyshev" "monodromy" | 5809 | 1391 |
| "spectral mapping" "functional calculus" "exponential operator" "cosine family" "monodromy trace" "wave trace" "semigroup" | 508 | 139 |
| "square factor" "cosh" "Casimir" "monodromy" | 2891 | 621 |

## Remaining proof obligations

The SQB quarter domination inequality remains unproved here. This work supplies
an entire transform compatible with critical scattering values and classifies its
real preimages exactly. It supplies neither an automorphic source transporting
those values nor an eigenfunction/domain admission theorem. Even existence of
an arbitrary matching real parameter for every actual Xi zero is precisely the
critical-placement assertion. Any next producer must derive that existence from
independent source identities; it cannot take the preimage condition as a premise
and report it as an unconditional RH proof. The frontier map was not edited.
