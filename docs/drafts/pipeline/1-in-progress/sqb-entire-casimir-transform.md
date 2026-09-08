# SQB entire Casimir transform

Status: paper derivation; Lean construction and audit in progress. RH remains open.

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

## Work checklist

- [x] Broad corpus search; check algebra, sign, strict threshold, alias.
- [ ] Verify API names and proofs with `lake env lean` scratch files.
- [ ] Formalize exact entire descent, native range, and strip classifier.
- [ ] Wire finished modules into RHTower; audit only individual modules.
- [ ] Audit all exports' axioms and formal lint; document exact remaining gap.
