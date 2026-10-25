# Faithful positive Meyer degrees require simple critical zeros

- **ID:** faithful-positive-meyer-degrees-require-simple-critical-zeros
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Q-II source effectivity and linear degree
- **Statement:** The genuine Poisson ideal is closed under taking sharp-square roots if and only if RH holds and every Xi zero is simple. These conditions are also equivalent to the existence of a linear cohomological degree strictly positive on every nonprincipal sharp square.
- **Status:** `[PROVED HERE, paper]`; Lean proof pending; external novelty unverified.

## Actual carrier and statement

Let `A` be `DeningerMeyerStrongLogTarget`, with its proved source convolution and
arithmetic involution `g# = J(conj(g))`. Let `I` be the actual range of the Poisson
source map. The corpus proves that `I` is a convolution ideal and that

`g in I iff every Mellin jet of g below the Xi multiplicity vanishes`.

The following assertions are equivalent:

1. For every actual source `g`, `g*g# in I` implies `g in I`.
2. RH holds and every Xi divisor point has multiplicity one.
3. There exists a complex-linear map `d : A/I -> C` such that
   `Re d([g*g#]) > 0` for every `g not in I`.

The degree in assertion 3 is not required to be the ordinary trace. Thus changing
the linear degree cannot remove either necessary condition while retaining
faithfulness on the full genuine quotient. No continuity assumption on `d` is needed.

Nonfaithful positive degrees already exist unconditionally. Hardy supplies a critical
divisor point `rho`. The genuine quotient functional `d([g])=M(g,rho)` sends every
sharp square to `|M(g,rho)|²`. Its value on the point source at `rho` is one. The
conjugate point `conj(rho)` is distinct: a real critical divisor point would be `1/2`,
which is not in the Xi divisor. The point source at `conj(rho)` is nonprincipal and
its sharp-square degree is zero. Thus this positive degree is nonzero and explicitly
nonfaithful. Its actual Lean module is `PositiveMeyerDegreesCanForgetClasses.lean`,
still awaiting its direct check.

## Dependency-closed paper proof

Write `r(rho)=1-conj(rho)` and `m(rho)` for the actual Xi multiplicity. The functional
equation and conjugation preserve multiplicity, so `m(r(rho))=m(rho)` and `r` is an
involution. The proved source reflection formulas give, for every raw Mellin jet,

`jet_k(g#, rho) = (-1)^k conjugate(jet_k(g, r(rho)))`.

Finite causal source sections give an actual source `e_(rho,j)` with exactly one
nonzero divisor jet, namely `jet_j(e_(rho,j),rho)=1`, for every `0<=j<m(rho)`.
Consequently this source is nonprincipal. The convolution Hasse-jet formula is a
finite sum over orders adding to the requested order.

If `rho` is off the critical line, then `rho != r(rho)`. The source `e_(rho,0)` and
its sharp have disjoint divisor jet supports. Every jet of their convolution below
the local multiplicity is zero. Their sharp square belongs to `I`, although the
source does not. Assertion 1 therefore puts every Xi divisor point on the critical
line, which is RH by the corpus's divisor-support criterion.

If `m(rho)>1`, use `e_(rho,m(rho)-1)`. At any point distinct from `rho`, the first
factor has every relevant jet zero. At `rho`, the sharp factor has every relevant
jet zero unless `r(rho)=rho`; in the latter case both nonzero jet orders are
`m(rho)-1`. Their sum is at least `m(rho)`. Once again every jet below multiplicity
of the sharp square vanishes. Assertion 1 therefore also forces simplicity.

Conversely, under RH and simplicity, a principal sharp square has value
`M(g,rho) conjugate(M(g,rho))=0` at every divisor point. Each value of `g` is zero,
and these are all the required jets when the divisor is simple. Hence `g in I`.
This proves 1 iff 2 without assuming any positive degree.

Assertion 3 implies 1: a principal sharp square has quotient class zero and linear
degree zero, contradicting strict positivity if its source is nonprincipal.

Under assertion 2, the existing ordinary cohomological trace degree supplies 3.
The source trace is the absolutely summable multiplicity-weighted sum of squared
Mellin values. It is nonnegative; a nonprincipal source has a nonzero required jet,
which by simplicity is a nonzero value, and its positive summand gives strict
positivity. Equivalently, source-trace Cauchy–Schwarz and the exact numerical radical
identify its zero set with the genuine principal ideal. This proves 2 implies 3.

## Positive survivor and research implication

Ordinary trace positivity alone is equivalent to RH and does not force simplicity.
Its numerical radical removes all higher jets. On the full genuine quotient, a
faithful positive degree must additionally exclude the explicit nilpotent jet
classes. The exact obstruction is sharp-square-root closure of the actual Poisson
ideal, rather than linearity of degree or existence of principal representatives.

The stronger local classification exposed by the proof is: a single jet source
`e_(rho,j)` has principal sharp square exactly when `r(rho)!=rho` or `2*j>=m(rho)`.
The reverse direction reads the nonzero product jet of order `2*j`, whose factorial
coefficient and reflection sign are nonzero. This classification remains a separate
Lean target; it is not implied merely by the terminal equivalence.

## Formalization dependencies

- `DeningerMeyerFiniteXiCausalSplitting`: actual finite jet sections and off-block vanishing.
- `DeningerMeyerGeneralizedZeroJetDescent`: reflected raw jets.
- `DeningerMeyerCausalConjugation`: conjugated raw jets.
- `DeningerMeyerConvolutionWeilTrace`: genuine source sharp and trace.
- `MeyerNumericalRadicalAndMultiplicity`: exact boundary and numerical kernels; actual-file check and standard axiom audits passed.
- `MeyerSourceIntersectionSurface`: positive faithful ordinary trace criterion; actual-file certified with standard axiom audits.

`FaithfulPositiveMeyerDegrees.lean` contains the complete proof attempts for the
local classification and the terminal equivalences. Its jet and divisor APIs have
passed scratch checks; its actual-file check remains pending the surface dependency.

All mathematical inputs have proofs; there is no assumed positivity producer or
hidden simplicity premise. The main result is an unconditional equivalence, not a
proof of RH or simplicity.
