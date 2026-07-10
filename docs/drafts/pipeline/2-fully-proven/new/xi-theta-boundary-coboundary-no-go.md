# The theta moving boundary is an exact flat coboundary

- **ID:** xi-theta-boundary-coboundary-no-go
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ROUTE-CLOSING OBSTRUCTION, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parents:** `xi-theta-critical-log-translation-seam.md`,
  `xi-theta-unit-radius-perron-source.md`, `phase-cancellation-crux.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiThetaBoundaryCoboundary.lean`

## The field-level question

Positive truncation does not commute with logarithmic translation.  The resulting finite window was
treated as a possible theta seam charge.  Before building a carrier or propagating that charge in a
contour depth, ask the invariant question:

> Is the moving boundary a nontrivial weld class, or is it an exact defect of the translation flow?

It is exact.  Therefore it cannot be the nontrivial constraint class whose polarization would bear
on RH.

## Setup

For an additive-valued function `f` on `R`, let

`(T_a f)(u)=f(u+a)`

and let `P_+` be strict positive truncation:

`(P_+ f)(u)=1_(0,infinity)(u)f(u)`.

For `a>0`, the swept-window boundary is

`(B_a f)(u)=1_(-a,0](u)f(u+a)`.

Define the normalized conjugation defect

`D_a = T_a P_+ T_(-a) - P_+`.                                    (1)

## Theorem A `[PROVED]`: the boundary is a projection commutator

For every `a>0`,

`B_a = T_a P_+ - P_+ T_a`.                                       (2)

Equivalently,

`B_a f = D_a(T_a f)`.                                             (3)

### Proof

The positive-truncation seam identity already gives pointwise

`P_+(T_a f)+B_a f=T_a(P_+f)`.

Rearranging proves (2).  Substituting `T_a f` into (1) and cancelling
`T_(-a)T_a=1` proves (3).

Thus the finite boundary window is not additional structure.  It is exactly the failure of one
fixed projection to be equivariant under translation.

## Theorem B `[PROVED]`: exact cocycle law

For `a,b>0`, the unnormalized windows obey

`B_(a+b) f = B_a(T_b f)+T_a(B_b f)`.                              (4)

For arbitrary real `a,b`, the normalized defect obeys

`D_(a+b)=T_a D_b T_(-a)+D_a`.                                    (5)

### Proof

Equation (4) splits the interval `(-a-b,0]` into the disjoint translated pieces
`(-a-b,-a]` and `(-a,0]`.  Algebraically it follows by applying (2) three times and cancelling the
middle `T_aP_+T_b` terms.

For (5), expand (1):

`T_a(T_bP_+T_(-b)-P_+)T_(-a) + (T_aP_+T_(-a)-P_+)
 = T_(a+b)P_+T_(-(a+b))-P_+`.

This is exactly `D_(a+b)`.

## Theorem C `[PROVED]`: zero curvature and theta specialization

The translation curvature

`K(a,b)=T_aD_bT_(-a)+D_a-D_(a+b)`

vanishes identically.  At every theta-square index `m>1`, with `a_m=2log m`, the moving boundary
appearing in the square-atom translation seam is

`B_(a_m)(thetaLogMother)=D_(a_m)(T_(a_m)thetaLogMother)`.           (6)

### Proof

The first statement is (5) rewritten.  Since `m>1`, `a_m>0`; applying (3) to the fixed theta mother
profile gives (6).

## Consequence: the carrier route is flow in disguise

The result is stronger than a warning about terminology.

- `D_a` has the explicit primitive `P_+`: it is a conjugation coboundary.
- Its cocycle law is forced by the translation group.
- Its curvature is zero.
- Every index-dependent theta window is only an evaluation of this same exact defect.

Therefore any obstruction theory that quotients by translation gauge sends this boundary class to
zero.  In particular it cannot supply the nonzero cohomology class required by a nontrivial
polarized obstruction realization.  Building a vertical carrier, a heat reader, or an `M`-indexed
defect family around `B_a` does not change its class; it only propagates an exact flow defect.

This is the precise mathematical reason the route is retired.

## What survives

- `[PROVED]` The positive theta half is still a canonical lower-supported `L2` function of unit
  Perron radius.  That is valid analytic infrastructure.
- `[BRIDGE]` Its canonical Perron seam recovers right-edge coefficients under carrier hypotheses.
  The recovery is a transported coefficient identity, not an RH-bearing invariant.
- `[FALSIFIED AS AN RH ROUTE]` The moving-boundary/reader/carrier construction produces the missing
  nontrivial seam class.

## New open core: a fixed non-exact constraint

The next object must be defined directly from the fixed completed datum and survive the quotient by
all affine translation/scaling coboundaries:

`weld-affine-coefficient-collapse.md` proves the sharper coefficient audit.  The scalar weld becomes
exact in the natural affine `<D,I>` coefficients, and the killing primitive is genuinely
FE-covariant once reflection is allowed to act on the weld labels.  FE symmetry does not rescue the
class.  Every primitive nevertheless has principal symbol one at the derivation generator, so the
weld survives modulo order-zero gauge as the connecting boundary of the fixed differential-order
filtration.

> `[OPEN CORE]` Prove that bounded polarization-preserving gauges in the fixed completed
> representation are order zero, then map the prime filtration boundary canonically to the Krein
> polarization.  Do not introduce a contour-depth family, evolving carrier, or translation defect.

The separating test is now exact: if a proposed seam has an explicit projection primitive, satisfies
a flat translation law, or is removed by affine conjugation, it is on the flow side and is rejected
before any positivity or coefficient calculation.

## Novelty and significance gates

- **NOVEL:** The commutator formula alone is elementary.  The new result is the complete
  normalization and route verdict: the square-indexed theta boundary family is one exact
  conjugation coboundary with zero curvature, so it vanishes in the very obstruction quotient the
  RH polarization needs.
- **SIGNIFICANT:** This closes the active carrier/reader branch for a structural reason and prevents
  further work from mistaking transported boundary data for the fixed constraint.  It replaces the
  false open core with a sharp non-exactness requirement on the actual completed weld.

## Gates

- [x] 0 -> 1: moving boundary tested for cohomological nontriviality.
- [x] 1 -> 2: commutator, normalized coboundary, cocycle law, zero curvature, and theta
  specialization proved.
- [x] 2 -> 3: theorem family formalized in Lean.
- [ ] 3 -> 4: identify and polarize the fixed non-exact completed-theta/prime class.
