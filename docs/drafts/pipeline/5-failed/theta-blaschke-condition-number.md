# [FALSIFIED CONSUMER] Theta Blaschke readers do not read the completed critical trace

- **ID:** theta-blaschke-condition-number
- **Stage:** 5-failed
- **Type:** FALSIFIED TRANSFORM BRIDGE / RETAINED FINITE INFRASTRUCTURE
- **Date:** 2026-07-10
- **Parent:** `../2-fully-proven/new/xi-theta-source-seam.md`
- **Statement:** The Blaschke reader exactly interpolates square rates in a Laplace variable, but
  the completed critical trace is Fourier in the logarithmic variable. Therefore this reader is not
  a coefficient coordinate supplied by the completed trace.

## Adjudication

`XiThetaCriticalTrace.lean` proves the exact identity

`completedRiemannZeta₀(1/2+it) = Fourier(xiThetaLogSource)(t/(4*pi))/2`

and then

`completedRiemannZeta₀(1/2+it) = Re(Fourier(xiThetaPositiveSource)(t/(4*pi)))`.

The Blaschke construction below interpolates resolvents at the square rates `pi*m^2` in the
additive heat/Laplace variable. Those are different transforms: after `x=exp u`, a heat atom is
`exp(u/4-pi*m^2*exp u)`, not `exp(-pi*m^2*u)`. No boundary-Hardy pairing derived from the completed
Mellin trace was produced because the proposed pairing has the wrong independent variable.

This does **not** show that the cosine trace loses the positive source: real half-line cosine
transforms can be injective. It shows only that the Blaschke reader is not the promised coordinate
functional on that trace.

## Later correction: composite route survives

The direct consumer remains falsified, but xi-theta-heat-reparametrization.md proves that inverse
logarithmic Fourier followed by y=exp(u)-1 converts the physical atom exactly into

exp(-pi m squared) exp(-pi m squared y).

Multiplication by exp(pi m squared) removes precisely this boundary shift and returns the ordinary
heat exponential. Therefore the Blaschke reader is viable as a **composite fixed-index reader**,
not as a direct critical-trace pairing. The live replacement card is
`theta-composite-heat-reader.md`.

## Medalist lens

The completed theta source has a genuine lower-supported half `h_+`.  Its heat frequencies are

`lambda_m=pi m^2`, `m>=1`.

A coefficient reader is a boundary Hardy function `Q_n` satisfying

`Q_n(lambda_m)=delta_(n,m)`.                                  (1)

The load-bearing question is not existence.  It is the least possible norm in (1): does moving
off diagonal preserve the archimedean decay, or merely move the inverse cost into the dual vector?

## Candidate moves

1. `[SEARCH]` Use finite Lagrange interpolation.  This ignores the infinite tail and gives no
   stable norm.
2. `[BRIDGE]` Use the right-half-plane Blaschke product with zero set `{pi m^2}`.
3. `[CONJECTURE]` The minimal interpolation norm is a native archimedean condition number whose
   exact value determines whether the half-source can feed the Perron seam without hidden loss.

## Finite probe

After scaling `z` by `pi`, define for `N>=n>=1`

`Q_(n,N)(z) = 2n^2/(z+n^2)
  * product_(1<=m<=N,m!=n) [(z-m^2)/(z+m^2)] [(n^2+m^2)/(n^2-m^2)]`.     (2)

Then

`Q_(n,N)(n^2)=1`,

`Q_(n,N)(m^2)=0` for `1<=m<=N`, `m!=n`.                      (3)

On the imaginary boundary every factor `(z-m^2)/(z+m^2)` has modulus one.  Hence the boundary
amplification is entirely the normalization product.

## Infinite probe and exact norm

Let

`B(z)=product_(m>=1) (z-lambda_m)/(z+lambda_m)`.

The Blaschke condition holds because `sum 1/lambda_m<infinity`.  The canonical reader is

`Q_n(z)=B(z)/(B'(lambda_n)(z-lambda_n))`.                     (4)

Equivalently, its normalization is the reciprocal of

`B_without_n(lambda_n)
 = product_(m!=n) |(n^2-m^2)/(n^2+m^2)|`.

Euler's sine and hyperbolic-sine products give

`|B_without_n(lambda_n)|=pi n/sinh(pi n)`.                   (5)

With the half-plane `H2` norm `(1/(2pi)) integral_R |f(it)|^2 dt`, the evaluation kernel at
`lambda` has squared norm `1/(2lambda)`.  Therefore

`||Q_n|| = sqrt(2lambda_n)/|B_without_n(lambda_n)|
          = sqrt(2/pi) sinh(pi n)`.                          (6)

## Optimality attack

Let `f in H2(C_+)` satisfy (1).  Its zeros at every `lambda_m`, `m!=n`, force

`f=B_without_n g`

with `g in H2` and `||g||=||f||`, since the Blaschke factor is inner.  At `lambda_n`,

`g(lambda_n)=1/B_without_n(lambda_n)`.

The reproducing-kernel inequality gives

`||f||=||g|| >= sqrt(2lambda_n)|g(lambda_n)|`,

which is exactly the right side of (6).  The canonical reader (4) attains equality.  Thus the
exponential cost is not an artifact of one construction.

## Interpretation and attack

- `[SURVIVES]` Exact non-diagonal theta coefficient extraction exists for every fixed `n`.
- `[FALSIFIED]` Non-diagonal extraction automatically preserves completion at uniformly bounded
  cost.  The optimal dual norm grows as `sinh(pi n)`.
- `[NOT YET FATAL]` Perron support transfer fixes `n` before negative depth tends to infinity, so a
  finite `kappa_n` can still be paid.  The condition number blocks uniform-in-`n` arguments but not
  a fixed-index seam contradiction.
- `[FALSIFIED]` The boundary Hardy pairing of the positive theta resolvent is the transform exposed
  by the completed Mellin trace.
- `[REDIRECT]` The correct coordinates are logarithmic translations by `2 log m`; positive
  truncation creates an exact moving-boundary commutator. See
  `../3-formalized/new/xi-theta-critical-log-translation-seam.md`.

## Lean plan

1. [x] Formalize the finite rational probe (2) and exact evaluations (3).
2. [x] Prove the imaginary-boundary modulus identity and the unconditional bound
   `||Q_(n,N)(0)|| >= 2(5/3)^floor(n/2)`.
3. Expose the infinite Blaschke/Hardy factorization only if the needed analytic product and Hardy
   interfaces can be built without a new unproved Prop.

## Novelty and significance gate

- `[SEARCH]` Blaschke interpolation, reproducing kernels, and Euler products are parent theory.
- `[BRIDGE]` Their specialization to the theta spectrum gives the exact formula (6).
- `[CONJECTURE — NOVEL x SIGNIFICANT]` The native invariant is the archimedean dual condition
  number and its role in the completed-source seam.  Promotion as new knowledge requires the
  completed-Mellin-to-Hardy bridge and a reflected-charge theorem; the finite algebra alone is
  exempt formal infrastructure, not a discovery claim.

## Gates

- [x] 0 -> 1: exact candidate, optimality attack, and nonfatality audit stated.
- [x] 1 -> 5: the required transform bridge is false by exact variable comparison.
- [x] finite infrastructure formalized in `ThetaBlaschkeProbe.lean`; the analytic bridge remains.
- [x] finite algebra retained in `ThetaBlaschkeProbe.lean`; no RH-facing promotion.
