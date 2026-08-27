# Reflected bi-heat measure-separated sign rate cone

- **ID:** RBH-MSSF
- **Stage:** 1-in-progress
- **Type:** CONTINUUM INCOMMENSURATE SIGNED RECEIVER CLASSIFICATION
- **Parent:** RBH-CSSF
- **Frontier-map policy:** read only

## Frozen conjecture

Let `P,Q` be nonzero finite positive Borel measures on rate space.  For one
`kappa>0`, assume

- `0<r<kappa` for `P`-almost every rate;
- `kappa≤r` for `Q`-almost every rate;
- `∫ sinh(r*T) dQ < ∞` for every `T>0`.

Define continuum reporter and wall derivative

`F(t) = -∫ sinh(r*t) dP(r) + ∫ sinh(r*t) dQ(r)`,

`D = ∫ r dQ(r) - ∫ r dP(r)`.

Prove exact classifications

`0≤D ↔ ∀t>0, 0<F(t)`

and

`0≤D ↔ ∀t, F(t)=0 ↔ t=0`.

Then factor arbitrary real-power RBH aperture integrals and derive an exact RH
receiver for every measure packet in cone.

## Corpus basis

- RBH-CSSF proves countable theorem by dominated `tsum`, strict separator
  comparison, low-tail normalization, and local uniform convergence.
- `measure_eq_of_laplace_eq` and continuum spectral-measure modules supply
  finite-measure and Laplace-transform infrastructure.
- Mandatory corpus search found no separated-support hyperbolic-sine integral
  cone.

## Attack

1. Derive low and first-moment integrability from finite mass and bounded support;
   derive high first-moment integrability from positive hyperbolic moment at `T=1`.
2. Apply dominated convergence to `F(t)/t` as `t→0+`.
3. Integrate separator comparison for `sinh(r*t)/r`; strictness follows from
   positive low mass and an almost-everywhere strict integrand.
4. Normalize low integral by `sinh(kappa*t)`.  Pointwise decay plus unit
   domination gives zero by dominated convergence; positive high mass supplies
   eventual lower bound `Q(univ)*sinh(kappa*t)`.
5. Endpoint domination gives compact-interval continuity; IVT converts `D<0`
   into additional positive zero.
6. Transport through continuum real-power aperture factorization.

## Provisional literature audit

Variation-diminishing Laplace-transform theory is classical.  The primary
source checked (Grussler--Sepulchre, arXiv:2006.10030) treats finite-dimensional
Toeplitz/Hankel systems and does not state this continuum hyperbolic-sine
moment-cone classification or RBH aperture theorem.  Search found applications
invoking general variation diminution, but no exact match.  Priority remains
provisional pending expert review.

## Status

- Mandatory corpus search complete.
- Conjecture frozen.
- Proof attack active.

## Failure boundaries

- Signed measures with more than one support-order sign change.
- Positive mass on separator from low side (`r=kappa`).
- Infinite measures or missing high hyperbolic moments.
- Source-derived measure law and non-diagonal rate collisions.

