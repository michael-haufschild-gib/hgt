# Rank-three meromorphic source-effectivity reconstruction

- **ID:** `rank-three-meromorphic-source-effectivity-reconstruction`
- **Stage:** 3-formalized
- **Type:** ANALYTIC RECONSTRUCTION BRIDGE / ACTUAL ELLIPTIC-GAMMA SOURCE INSTANCE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [BRIDGE, NOT NEW SCIENTIFIC KNOWLEDGE]`
  `[NOT AN RH RESULT]`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/EllipticGammaProductSourceEquation.lean`
  - `formal/GaloisForLFunctions/HTGeometry/MeromorphicRankThreeSourceBoundary.lean`
  - `formal/GaloisForLFunctions/HTGeometry/CriticalPeriodTrace.lean`
- **Parent:** `../../1-in-progress/hypertranscendental-constraint-hodge-duality.md`

## Statement

Let `v=(1,sigma,tau)` be linearly independent over `Q`, let `H=Z v_0+Z v_1+Z v_2`, and let
`M(C)` be the global meromorphic fraction field.  Translation by the three generators defines a
commuting difference-differential field.  For nonzero `x`, write

```text
B_v(x)_i = x(z+v_i)/x(z).                                  (1)
```

Then:

1. the common fixed field of the three translations is exactly `C`;
2. `B_v(x)=B_v(y)` iff `x=c y` for a unique `c in C^x`;
3. if `x,y` have fraction presentations regular and nonzero at one common pointed source value
   `z_*`, then

   ```text
   B_v(x)=B_v(y) and x(z_*)=y(z_*)  implies  x=y;           (2)
   ```

4. the same theorem applies to the genuine elliptic-gamma product constructed in the Lean tree.

Thus the unpointed source constraint reconstructs both objects and source-preserving morphisms up
to the exact scalar gauge `C^x`; one regular source pointing kills precisely that gauge.

## Explicit source production

The elliptic-gamma boundary in `(1)` is not defined by translating the answer.  On paper, direct
reindexing of the convergent numerator and denominator double products proves three explicit
source laws.  Period one has ratio one.  The two structural shifts peel off the one-dimensional
products

```text
Theta_tau(z)
 = product_(k>=0) (1-q^(k+1)/x(z)) (1-q^k x(z)),           (3)

Theta_(sigma|tau)(z)
 = product_(j>=0) (1-p^(j+1)/x(z)) (1-p^j x(z)),           (4)
```

where `p=exp(2 pi i sigma)`, `q=exp(2 pi i tau)`, and `x(z)` is the centered additive coordinate.
On the common regular locus,

```text
Gamma(z+1)=Gamma(z),
Gamma(z+sigma)=Theta_tau(z) Gamma(z),
Gamma(z+tau)=Theta_(sigma|tau)(z) Gamma(z).                 (5)
```

Equations `(3)`--`(5)` are constructed solely from the source periods and one-dimensional
products.  They close the circularity gate left open by a boundary fingerprint defined from
`Gamma` itself.  Lean certifies every zero/successor factor identity needed by the two structural
reindexings and the complete period-one product equation.  Packaging the two infinite double
product reindexings as whole-product equalities remains outside the Lean certificate.

## Proof of reconstruction

If `B_v(x)=B_v(y)`, then `h=x/y` is fixed by the three generators.  The fixed periods form an
additive subgroup, so generator invariance extends to all of `H`.  Rank-three rational
independence makes `H` nondiscrete and supplies nonzero periods tending to zero.  Meromorphic
rigidity therefore makes `h` constant.  Conversely every constant multiple has the same source
boundary.  This proves the exact scalar-torsor statement.

For pointed fraction presentations, equality in the fraction field clears to a cross-product
identity in the global analytic subring.  Literal germ evaluation at `z_*` sends
`x=c y` to `x(z_*)=c y(z_*)`.  Nonvanishing and equality of the pointed values force `c=1`, proving
`(2)`.  The calibration is actual evaluation; it does not store the meromorphic germ.

## Critical completion and separated integral comparison

For a nonzero physical period `lambda`, put

```text
w(lambda)=lambda/(1+|lambda|).                              (6)
```

The critical trace is the complete `ell^infinity` space of decoded bounded coordinates.  Its
analytic realization multiplies the `lambda` coordinate by `w(lambda)`.  Every coordinate has the
explicit inverse `w(lambda)^(-1)`, while the phase `w(lambda)/|w(lambda)|` has Hermitian norm one.
The unscaled `lambda` is retained as a separate integral comparison datum.  This is the precise
completion of the divided-difference collar; it is not the closure of the raw nonclosed range in
the wrong norm.

The analytic origin is the source identity

```text
(f(z+lambda)-f(z))/lambda
  = integral_0^1 f'(z+t lambda) dt,                         (7)
```

whose limit at `lambda=0` is the vertical derivative.  Mixed difference cubes give the higher
derivatives, and Cauchy estimates give the factorial, Gevrey-one boundary.  The full paper proof
is in
`../../2-fully-proven/not_new_scientific_knowledge/critical-divided-difference-period-incidence.md`.

## What this closes and what it does not

This theorem closes the analytic reconstruction and morphism gate on the natural irrational
triptic source class.  Together with the existing gamma gerbe, integral orbit divisor, Hermitian
connective structure, period-incidence phase transition, and finite facet Hodge gap, it supplies
all components of the proposed source-effectivity object on this stratum.

It does **not** yet prove the global five-realization conservativity theorem.  That theorem still
requires typed comparison morphisms showing that the analytic, group--Cech/monodromy, spectral,
Hermitian, and integral outputs come from one source-pure lift and that equality of all five
outputs reconstructs the complete lift rather than merely the standard wedge germ.

## Novelty and anti-theatre gate

The product functional equations, fixed-field rigidity, and normalization of a scalar solution
torsor are parent mathematics.  They are not claimed as new scientific knowledge.  Their role is
load-bearing: they discharge the previously open non-circular analytic reconstruction gate for an
actual HT source.

- `[ANTI-THEATRE -- PASS]` The boundary is explicit in source parameters, the pointing is literal
  regular evaluation, and source-preserving morphisms are classified as the residual scalar
  torsor.
- `[NOVELTY -- BRIDGE]` No novelty claim is made for this card.
- `[SIGNIFICANCE -- PROGRAMMATIC]` The theorem upgrades the triptic analytic model from anomaly
  detection to exact pointed reconstruction.
- `[RH BOUNDARY]` No zeta source, zero divisor, positivity theorem, or RH consequence occurs.

## Lean certificate

New declarations include:

- `ellipticGammaProduct_add_one`;
- `ellipticGammaForwardFactor_add_sigma_zero`;
- `ellipticGammaForwardFactor_add_sigma_succ`;
- `ellipticGammaBackwardFactor_add_sigma`;
- `ellipticGammaForwardFactor_add_tau_zero`;
- `ellipticGammaForwardFactor_add_tau_succ`;
- `ellipticGammaBackwardFactor_add_tau`;
- `rankThree_generator_jointFixed_iff_constant`;
- `rankThreeGeneratorMultiplicativeBoundary_eq_iff_constant_multiple`;
- `RegularPointedMeromorphicPresentation.eq_toMero_of_same_sourceBoundary_and_value`;
- `eq_ellipticGammaMero_of_same_sourceBoundary_and_value`;
- `criticalPeriodTraceRealization_injective`;
- `criticalPeriodTrace_reconstruction`;
- `norm_criticalPeriodPhase`.

## Gates

- [x] actual three-period translation action constructed
- [x] generator invariance extended to the full physical period subgroup
- [x] joint-fixed field proved equal to the complex constants
- [x] unpointed boundary proved nonconservative
- [x] source-preserving morphisms classified by `C^x`
- [x] literal regular-point evaluation proved to kill exactly the scalar gauge
- [x] actual elliptic-gamma product specialized
- [x] three explicit source equations proved on paper from product reindexing
- [x] structural zero/successor factor identities and period-one product equation formalized
- [ ] whole-product `sigma` and `tau` reindexings packaged in Lean
- [x] complete critical trace and coordinate reconstruction formalized
- [ ] global field identity for `(5)` packaged as analytic-subring boundary elements
- [ ] five realization comparisons proved jointly conservative on the full effective lift
- [ ] independent specialist audit
