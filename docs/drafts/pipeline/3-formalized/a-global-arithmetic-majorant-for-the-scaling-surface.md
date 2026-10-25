# A global arithmetic majorant for the scaling surface

- **ID:** a-global-arithmetic-majorant-for-the-scaling-surface
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Q-II; extension of the aperture majorant.
- **Statement:** One quadratic arithmetic reserve gives Bézout and ampleness on the entire compact-source scaling surface, independently of RH, and fails RR.
- **Status:** `[PROVED HERE, paper and Lean]`; actual-file final audit passed; external novelty unverified.

## Source estimate

For a real compact C² source `f`, put

`m(f)=integral f²`, `w(f)=integral (exp(|t|) f(t))²`,
`S=sum_n Lambda(n)/n^(3/2)`, and `gamma=gammaHardyPhaseRate 0`.

The corpus proves finiteness and nonnegativity of `S`, the exact identity
`markovEnergy(f)=archForm(f)-primeSum(f)`, and
`archForm(f)>=2 gamma m(f)` from its nonnegative archimedean Lévy energy.

For every real shift `a`, the weighted correlation bound is

`|integral f(t) f(t-a)| <= exp(-|a|) w(f)`.

Indeed, `|a|<=|t|+|t-a|`. Multiply this exponential inequality by
`|f(t)f(t-a)|`, integrate, and apply the ordinary translation Cauchy–Schwarz
bound to `exp(|t|)|f(t)|`. Its square integral is `w(f)`. All integrands have
compact support, so no integration or summation interchange needs an additional
analytic premise. The same argument without the initial absolute value suffices
for the following upper estimate.

At `a=log n`, `n>=2`, the two correlations in `primeSum` are each at most
`w(f)/n`. Multiply by the nonnegative atom `Lambda(n)/sqrt(n)` and sum. The actual
prime sum is summable by compact support, and the dominating series is the proved
three-halves von Mangoldt series. Consequently

`primeSum(f) <= 2 S w(f)`.

## One aperture-independent reserve

Write `o(f)=integral f(t)sinh(t/2)` and `e(f)=integral f(t)cosh(t/2)`.
The exact source identity on the original scaling surface is

`delta(f,f)=archForm(f)-primeSum(f)-2 o(f)^2+2 e(f)^2`.

Define the positive reserve

`R(f)=(2 |gamma|+1)m(f)+2 S w(f)+2 o(f)^2`.

The preceding estimates give `R(f)>=m(f)` and
`delta(f,f)+R(f)>=m(f)+2 e(f)^2>=m(f)`.
Thus the arithmetic quadratic form

`Q(f)=archForm(f)-primeSum(f)+2 o(f)^2+2 e(f)^2`
`     +2(2 |gamma|+1)m(f)+4 S w(f)`

satisfies `Q=delta+2R`, `Q>=2m`, and both `delta<=Q` and `-delta<=Q`.
Its definition uses only actual source integrals and prime atoms. It has no
aperture parameter and no zero-side sum. Quadraticity follows from the original
bilinear defect, weighted L² pairing, and squared linear pole moments.

The diagonal-majorant discriminant lemma now proves
`delta(f,g)^2<=Q(f)Q(g)` for arbitrary compact sources, even with different
supports. The source cone with nonnegative two fibre degrees and
`Q(f)<=2 deg_H deg_V` therefore has Bézout on the original pairing. The strict
mass floor proves ampleness; an effective class of ample degree zero is the zero
class itself.

RR would require `Q<=delta`, hence `2R<=0`. A nonzero compact source has positive
mass and `R>=m>0`, a contradiction. This is an unconditional RR failure for this
specific globally compatible cone, not a failure of all source-defined RR cones.

## Cone structure

The same source set is a pointed generating convex cone. For effective classes with
fibre degrees `(a,b)` and `(c,d)`, positivity of the quadratic form `Q` gives
`|Q(x,y)|<=sqrt(Q(x)Q(y))<=2 sqrt(abcd)<=ad+bc`. Therefore
`Q(x+y)<=2(a+c)(b+d)`, proving additive closure. Nonnegative scalar closure follows
from quadratic homogeneity, and zero belongs to the cone.

If both `x` and `-x` are effective, both degrees vanish and `Q(x)<=0`; its strict mass
floor forces the source to vanish, after which the degrees force the two fibre
coordinates to vanish. Thus the cone is pointed. For any class, adding sufficiently
large positive multiples of both fibres makes the degrees positive and their product
larger than its fixed finite reserve. The added pure-fibre class is itself effective,
so every class is a difference of two effective classes. These arguments also apply
to the aperture majorant cone. The global cone statements are formalized below; the aperture geometry leaf is checked separately.

## New insight and remaining work

The aperture dependence of the elementary Chebyshev compensation is removable.
The summable three-halves prime series and an exponential source weight give a
single global mixed bound. Independent Bézout is therefore available on the
original surface without an aperture-gluing premise. Matching the RR reserve
still requires removing the explicit positive `2R` while retaining the mixed
bound; this construction does not prove that step.

## Exact corpus dependencies

- `RHTower/WeilMarkovFarOutNonnegativeOddPositivity.lean`: `archForm_ge`,
  `levyEnergy_nonneg`, and the unweighted translation square-integral bound.
- `RHTower/WeilMarkovOddSectorTrivialZeroSquares.lean`:
  `markovEnergy_ofReal_eq_archForm_sub_primeSum`, `summable_primeSum_terms`.
- `RHTower/MontgomeryPrimeSideBounds.lean`:
  `summable_vonMangoldt_div_threeHalves`, `vonMangoldtThreeHalvesMass_nonneg`.
- `ArithmeticCriticalityTheory/FullZeroFormWeilPositivity.lean`: exact pole split.
- ACS: original defect/full-zero-form identity and sharp source cone criteria.

## Lean certificate

`ArithmeticCastelnuovoSeveri/GlobalArithmeticMajorantsSupplyBezout.lean` passed
its actual-file `lake --old env lean` audit. The eight endpoint audits reported
only `propext`, `Classical.choice`, and `Quot.sound`:

- `globalArithmeticMajorant_eq_defect_add_two_reserve`
- `defect_sq_le_globalArithmeticMajorant`
- `globalArithmeticMajorantCone_bezout`
- `globalArithmeticMajorantCone_ample_zero`
- `globalArithmeticMajorantCone_not_riemannRoch`
- `globalArithmeticMajorantCone_convex`
- `globalArithmeticMajorantCone_generating`
- `globalArithmeticMajorantCone_pointed`

The module also proves the mass floors, ampleness, additive closure, nonnegative
scalar closure, and zero membership. The source estimates are independently
certified in `ExponentialSourceMassControlsTheFullPrimeSum`. Both modules are
wired into the programme umbrella; the umbrella was not compiled.
