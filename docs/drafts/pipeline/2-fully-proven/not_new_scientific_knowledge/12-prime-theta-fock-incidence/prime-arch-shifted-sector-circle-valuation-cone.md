# Prime--archimedean shifted sector-circle and valuation-cone law

- **ID:** `prime-arch-shifted-sector-circle-valuation-cone`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE] [BRIDGE] [NOT AN RH PROOF]`
- **Parents:** `prime-arch-explicit-circle-state-reflection-law`,
  `prime-arch-scaled-hausdorff-divisor-value-law`,
  `sonin-coupled-finite-gram-closure-rh`
- **Statement:** The unconditional narrow sector and endpoint radius of every Xi reciprocal-square
  atom produce positive analytic circle states for the first thirteen shifted prime--Gamma moment
  tails.  The thirteenth state uses the exact degree-thirteen real-part polynomial, extending past
  the quadratic-cosine cutoff.  For polynomial Hankel tests this gives explicit nonnegative
  coefficient cones at every valuation `v <= 6`.  Consequently the coupled-Sonin one-sided
  comparison need only be proved on the complementary residual family in order to imply RH.

## Setup

For every multiplicity copy `q` of the Xi divisor put

```text
u_q = xiZeroCopyReciprocalSquare(q),
m_n = normalizedPrimeArchMoment(n) = sum_q u_q^(n+1),
R   = 2/41.
```

All displayed sums below are absolutely convergent.  The formal corpus proves

```text
Re(u_q) > 0,
Im(u_q)^2 <= Re(u_q)^2/84,
|u_q| < R,                                                   (1)
```

and that every `m_n` is real.  The radius follows directly from the endpoint height gap:
`|u_q|` is the reciprocal of the squared centered distance of the zero, whose imaginary square is
strictly greater than `41/2`.

For `s >= 0` define

```text
J_s = sum_q |u_q|^(s+1),
w_(Xi,s)(e^(it)) = m_s + 2 sum_(n>=1) m_(s+n) cos(nt).       (2)
```

## 1. Sectorial lower mass

Write `u_q=|u_q| exp(i theta_q)`.  The first two inequalities in `(1)` give

```text
|theta_q| <= arctan(1/sqrt(84)) <= 1/sqrt(84).              (3)
```

Fix `0 <= s <= 11` and put `k=s+1`, so `1 <= k <= 12`.  The elementary inequality
`cos x >= 1-x^2/2` gives

```text
Re(u_q^k)
  = |u_q|^k cos(k theta_q)
 >= (1-k^2/168)|u_q|^k.
```

Set

```text
c_s = 1-(s+1)^2/168.                                       (4)
```

Then `c_s >= 1/7 > 0`.  Taking real parts through the absolutely convergent divisor sum yields

```text
m_s = sum_q Re(u_q^(s+1)) >= c_s J_s > 0.                  (5)
```

The strict inequality uses the unconditional nonemptiness of the Xi divisor.  Thus the initial
mass of each of these twelve shifted tails is positive without RH.

### 1a. Exact thirteenth-power extension

The quadratic lower bound for cosine becomes useless at `k=13`, but the sector itself does not.
Write `u=x+iy`, `X=x^2`, and `Y=y^2`, so `x>0` and `0<=Y<=X/84`.  Exact expansion gives

```text
Re(u^13)/x
 = X^6-78X^5Y+715X^4Y^2-1716X^3Y^3
     +1287X^2Y^4-286XY^5+13Y^6.                            (5a)
```

The paired terms satisfy

```text
715X^4Y^2-1716X^3Y^3 >= 694X^4Y^2,
1287X^2Y^4-286XY^5 >= 0,
```

and on `0<=Y<=X/84`,

```text
X^2-78XY+694Y^2 >= X^2/6.
```

For the last inequality, multiplying by six reduces it to nonnegativity of
`5X^2-468XY+4164Y^2`, and the exact identity

```text
5X^2-468XY+4164Y^2
 = (X-84Y)*((2929/588)X-(347/7)Y)+(11/588)X^2
```

has nonnegative factors on the stated sector.

Hence `Re(u^13)>=x^13/6`.  Also `|u|<=(85/84)x` and the exact rational inequality
`(85/84)^13<4/3` yield

```text
Re(u^13) > |u|^13/8.                                      (5b)
```

Consequently

```text
m_12 >= J_12/8 > 0.                                       (5c)
```

The atomwise estimate, its Xi specialization, `(5c)`, the endpoint disk bound, and the later
geometric moment envelope are formalized in
`PrimeArchShiftThirteenCircleCone.lean`.

## 2. Thirteen explicit positive circle states

For every `n >= 1`, the radius bound in `(1)` gives

```text
|m_(s+n)| <= R^n J_s.
```

Hence

```text
2 sum_(n>=1) |m_(s+n)|
 <= 2 R/(1-R) J_s
 = 4/39 J_s
 <= delta_s m_s,                                           (6)
```

where

```text
delta_s = 4/(39 c_s)
         = 224/(13*(168-(s+1)^2)).                         (7)
```

For `s <= 11`, `delta_s <= 28/39 < 1`.  The Fourier series in `(2)` therefore converges
absolutely and real-analytically and satisfies the pointwise two-sided estimate

```text
(1-delta_s)m_s <= w_(Xi,s) <= (1+delta_s)m_s.               (8)
```

Consequently

```text
d mu_(Xi,s) = w_(Xi,s)/m_s dm                              (9)
```

is an unconditional probability measure equivalent to Haar measure, with

```text
integral_T zeta^n d mu_(Xi,s)(zeta) = m_(s+n)/m_s.          (10)
```

For `s=12`, `(5c)` replaces `(5)`.  The same endpoint-radius calculation gives

```text
2 sum_(n>=1)|m_(12+n)| <= 4/39 J_12 <= 32/39 m_12.         (10a)
```

Thus `(8)--(10)` also hold at `s=12` with

```text
delta_12=32/39<1.                                         (10b)
```

This does not assert that the shifted sequence is a positive real power-moment sequence.  It
constructs an ordinary unit-circle state whose reflected Gram kernel is that shifted Hankel tail.
The distinction is exactly the orientation gap.

## 3. Shifted coefficient cones

Let

```text
q(z)=b_0+b_1 z+...+b_N z^N,
E_tail(q)=sum_(n=1)^N b_n^2.
```

Using circle conjugation as the reflection, the shifted Hankel value has the polarization formula

```text
(1/m_s) sum_(i,j) b_i b_j m_(s+i+j)
 = ||C_q||^2_(L2(mu_(Xi,s)))-||S_q||^2_(L2(mu_(Xi,s))).    (11)
```

Haar orthogonality and `(8)` imply

```text
(1/m_s) sum_(i,j) b_i b_j m_(s+i+j)
 >= (1-delta_s)b_0^2-delta_s E_tail(q).                    (12)
```

Therefore the shifted Hankel value is nonnegative whenever

```text
224 E_tail(q)
 <= (1960-13*(s+1)^2)b_0^2.                               (13)
```

For the new shift `s=12`, the sharper bound `(10b)` gives the additional cone

```text
32 E_tail(q) <= 7 b_0^2.                                  (13a)
```

This is a genuine unconditional part of each shifted RH-equivalent cone, not a positivity
assumption on that cone.

## 4. Polynomial valuation law

Let a nonzero real polynomial have its canonical factorization

```text
P(X)=X^v q(X),  q(0)=b_0 != 0.                              (14)
```

The prime--Gamma Hankel value of `P` is

```text
Q(P)=sum_(i,j) b_i b_j m_(2v+i+j),                          (15)
```

so the relevant shift is `s=2v`, not `v`.  For every `v <= 5`, `(13)` gives

```text
224 E_tail(q)
 <= (1960-13*(2v+1)^2)b_0^2
 -> Q(P) >= 0.                                              (16)
```

Since the right-hand coefficient decreases with `v`, the uniform low-valuation cone

```text
v <= 5 and 224 E_tail(q) <= 387 b_0^2                      (17)
```

is also unconditionally nonnegative.  Formula `(16)` includes nonconstant tests with zero
constant coefficient, a region not reached by the unshifted central-coefficient theorem.  At
`v=0` it also slightly sharpens that theorem's sufficient coefficient ratio.

For each fixed `v`, the formal theorem
`sequenceTraceHankelNonnegative_shiftedPrimeArchMomentTail_iff_riemannHypothesis v` says that
positivity of the *entire* tail beginning at `m_(2v)` is equivalent to RH.  The result above
therefore discharges an explicit interior cone in the first six of those exact RH-equivalent
tails.  At `v=6`, `(13a)` additionally gives

```text
32 E_tail(q) <= 7 b_0^2 -> Q(X^6 q) >= 0.                 (17a)
```

In particular, the uniform cone `v<=6` and `32 E_tail(q)<=7b_0^2` is unconditional.  The result
now reaches the first seven shifted RH-equivalent tails while making no claim about complementary
tests.

## 5. Residual coupled-Sonin chain

Let `A_sector` consist of zero together with the integer polynomials satisfying `(16)` for
`v<=5`, or `(17a)` for `v=6`, using their canonical valuation factorization, and put

```text
R_sector = Z[X] minus A_sector.                              (18)
```

For a nondegenerate Sonin aperture `a`, write

```text
G_a(P) = soninAllPrimeCoupledNormalizedPolynomialGramValue(a,P).
```

The Lean corpus proves `G_a(P) >= 0`.  Consider the restricted, source-side condition

```text
for every P in R_sector and every epsilon > 0,
  there exists a nondegenerate aperture a such that
  G_a(P) <= Q(P)+epsilon.                                   (19)
```

Then `(19)` implies RH.  Indeed, if `P` lies in `R_sector` and `Q(P)<0`, choose
`epsilon=-Q(P)/2`; `(19)` contradicts `G_a(P)>=0`.  If `P` lies in `A_sector`, `(16)` already gives
`Q(P)>=0`.  Thus every integer-polynomial prime--Gamma Hankel value is nonnegative, and the
formal countable Hankel criterion gives RH.

The resulting top-down chain is

```text
reciprocal-square endpoint radius + one-eighty-fourth sector law
  -> thirteen positive shifted circle states
  -> seven unconditional polynomial-valuation coefficient cones
  + restricted coupled-Sonin variational comparison only on R_sector
  -> complete integer prime--Gamma Hankel positivity
  -> RH.                                                     (20)
```

This strictly weakens `SoninCoupledPrimeArchPerTestVariationalUpperBound`: no Sonin comparison is
needed on `A_sector`.  It does not make the remaining comparison automatic.  High valuation and
low-valuation tail-dominant tests remain the live source-value problem.

## Hard boundary

The proof uses only an atomwise sector and radius.  Such information cannot control arbitrarily
high powers: the phase of `u_q^k` eventually leaves every fixed positive half-plane even while
`u_q` remains in the narrow original sector.  Therefore this argument cannot by itself prove all
shifted Hankel positivity or RH.  Extending `(16)` cofinally requires a new value relation that
couples phases across divisor atoms, not a smaller bound on the same individual sector.

The positive reformulation is precise: the existing sector law supplies a finite-depth base
region; the missing theorem is a source coupling on the residual coefficient family, for which the
coupled-Sonin Rayleigh comparison is one concrete non-sign interface.

## Literature calibration

The trigonometric moment construction and its Toeplitz positivity are classical.  Positive Hankel
operators and reflection-positive circle representations are treated by Adamo--Neeb--Schober,
[Reflection positivity and Hankel operators](https://arxiv.org/abs/2105.08522), and
Neeb--Olafsson,
[Reflection positivity for the circle group](https://arxiv.org/abs/1411.2439).  For the broader
complex moment problem and positive-definite extensions, see Cichon--Stochel--Szafraniec,
[The complex moment problem: determinacy and extendibility](https://arxiv.org/abs/1803.03066).

The targeted literature search did not locate a theorem that turns a fixed narrow sector of
complex atoms into all-order Hankel positivity; that implication would in any case be false for
the phase-winding reason above.  The
project-specific bridge is the application of the formal Xi endpoint constants to the thirteen
shifted densities, the valuation indexing `(15)`, and the resulting restriction of the Sonin
source comparison.

## Formal reuse surface

The formal proof should reuse:

```text
re_pow_thirteen_gt_one_eighth_norm_pow_of_sector
re_xiZeroCopyReciprocalSquare_pow_thirteen_gt_one_eighth_norm_pow
norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne
one_eighth_xiShiftThirteenAbsoluteMass_le_normalizedPrimeArchMoment_twelve
xiShiftThirteenAbsoluteTail_le
abs_normalizedPrimeArchMoment_twelve_add_le
summable_xiZeroCopyReciprocalSquare_pow
xiCentralReciprocalMoment_im_eq_zero
normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment
xiZeroCopy_fortyOne_div_two_lt_im_sq
xiThermalNode_pos
xiThermalOrientationTerm_le_one_over_eightyFour_node_sq
shiftedPrimeArchMomentTail
momentPolynomialTransform_X_pow_sq_eq_shiftedPrimeArchMomentTail
sequenceTraceHankelNonnegative_shiftedPrimeArchMomentTail_iff_riemannHypothesis
primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis
soninAllPrimeCoupledNormalizedPolynomialGramValue_nonneg
riemannHypothesis_of_soninCoupledPrimeArchPerTestVariationalUpperBound
```

The reusable theorem belongs in `HTGeometry`: a summable family of complex atoms in a sector
`|arg u|<=alpha` and disk `|u|<=R` yields a positive shifted Fourier density whenever
`cos((s+1)alpha)>2R/(1-R)`.  The rational Xi specialization and the restricted Sonin consumer
belong in `RHTower`.

## Gates

- [x] 0 -> 1: shifted-tail source objects and non-circular sector input identified
- [x] 1 -> 2: sectorial lower mass and two-sided shifted density bounds proved
- [x] 1 -> 2: explicit shifted coefficient cones and correct `2v` valuation indexing proved
- [x] 1 -> 2: restricted coupled-Sonin comparison proved sufficient for RH
- [x] literature calibration: classical carrier theory separated from the Xi-specific constants
- [x] 2 -> 3: exact thirteenth-power sector bound, Xi specialization, mass lower bound, endpoint
  disk, and geometric tail envelope formalized
- [ ] 2 -> 3: formalize the circle-density packaging, coefficient cone, and residual consumer
- [ ] proof input: establish the restricted Sonin comparison `(19)`, or a different source-value
  theorem covering `R_sector`, without Xi zero orientation or an RH-equivalent representing measure

## Lean progress log — 2026-08-22

Added and wired the reusable unconditional density layer:

```text
HTGeometry/SummableCircleFourierDensity.lean
RHTower/PrimeArchShiftedCircleDensity.lean
```

The generic module defines the literal symmetric Fourier density, proves absolute-tail two-sided
bounds, measurability, Haar integrability, and finiteness of its density measure.  The Xi
specialization defines the actual shifted densities
`m_s + 2 sum_(n>=1) m_(s+n) Re(z^n)` and proves their explicit
`m_s ± (4/39) J_s` bounds and strict positivity for every `s <= 12`, using the exact
thirteenth-power endpoint at `s = 12`.  The completed public capstones are
`symmetricCircleFourierDensityMeasure_finite` and
`primeArchShiftCircleDensity_pos_of_le_twelve`.

Targeted leaf builds and axiom checks passed; both capstones depend only on Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` foundations.  This closes the density existence,
coercivity, and finite-measure portion of the `2 -> 3` gate.  It does **not** close probability
normalization, Fourier-moment recovery, the weighted `L²` reflection carrier, or the residual
Sonin comparison; the card remains at Stage 2.
