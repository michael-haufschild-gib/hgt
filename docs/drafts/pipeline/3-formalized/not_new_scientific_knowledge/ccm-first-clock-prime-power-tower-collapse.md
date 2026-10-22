# CCM first-clock prime-power tower collapse

- **ID:** `ccm-first-clock-prime-power-tower-collapse`
- **Stage:** 3-formalized
- **Type:** THEOREM / RIGHT-TO-LEFT RH FRONTIER REDUCTION
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [SOURCE-PURE] [NO COMPUTATION] [NOT CLAIMED NOVEL]`
- **Parent:** `ccm-first-clock-landau-completeness-law.md`
- **Formal endpoint:** `CCMFirstClockPrimeHalfWaveDominance`

## Goal

Classify the sign of every complete one-prime-power contribution to the physical first CCM sine
clock.  Remove prime-power interference from the RH-complete half-wave wall before attempting any
cross-prime transport.

For a prime `p`, put

```text
T=L/log p,
N=floor T,
r=p^(-1/2),
theta=2*pi/T.
```

When `p<=exp L`, the complete `p`-tower contribution is

```text
Tower_p(L)=log p * sum_(j=1)^N r^j sin(j*theta).          (1)
```

## Theorem

1. If `1<=T<2`, then `N=1`; the tower is the irreducible-prime atom and is counter-phased.
2. If `N=2`, then

   ```text
   Tower_p(L)
     =log p * r*sin(theta)*(1+2*r*cos(theta)).            (2)
   ```

   Hence it is nonnegative for every `p>=5`.  The only possible two-power tower defects occur
   for `p=2` and `p=3`, with exact sign wall

   ```text
   1+2*p^(-1/2)*cos(2*pi*log p/L).                       (3)
   ```

3. If `N=3`, then `Tower_p(L)>0` for every prime `p`.
4. If `N>=4`, then `Tower_p(L)>0` for every prime `p`.

Consequently every negative prime-power tower in the complete first-clock source is either:

```text
an irreducible outer prime exp(L/2)<p<=exp L,
or one of the two explicit square windows p=2,3.         (4)
```

The infinite composite prime-power sector outside `(4)` is unconditionally oriented.

This is useful source reduction, not proposed paper headline. Finite damped-geometric summation
and the prime-power decomposition of the von Mangoldt function are classical. Corpus contribution
is exact assembly at physical CCM first clock and direct wiring to existing RH-complete endpoint.

## Paper attack

The finite geometric identity is

```text
sum_(j=1)^N r^j sin(j*theta)
 =r[sin(theta)-r^N sin((N+1)theta)+r^(N+1)sin(N theta)]
   /(1-2r cos(theta)+r^2).                               (5)
```

Write `T=N+delta`, `0<=delta<1`.  Then

```text
sin(N theta)=-sin(delta theta),
sin((N+1)theta)=sin((1-delta)theta).                     (6)
```

The denominator in `(5)` is strictly positive.

- `N=2`: use `sin(2theta)=2sin(theta)cos(theta)`.  Since `r<=1/2` for `p>=5`,
  `1+2r cos(theta)>=1-2r>=0`.
- `N=3`: here `pi/2<theta<=2pi/3`.  Put `x=cos theta in [-1/2,0)`.  Division by the positive
  `r sin theta` gives

  ```text
  4r^2 x^2+2r x+1-r^2.                                  (7)
  ```

  Its unrestricted quadratic minimum is `3/4-r^2`, positive because every prime has
  `r^2=1/p<=1/2`.
- `N>=4`: now `0<theta<=pi/2`.  Both angles in `(6)` lie in `[0,theta]`, so their sines are at
  most `sin theta`.  The numerator in `(5)` is therefore at least

  ```text
  r*sin(theta)*(1-r^N-r^(N+1)).
  ```

  Since `r<=1/sqrt 2`, `N>=4`, and

  ```text
  r^N(1+r)<=r^4(1+r)<=1/4*(1+1/sqrt 2)<1,
  ```

  this is strictly positive.

No zero data, prime estimate, asymptotic argument, or numerical evaluation enters.

## Exact RH connector

Lean defines bad-tower residual as sum of:

1. exponent-one primes in `(exp(L/2),exp L]`;
2. the negative part of the exact `p=2` two-power tower when `2<=L/log 2<3`;
3. the negative part of the exact `p=3` two-power tower when `2<=L/log 3<3`.

Good-tower mass is remaining nonnegative tower sum. Lean proves

```text
ccmFirstClockPrimeSineMass
  = goodTowerMass - badTowerResidual.                    (8)
```

Then reduced source law

```text
badTowerResidual
  <= ccmFirstClockContinuousHalfWaveBudget + goodTowerMass
```

is equivalent to `CCMFirstClockPrimeHalfWaveDominance`, hence to RH.

Formal endpoint:

```text
CCMFirstClockReducedTowerDominance ↔ RiemannHypothesis.
```

## Hostile audit checklist

- [x] diagonal exponential tilting is not used
- [x] Dirichlet convolution is not used
- [x] no prime-power tower is discarded
- [x] hard cutoff `p^j<=exp L` is retained exactly through `N=floor(L/log p)`
- [x] first-clock phase `2*pi*log(p^j)/L` is retained exactly
- [x] verify no equivalent tower-classification theorem exists in current Lean corpus
- [x] verify prime-power reindexing APIs against current mathlib toolchain
- [x] complete dependency-closed paper proof
- [x] formalize tower theorem
- [x] formalize first-clock mass decomposition
- [x] wire reduced dominance `↔ RH`
- [ ] post-proof primary-literature audit

## Lean implementation

Module:

```text
formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockPrimePowerTowerCollapse.lean
```

Main declarations:

```text
firstClockGeometricTower_mul_denominator
criticalPrimeFractionalTower_pos_of_three_le
criticalPrimeFractionalTower_two_nonneg_of_five_le
sum_primePow_Icc_eq_sum_primesLE
ccmFirstClockPrimeSineMass_eq_sum_primePowerTowerMass
ccmFirstClockPrimePowerTowerMass_firstClock_pos_of_three_le
ccmFirstClockPrimePowerTowerMass_firstClock_nonneg_of_length_two_of_five_le
ccmFirstClockPrimePowerTowerMass_firstClock_nonpos_of_length_one
ccmFirstClockPrimeSineMass_eq_reducedGood_sub_bad
ccmFirstClockReducedTowerDominance_iff_rh
```

Direct check:

```text
lake env lean GaloisForLFunctions/RHTower/CCM/CCMFirstClockPrimePowerTowerCollapse.lean
```

passed without warnings. Module is imported by `GaloisForLFunctions.RHTower`.

## Frontier after collapse

No further one-prime manipulation can close reduced dominance:

1. all towers with at least three admitted modes are strictly positive;
2. all two-mode towers at `p>=5` are nonnegative;
3. only finite small-square anomalies `p=2,3` remain from composite modes;
4. cofinally, unresolved negative mass is exactly exponent-one outer-prime mass.

Therefore next right-to-left problem is cross-prime or prime--Gamma transport of outer-prime mass.
Tower refinement itself is exhausted.
