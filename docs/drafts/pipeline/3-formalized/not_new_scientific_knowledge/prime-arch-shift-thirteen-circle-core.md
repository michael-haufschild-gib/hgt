# Prime--archimedean shift-thirteen circle core

- **ID:** `prime-arch-shift-thirteen-circle-core`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM / `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `prime-arch-shifted-sector-circle-valuation-cone`

## Target

Every reciprocal-square Xi-divisor atom `u` satisfies

```text
Re(u^13) > |u|^13/8,
|u| < 2/41.
```

If

```text
J_12 = sum_q |u_q|^13,
```

then the twelfth normalized prime--archimedean moment and all later moments obey

```text
J_12/8 <= normalizedPrimeArchMoment(12),
|normalizedPrimeArchMoment(12+n)| <= (2/41)^n J_12.
```

These inequalities cross the `s=11` cutoff of the quadratic cosine estimate.  On paper they give
the thirteenth strictly positive circle density, with relative deviation at most `32/39`, and the
new valuation-six coefficient cone

```text
32*E_tail(q) <= 7*q(0)^2 -> Q(X^6 q) >= 0.
```

## Mechanism

For `u=x+iy`, set `X=x^2` and `Y=y^2`.  The formal Xi sector input is
`x>0` and `Y<=X/84`.  Exact expansion of `Re(u^13)` groups the potentially negative terms with
their adjacent positive terms.  The remaining quadratic is bounded below by `X^2/6` through the
factorization

```text
5X^2-468XY+4164Y^2
 = (X-84Y)*((2929/588)X-(347/7)Y)+(11/588)X^2.
```

Thus `Re(u^13)>=x^13/6`.  The same sector gives `|u|<=(85/84)x`, and
`(85/84)^13<4/3` yields the strict one-eighth bound.  The endpoint height gap supplies the disk
radius.  Absolute summability then transfers the atomwise estimates to the source moments with
divisor multiplicity intact.

## Lean declarations

File:
`formal/GaloisForLFunctions/RHTower/PrimeArchShiftThirteenCircleCone.lean`

- `re_pow_thirteen_gt_one_eighth_norm_pow_of_sector`
- `re_xiZeroCopyReciprocalSquare_pow_thirteen_gt_one_eighth_norm_pow`
- `norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne`
- `xiShiftThirteenAbsoluteMass`
- `summable_xiShiftThirteenAbsoluteMass`
- `one_eighth_xiShiftThirteenAbsoluteMass_le_normalizedPrimeArchMoment_twelve`
- `xiShiftThirteenAbsoluteTail_le`
- `abs_normalizedPrimeArchMoment_twelve_add_le`

## Positive boundary

The exact algebra discharges one additional shifted state and one additional polynomial valuation.
It also shows why the earlier failure at exponent thirteen was a failure of the quadratic cosine
minorant, not of the Xi sector.  The same fixed sector still cannot control arbitrarily high powers:
phase winding eventually exits the positive half-plane.  The remaining RH load is therefore the
source coupling on valuation at least seven and on the tail-dominant complement of the seven known
coefficient cones.

## Gates

- [x] exact degree-thirteen sector inequality formalized
- [x] Xi atom specialization formalized
- [x] rational endpoint disk formalized
- [x] thirteenth absolute-mass lower bound formalized
- [x] all-later-moment geometric envelope formalized
- [x] leaf module checked directly
- [x] RHTower umbrella wired
- [ ] circle-density and valuation-six finite-coefficient packaging formalized
- [ ] residual source coupling proved
- [ ] RH
