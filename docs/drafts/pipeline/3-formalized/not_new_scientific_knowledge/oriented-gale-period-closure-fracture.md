# Identical oriented Gale data can have opposite period-closure effectivity

- **ID:** `oriented-gale-period-closure-fracture`
- **Stage:** 3-formalized
- **Type:** EXACT NO-GO / TOPOLOGICAL POSITIVE SUCCESSOR / LEAN 4
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [NOT STANDALONE NEW SCIENCE]`
- **Research role:** falsifier and positive typing theorem for the Gale--Kolchin field

## Theorem

Let

```text
P_lat=(1,i,1+i),             P_irr=(1,i,sqrt(2)+i)
```

as labelled triples in the real plane underlying `C`.  Their rank-two chirotopes are identical:
every labelled pair has the same determinant sign.  Nevertheless their integral period groups

```text
L_lat=Z-span(P_lat),         L_irr=Z-span(P_irr)
```

have opposite global effectivity phases.  The first is discrete and its period-incidence
multiplier has a continuous left inverse.  The second is nondiscrete and its multiplier has no
continuous left inverse.

The proof is exact.  `L_lat` lies in the standard complex lattice.  Irrationality of `sqrt(2)`
makes `P_irr` rationally independent, so its integral rank is three; no integral rank-three
subgroup of a real two-plane is discrete.  The complete period-effectivity classification then
gives the left-inverse assertions.

Combining this theorem with `exists_nonconstant_fixed_iff_discretePeriodSource` gives the analytic
form: `L_lat` admits a nonconstant global meromorphic fixed gauge, whereas every global
meromorphic `L_irr`-fixed gauge is constant.

## No-go

No invariant factoring only through the real oriented matroid, its chirotope, or its determinant
line can classify global period effectivity or fixed-gauge rigidity.  In particular, the oriented
Gale transform is not the complete source invariant required by the hypertranscendental unified
field.

## Positive successor

The missing datum is not another orientation.  Retain the closure of the integral period group,
or equivalently its continuous character object

```text
dual_Pontryagin(R^d / closure(L)).
```

The oriented Gale dual controls finite dependence and DA support; the period-closure character
object controls the discrete/nondiscrete wall, global fixed gauges, and incidence strictness.  A
viable unified theorem must construct an HT-specific comparison/transgression between these edge
objects.  Merely listing them is not a new theory.

## Lean surface

File: `formal/GaloisForLFunctions/HTGeometry/GalePeriodClosureFracture.lean`.

- `periodChirotope_lattice_eq_irrational`
- `irrationalPeriodTriple_linearIndependent`
- `latticePeriodGroup_discrete`
- `irrationalPeriodGroup_not_discrete`
- `same_chirotope_opposite_period_effectivity`

All declarations are unconditional and the file passes direct Lean verification.

## Novelty gate

The explicit fracture is mathematically useful but not claimed as standalone new science.  The
ingredients are elementary lattice topology and parent period classification.  More broadly,
Panov already treats real vector configurations, Gale duality, rationality/discreteness, and
properness together (`https://arxiv.org/abs/2411.03366`); lattice Gale duality and arithmetic
matroids cover the integral setting (`https://arxiv.org/abs/2409.15227`).

The candidate-new residue is narrower: an exact source-natural comparison identifying an HT
differential-annihilator complex and its meromorphic fixed-gauge/nonclosed-range object as two
edge realizations of one class, verified in more than one natural HT family.

## Gates

- [x] exact oriented-matroid collision proved
- [x] opposite period-topology phases proved
- [x] opposite incidence-effectivity phases proved
- [x] fixed-gauge consequence supplied by the exact existing classification
- [x] positive period-closure character receiver identified
- [x] Lean file directly verified
- [x] parent collision recorded; no standalone novelty claim
