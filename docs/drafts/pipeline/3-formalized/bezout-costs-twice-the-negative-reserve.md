# Bézout costs twice the negative reserve

- **ID:** bezout-costs-twice-the-negative-reserve
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q-II arithmetic majorants and compensated-surface comparison.
- **Statement:** For a nonnegative quadratic reserve `R`, the original-surface source cone with threshold `delta+2R` has Bézout exactly when `delta+R` is nonnegative.
- **Status:** `[PROVED HERE]`; actual-file Lean check and all seven transitive axiom audits passed; external novelty unverified.

## Exact theorem

Let `S` be a real polar surface, with defect bilinear form `delta`. Let `R` be a
symmetric bilinear form, nonnegative on the diagonal, and zero whenever either input
is a fibre. Put `Q(x)=delta(x,x)+2R(x,x)`.

The following conditions are equivalent:

1. The graded source cone of `Q` has Bézout for the original pairing.
2. The closed source cone of `Q` has Bézout for the original pairing.
3. `delta(x,x)+R(x,x)>=0` for every `x`.
4. The surface whose intersection pairing is `S.pair-R` has Hodge index.

The graded source cone has RR exactly when `R(x,x)=0` for every `x`. The closed
source cone has RR exactly when that vanishing condition holds and the original
defect is nonnegative. These are unconditional equivalences between specified data;
no positivity producer is assumed.

## Proof

Condition 3 gives `Q>=R>=0`, `delta<=Q`, and `-delta<=Q`. The quadratic-majorant
discriminant lemma then gives `delta(x,y)^2<=Q(x)Q(y)`. The sharp source-cone
criterion gives closed and graded Bézout. Their equality under a nonnegative reserve
and the existing graded criterion justify passing between the two cone variants.

Conversely, graded Bézout forces `Q>=0` and its diagonal mixed bound gives
`|delta(x,x)|<=Q(x)`, hence condition 3. For closed Bézout, the positive-part
criterion gives `|delta(x,x)|<=max(Q(x),0)`. If `Q(x)<0`, then
`delta(x,x)<=Q(x)<0` since `R>=0`, contradicting that bound. Thus `Q>=0`, and
the same argument applies. This proves 1--3.

The compensated surface has defect `delta+R`; its Hodge index is therefore precisely
condition 3. This is the already-proved compensation identity, applied with the
actual reserve `R`, and proves 3 iff 4.

Graded RR is exactly `Q<=delta`, hence `2R<=0`, which with `R>=0` is `R=0` on
the diagonal. Closed RR is exactly `max(Q,0)<=delta`; since `Q>=delta`, it forces
`R=0` and `delta>=0`. Conversely these two conditions make `Q=delta>=0`, so the
closed RR criterion holds.

## Sharp scalar interpretation

Fix a nonnegative quadratic mass `m`. For `kappa>=0`, the reserve
`Q_kappa=delta+kappa*m` gives original-surface Bézout exactly when
`delta+(kappa/2)*m>=0`. Thus its exact scalar Bézout compensation is twice the
compensation needed to give Hodge index after changing the intersection pairing by
`-(kappa/2)*m`. No assertion that either infimum is attained is required.

For the arithmetic aperture floor `delta>=-C(r)m`, the threshold
`delta+2C(r)m` is therefore justified directly. When the displayed floor is not
optimal, this theorem identifies the precise remaining improvement: the negative
Rayleigh floor itself, rather than a separate mixed estimate.

## Positive survivor

The factor two is a sharp structural law connecting two distinct operations:
changing the intersection pairing and changing source effectivity while keeping the
pairing fixed. The result explains why a Hodge-index compensation cannot be copied
unchanged into a Bézout source reserve. It also reduces every quadratic original-pairing
majorant optimization to an exact diagonal floor problem.

## Lean certificate

Module: `ArithmeticCastelnuovoSeveri/BezoutCostsTwiceTheNegativeReserve.lean`.

The seven audited endpoints in namespace `PolarSurface` are:

- `gradedSourceCone_doubledReserve_bezout_iff`
- `sourceCone_doubledReserve_bezout_iff`
- `sourceCone_doubledReserve_bezout_iff_compensated_hodgeIndex`
- `gradedSourceCone_doubledReserve_riemannRoch_iff`
- `sourceCone_doubledReserve_riemannRoch_iff`
- `sourceCone_defect_add_scalar_reserve_bezout_iff`
- `gradedSourceCone_defect_add_scalar_reserve_bezout_iff`

Each `#print axioms` returned exactly `[propext, Classical.choice, Quot.sound]`.
The final actual-file command passed:

```
lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BezoutCostsTwiceTheNegativeReserve.lean
```

Temporary prints removed; ACS umbrella and README wired. No olean was built for
this leaf. Its already certified aperture-majorant dependency olean was built
only because this actual module imports it.
