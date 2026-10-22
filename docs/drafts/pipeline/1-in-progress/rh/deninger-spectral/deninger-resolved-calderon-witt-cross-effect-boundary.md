# Deninger resolved Calderón--Witt cross-effect boundary

- **ID:** `HGT-deninger-resolved-calderon-witt-cross-effect-boundary`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONSTRUCTION / ROUTE-L FRONTIER
- **Date:** 2026-08-02

## Non-overlap audit

Current Möbius--theta and Hellinger--Gamma work constructs coefficient-faithful cofaces,
telescoping chains, pure-Hodge graph capacity, and completed Xi incidence carriers.  Existing
universal laws already prove that disjointly retained factor defects prevent covariance
cancellation.  Repeating either construction would add no knowledge.

Deninger's unique unresolved datum is earlier than those constructions: the actual algebraic
Calderón--Witt source cup alternates two ordered Meyer/rational-Witt cross-effects, while the
Deninger Green comparison adds two transported internal covariance defects.  Both augmentations
can erase a nonzero antidiagonal.

## Conjecture and construction

For a bilinear cross-effect `B : Q -> P -> S`, define its resolved alternating value by

```text
R_B((q,a),(r,b)) = (B(q,b), -B(r,a)) in S x S.
```

Then

```text
codiagonal(R_B(x,y)) = alternatingCrossEffect_B(x,y),
R_B(x,x) = antidiagonal(B(x_Q,x_P)).
```

The two coordinates lie in the disjoint source-derived axes `S x 0` and `0 x S`.  For the actual
algebraic Calderón--Witt source at every prime, the canonical Meyer unit defect and canonical
finite rational-Witt unit packet have nonzero cross-effect.  Hence the source contains a canonical
nonzero resolved self-boundary which is killed by the ordinary alternating cup.  Its one-prime
embedding supplies the same nonzero antidiagonal in the all-prime finite-support source.

## Scientific content

This is not an arbitrary product duplication.  Both ordered coordinates are forced by the actual
source multiplication before alternation, and nonvanishing is forced by the injective first
suspension of a genuine arithmetic-Frobenius-fixed finite rational-Witt packet.  It constructs the
source-side resolved object whose absence made previous factor-retention statements merely
conditional.

It also gives a hostile falsifier for every proposed completed transport: a map observing only the
alternating cup, Haar orientation, or total Green covariance necessarily kills this explicit
source boundary.

## Exact remaining gate

Construct a label-preserving completed chain transport which sends the two ordered source
cross-effect axes to the two Deninger Green internal-defect axes before codiagonalization.  It must
be conservative on the cofinal source-selected resolved span and graph-closed in the actual
Gamma/co-Poisson Hodge boundary topology.  Identifying only the codiagonals is insufficient and
unconditional.

The updated Hellinger--Hodge Green-descent paper identifies the same missing maps as
`L_J : im D_J -> P` and `L_R : im D_R -> Q` on one source-pointed Hausdorff closed graph carrier.
The ordered cross-effect resolution constructed here supplies canonical algebraic models of
`P = S x 0` and `Q = 0 x S`, plus a nonzero source-selected antidiagonal falsifier.  It does not
supply the completed maps `L_J,L_R` or their graph closedness.

## Hostile audit

- The resolved source boundary does not prove RH.
- Its ordinary cup vanishes by alternation, so no boundary-blind source consumer can detect it.
- No fixed divisor witness or admitted sector is chosen after inspecting zeros.
- A completed comparison that sends this boundary to zero would refute conservativity, not prove
  landing.
- `[NOVELTY UNVERIFIED]` External literature audit remains separate; internal corpus search found
  no resolved ordered Calderón--Witt cross-effect construction.

## Balanced-coend transversality

The updated Hellinger--Hodge paper also forces a distinction between two superficially similar
two-channel objects.  A completed balanced Hellinger--Gamma grade has the form

```text
B_n^a(x) = (gamma_n(-a) x, gamma_n(a) x),
```

and both real Gamma gauges are strictly positive.  Therefore

```text
codiagonal(B_n^a(x)) = 0  <->  x = 0.
```

Its range is disjoint from the codiagonal kernel, whereas the nonzero Deninger Green resolved
defect lies entirely in that kernel.  Thus the other route's two Hodge channels cannot be renamed
as Deninger's two factor-defect channels: no nonzero antidiagonal is one finite balanced grade.
This exact no-lift theorem is formalized in
`DeningerResolvedDefectHellingerGammaBalancedCofaceNoGo.lean`.

## Gates

- [x] Internal corpus and concurrent-work nonduplication audit
- [x] Paper proof dependency-closed
- [x] Lean formalization unconditional (direct module check)
- [x] Umbrella wiring and targeted module build
- [ ] Conservative completed source-to-Green resolved transport
