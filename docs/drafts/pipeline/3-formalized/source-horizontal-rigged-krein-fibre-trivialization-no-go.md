# Source-horizontal rigged Krein fibre trivialization no-go

- **ID:** source-horizontal-rigged-krein-fibre-trivialization-no-go
- **Stage:** 3-formalized
- **Route:** CCM-FU · `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`
- **Module:** `GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinFibreTrivializationNoGo`
- **Capstone:** `sourceHorizontalRiggedPointwiseKreinGeometryRouteKilled`

## Result

For any two off-wall parameters in one open half-strip, an explicit diagonal linear equivalence on
the fixed Deninger height--Köthe source:

- transports the distinguished all-prime reservoir functional exactly;
- transports the positive diagonal exactly;
- is an exact congruence of the full rigged Witt pairing;
- is tame in both directions, with one height-seminorm loss.

Across opposite chambers the same map is an exact anti-congruence
(`preDivisorRiggedPrimeWittPairing_transport_anti`).

## Route consequence

Pointwise topological Krein-isomorphism invariants are constant on each open half-strip, so they
cannot force the critical wall for a hypothetical off-wall Xi zero. This kills that CCM-FU
producer class before `SuzukiRectangularWardDefectBoundedness`. Surviving mechanisms must retain
fixed source coordinates or cross-fibre relative trace/connection data.

## Proof kernel

With `w_s(p)=|primeGammaCofinalBocksteinCoefficient(rate(s),p)|`, set
`r_p(s,t)=sqrt(w_s(p))/sqrt(w_t(p))`. Corpus Bockstein estimates give
`c_t/p ≤ w_t(p) ≤ 1`; hence `r_p` and its reciprocal have polynomial height growth. Diagonal
multiplication preserves the Köthe source tamely. The identities
`sqrt(w_t)r_p=sqrt(w_s)` and `w_t r_p²=w_s` transport every defining series termwise.

## Novelty audit through 2026-08-31

No matching classification was found in Suzuki 2606.09096v2, Kalmes--Santacreu 2301.11186,
Dimant--Villafañe 1706.04901, or Connes--Consani 1910.14368.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalRiggedKreinFibreTrivializationNoGo.lean`
- `lake build GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinFibreTrivializationNoGo`
- capstone axioms: `propext`, `Classical.choice`, `Quot.sound` only
- imported by `GaloisForLFunctions/RHTower.lean`
