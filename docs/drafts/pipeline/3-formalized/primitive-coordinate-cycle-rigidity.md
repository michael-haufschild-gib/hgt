# Primitive coordinates force a finite full cycle

- **ID:** PRIMITIVE-COORDINATE-CYCLE-RIGIDITY-20261009
- **Stage:** 3-formalized
- **Type:** BRIDGE; external novelty unverified; corpus only
- **Parent:** `polynomial-exterior-cycle.md`

## Exact result

Let A be an arbitrary type, K a field, T a permutation of A and u:A→K an injective nonzero coordinate. Suppose all u(a)^d agree, d>0, ζ is a primitive d-th root, and u(Ta)=ζu(a). Then T is a cycle on all of A. For any chosen a₀∈A, the orbit map Fin d→A, k↦T^k a₀, is bijective. In particular Nat.card A=d. Finiteness of A is a conclusion, not an assumption.

## Corpus audit

The documented `IsCycleOn IsPrimitiveRoot` lexical search returned no hits. Inspected installed `IsPrimitiveRoot.pow_inj`, `IsPrimitiveRoot.eq_pow_of_pow_eq_one`, `Equiv.Perm.IsCycleOn`, and `Nat.card_congr` provide the algebraic ingredients. No external sources or numerical enumeration were used. This is not an external novelty certificate.

## Complete paper proof [PROVED HERE]

Induction gives u(T^k a)=ζ^k u(a). If two indices i,j<d give the same orbit point, apply u and cancel u(a₀)≠0. Primitivity makes ζ^i=ζ^j imply i=j. Conversely, for any a, the quotient u(a)/u(a₀) has d-th power one. The inspected primitive-root classification expresses it as ζ^k for k<d. Coordinate injectivity then gives a=T^k a₀. This proves the orbit bijection. Choosing each a as basepoint shows every pair lies in the same permutation cycle, and the finite orbit bijection gives the exact natural cardinality.

## Formal certificate — 2026-10-09

`formal/GaloisForLFunctions/HTGeometry/PrimitiveCoordinateCycle.lean` contains four public theorems: `coordinate_perm_pow`, `bijective_orbit_of_primitive_coordinate`, `isCycleOn_of_primitive_coordinate`, and `natCard_eq_of_primitive_coordinate`. First scratch check, production leaf build, all four standard-only axiom audits and final actual-source `lake env lean` check pass. Final log is empty. Audit log: `/tmp/hgt-primitive-coordinate-cycle-axioms.log`; final log: `/tmp/hgt-PrimitiveCoordinateCycle-final.log`. The module is wired into the HTGeometry umbrella. The next index/lint refresh will include this module and the reciprocal-coordinate construction currently in progress.

The subsequent index refresh passed (`/tmp/hgt-reciprocal-coordinate-index.log`). Authoritative global lint reports only the unrelated unreachable module `RHTower.PaperMaassFourierReconstruction`; no error concerns these modules (`/tmp/hgt-reciprocal-coordinate-lint.log`).

The actual polynomial exterior coordinate and its intertwining with the positive large-circle monodromy are still required. This theorem proves that, once that explicitly constructed coordinate is verified, both full cyclicity and degree-many sheets follow without a separate root-counting premise. It does not itself assert the exterior monodromy or RH.
