# Unconditional Lean capstone for the all-order multiple-elliptic-gamma structural matroid

- **ID:** `all-order-multiple-elliptic-gamma-structural-matroid-lean-capstone`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean target)
- **Scientific status:** `[FORMALIZATION REQUIRED FOR FINAL PROOF]`
- **Parent:** `all-order-multiple-elliptic-gamma-structural-differential-matroid`
- **Statement:** Formalize without project axioms the concrete all-order additive and
  multiplicative differential-transcendence-rank formulas for generic multiple elliptic gamma.

## Completion criterion

This card closes only when the Lean tree contains the actual multiple elliptic gamma function, its
logarithmic derivative and hierarchy equations, and a theorem equivalent to

```text
dtrdeg_(C(z)) C(z)<P_1(T)Psi_r,...,P_m(T)Psi_r>_delta
  =dim_(C(delta)) span{Pbar_1,...,Pbar_m}
```

for every generic order and every finite structural operator family, together with the
multiplicative product theorem. A theorem parameterized by assumptions that merely restate
elliptic-gamma atomicity, simultaneous telescoping, or the desired independence conclusion does
not satisfy this criterion.

## Formal dependency order

1. differential polynomial evaluation, DA extensions, differential independence, and differential
   transcendence degree;
2. commuting difference-differential fields and several-automorphism parameterized
   Picard--Vessiot theory;
3. the unconditional additive simultaneous telescoping theorem with constant extension and
   algebraically closed descent;
4. meromorphic functions with periods, nondiscrete-period constancy, elliptic curves, elliptic
   function fields, and specialization from a product;
5. theta functions, elliptic gamma, multiple elliptic gamma, and all hierarchy identities;
6. non-torsion elliptic translation orbits, principal parts, and orbital residue obstruction;
7. generic order-one defect-coset atomicity;
8. free differential-shift one-slice nonsummability and nested-star orbit gluing;
9. localized Stanley--Reisner decomposition and the differential-linear rank theorem;
10. all-order additive capstone and multiplicative logarithmic-derivative transfer.

## Current unconditional Lean evidence

`formal/GaloisForLFunctions/SimplicialConstraintTower.lean` proves:

```text
pureOfCard_uniformFacets
ridgeThick_uniformFacets
exists_two_coface_directions_of_pure_ridgeThick
```

`formal/GaloisForLFunctions/DifferentialIndependence.lean` now supplies the field-relative
definitions needed by the actual matroid theorem:

```text
DifferentialIndependent
DifferentialAlgebraicOver
HypertranscendentalOver
```

It proves injective-subfamily preservation, ordinary algebraic independence of order-zero
coordinates, stability under arbitrary per-coordinate derivative shifts, and preservation under
ordinary algebraic scalar extension.

Both modules build under the repository toolchain. `#print axioms` for their principal theorems
reports only `propext`, `Classical.choice`, and `Quot.sound`.

This is the first real dependency of the strengthened theorem. It is not evidence that the
analytic capstone is already formalized.

## Gates

- [x] exact final theorem and anti-shell completion criterion recorded
- [x] first generalized combinatorial dependency implemented and built
- [x] field-relative differential independence and jet-family core implemented and built
- [ ] differential algebra foundation
- [ ] multi-automorphism parameterized Picard--Vessiot foundation
- [ ] unconditional simultaneous telescoping
- [ ] meromorphic and elliptic function-field foundation
- [ ] theta and multiple-elliptic-gamma definitions and hierarchy
- [ ] orbit-principal-part obstruction
- [ ] generic order-one atomic theorem
- [ ] abstract all-order independence induction
- [ ] Stanley--Reisner differential-rank theorem
- [ ] concrete additive and multiplicative capstones
- [ ] `scripts/formal_tools.py lint` passes
- [ ] exact capstone `#print axioms` contains only standard Lean axioms

## Log

- 2026-07-10 -- Opened after the paper theorem passed adversarial audit. The user criterion makes
  full unconditional Lean formalization, rather than a paper proof or hypothesis shell, the final
  proof standard.
- 2026-07-10 -- Formalized the pure ridge-thick two-coface theorem and the uniform-skeleton
  instance as the first dependency of the stronger constraint-tower theorem.
