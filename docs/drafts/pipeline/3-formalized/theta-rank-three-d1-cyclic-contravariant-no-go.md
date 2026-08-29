# Theta rank-three D1 cyclic contravariant no-go

- **ID:** S6G-D1-CYCLIC-NG
- **Stage:** 3-formalized
- **Type:** ROUTE-KILL
- **Route:** TCD / S6F finite rank-three D1
- **Novelty:** NOVELTY UNVERIFIED

## Exact attempted RH chain

```text
positive scalar-contravariant form on an adapted-graded sl2 carrier containing source D1
  -> convergent norm/evaluation certificate for source D1
  -> native rank-three D1 on 0 < x < 137/2000
  -> finite TCD/S6F gate
  -> cofinal all-order Hankel/Bezoutian landing
  -> Weil positivity
  -> RH
```

## Verdict

`[PROVED NO-GO]` No adapted-graded source-`sl2` submodule containing
`modularThetaSourcePositiveReflectedEighthPolynomial` admits a positive scalar-contravariant form,
for any real star coefficient. This kills every adapted-graded proper-carrier realization of the
first arrow above.

The invariant boundary `r=k=0` sees source D1 as a nonconstant polynomial in `b`: it vanishes at
`b=1`, while its value at `b=0` is the nonzero seam determinant. Hence some positive adapted-weight
component has nonzero boundary value. Repeated lowering produces an exact finite string

```text
F v = u,   E u = 0,   H v = 2v,   E v != 0.
```

Contravariance applied to `E u = 0` and `F v = u` forces the scalar star coefficient to be zero.
Applying contravariance to `E v` then forces its squared norm to be zero, contradicting positive
definiteness. The argument uses no finite-dimensionality, completion, numerical certificate, or
explicit expansion of D1.

## Formalization

- Module:
  `GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveD1CyclicContravariantNoGo`
- Exact D1 string:
  `exists_modularThetaSourcePositiveReflectedEighth_vacuumString`
- Capstone:
  `modularThetaSourcePositive_no_D1_gradedScalarContravariantCarrier`
- Umbrella:
  `GaloisForLFunctions.HTGeometry`

Verified with:

```text
lake env lean GaloisForLFunctions/HTGeometry/PolynomialODEJetRankThreeSourcePositiveD1CyclicContravariantNoGo.lean
lake build GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveD1CyclicContravariantNoGo
```

The capstone and its two key existence theorems report only
`propext`, `Classical.choice`, and `Quot.sound` under `#print axioms`.

## Corpus and literature position

- `[CORPUS]` The exact source action, adapted coordinates, finite-module no-go, and full-carrier
  no-go supplied the conjecture and proof architecture.
- `[LITERATURE]` Polynomial differential realizations of highest/lowest-weight `sl2` modules are
  standard; Nekrasov--Tsymbaliuk, arXiv:2103.12611, equations (164)--(180).
- `[LITERATURE]` Contravariant forms control weight-module decompositions; Mudrov,
  arXiv:1709.08394, Theorem 6.3.
- No audited source treats this theta D1 cyclic carrier or derives this vacuum-string obstruction.

## Subsequent closure

`S6G-D1-AUTO-GRADE` proves that every source-`E,F`-stable polynomial submodule automatically has
the adapted-component closure assumed here. Therefore the unrestricted scalar proper-carrier route
is now dead. Remaining representation routes require a non-scalar adjoint law,
localization/completion outside the polynomial carrier, or an indefinite form. Direct cross-scale
determinant geometry remains unaffected.
