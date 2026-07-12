# Stanley--Reisner numerator differential matroid law

- **ID:** `stanley-reisner-numerator-differential-matroid-law`
- **Stage:** 3-formalized
- **Type:** THEOREM ASSEMBLY BRIDGE
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [CONTRIBUTING GEOMETRY ONLY]`
- **Statement:** For every finite family of classes in a finite Stanley--Reisner quotient over
  `C[D]`, complete facet restriction, the coordinate change `x_v=t_v-1`, and finite orbit
  coefficient expansion produce structural differential-operator outputs whose full nonlinear
  differential-independence matroid is exactly the linear matroid of the original quotient classes.

## Exact law

Let `N_i` be finitely many classes in

```text
C[D][x_v:v in V]/I_Delta.
```

Each facet quotient is canonically the polynomial ring on that facet.  Converting its difference
variables by `x_v=t_v-1` and embedding its exponent support into the common vertex exponent type
gives finitely supported rows `Q_i(A,n)` over `C[D]`.  On any differentially independent source
packet indexed by their common finite support, Lean proves

```text
DifferentialIndependent C (Q(D)X)
  <-> LinearIndependent C[D] (N_i).
```

Thus numerator-level facet sewing creates no hidden nonlinear differential circuits and loses no
Stanley--Reisner circuit.

## Lean realization

The formal chain consists of:

- `LocalizationQuotient`: quotienting commutes with localization and finite localized families
  admit one common denominator;
- `FacetPolynomialQuotient`: a coordinate facet quotient is exactly its facet polynomial ring;
- `StanleyReisnerFacetCoordinates`: complete facet polynomial coordinates are faithful;
- `DifferenceTranslationCoordinates`: `x_v=t_v-1` is an algebra equivalence;
- `FacetTranslationCoordinates`: complete finite translation rows preserve and reflect circuits;
- `StanleyReisnerNumeratorDifferentialMatroid`:
  `differentialIndependent_stanleyReisnerNumeratorRows_iff`.

All modules build unconditionally in the project toolchain.

## Boundary

The numerator-level full nonlinear matroid is complete.  The remaining Laurent step is explicit:
represent the common localization denominator by its translation exponent, shift every facet
coefficient support by the corresponding negative exponent, and instantiate that finite Laurent
packet in the formal upper-end prime-log translation family.

## Gates

- [x] exact facet quotient coordinates
- [x] exact difference-to-translation coordinate equivalence
- [x] exact numerator nonlinear differential matroid
- [x] unconditional Lean formalization
- [x] no separate novelty claim apart from the final realized geometry
