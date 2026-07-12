# Dyadic Weyl multiplicity RH gate

- **ID:** `dyadic-weyl-multiplicity-rh-gate`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/WeldWeylMultiplicity.lean`
- **Route:** `../../1-in-progress/dyadic-weld-weyl-multiplicity-route.md`

## Theorem

Let `U,V` be invertible `d x d` complex matrices and let `zeta` be a primitive `n`-th root of
unity.  If

```text
U V = zeta V U,
```

then `n | d`.

For `zeta = Bottcher.dyadicRoot k`, the exact Prüfer theorem gives `n=2^k`, hence
`2^k | d`.

An `SEMDyadicWeylModel k h` specializes this relation to the undoubled index space
`Fin zs.length` of an actual `SEMSplitData` object `h`.  Therefore:

```text
internal model at level k for every actual right-half SEM split
  -> RHLadder k;

internal models at every level
  -> RiemannHypothesis;

internal models at cofinally many levels
  -> RiemannHypothesis.
```

## Proof

Taking determinants of `UV=zeta VU` gives

```text
det(U) det(V) = zeta^d det(V) det(U).
```

Both determinants are nonzero, so cancellation gives `zeta^d=1`.  Primitivity gives `n | d`.
For an SEM split, the source theorem `semSplitData_count_eq` identifies `zs.length` with the finite
analytic order of `xi` at the centre.  This is exactly the divisibility predicate in
`rhLadder_iff_toNat_dvd`.  The all-level and cofinal capstones use `rh_iff_forall_ladder` and
`rh_of_rhLadder_cofinal`.

## Non-circularity boundary

The formal model does not assert its own existence.  Its matrices act directly on
`Fin zs.length`; adding an external `2^k`-dimensional clock--shift tensor factor cannot inhabit this
type without first proving that the original hole count has the required factor.  The remaining
open theorem must therefore construct the Weyl action internally from source data.

The Böttcher phase alone is insufficient: a rank-one abelian Prüfer action supplies no projective
commutator.  The positive successor is a rank-two integral weld action whose commutator phase is
source-selected before real/divisible scalar extension.

## Formal surface

- `dyadicWeylPhase_isPrimitiveRoot`
- `dvd_card_of_invertible_weyl_pair`
- `pow_dvd_card_of_dyadic_weyl_pair`
- `SEMDyadicWeylModel`
- `SEMDyadicWeylModel.pow_dvd_holeCount`
- `rhLadder_of_semDyadicWeylModel`
- `riemannHypothesis_of_all_semDyadicWeylModels`
- `riemannHypothesis_of_cofinal_semDyadicWeylModels`

## Verification

`lake env lean GaloisForLFunctions/RHTower/WeldWeylMultiplicity.lean` passes on the repository
toolchain.

## Novelty and significance gate

The determinant argument and finite Weyl-pair dimension law are standard.  The contribution is a
precise glue theorem connecting the corpus's exact Böttcher Prüfer multiplier to the actual SEM
hole-count RH ladder.  It is therefore classified as `not_new_scientific_knowledge`; the potential
new science lies only in constructing the source-built internal action and thereby closing RH.

## Gates

- [x] 0 -> 1: exact finite-dimensional theorem and SEM specialization stated
- [x] 1 -> 2: determinant proof complete
- [x] 2 -> 3: formalized and exact module check passes
- [ ] 3 -> 4: not promoted; construction of the internal action remains open

