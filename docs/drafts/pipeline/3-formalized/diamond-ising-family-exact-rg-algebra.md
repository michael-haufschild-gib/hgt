# Diamond-Ising branching-family exact RG algebra

- **ID:** `diamond-ising-family-exact-rg-algebra`
- **Stage:** 3-formalized
- **Type:** LEAN 4 THEOREM FAMILY / EXACT PHYSICAL RG ALGEBRA
- **Scientific status:** `[FORMALIZED] [UNCONDITIONAL] [PARENT-DERIVED ALGEBRA]`
- **Paper parent:**
  `../2-fully-proven/needs-audit/diamond-ising-family-rg-generation-hypertranscendence.md`
- **Statement:** The exact `b`-branch, two-bond diamond-Ising projective RG weights and rational
  transmissivity family are formalized for arbitrary natural `b`.  The family recovers the
  two-branch map, has exact high- and low-temperature phase-anchor factors, has precisely
  quadratic numerator contact at the high-temperature anchor for positive `b`, and its primitive
  numerator and normalization denominator have no common complex zero.

## Lean module

`GaloisForLFunctions.HTGeometry.DiamondIsingFamilyRG`

File:
`formal/GaloisForLFunctions/HTGeometry/DiamondIsingFamilyRG.lean`

The umbrella module `GaloisForLFunctions.HTGeometry` imports it.

## Formal surface

The module defines

```text
diamondIsingFamilyRG b
diamondIsingFamilyNumerator b
diamondIsingFamilyDenominator b
```

and proves:

```text
diamondIsingFamilyRG_two
diamondIsingBlockSameWeight
diamondIsingBlockDifferentWeight
diamondIsingBlockWeightDifference
diamondIsingBlockWeightSum
diamondIsingFamily_denominator_sub_numerator
diamondIsingFamily_denominator_add_numerator
diamondIsingFamilyNumerator_eval_zero
diamondIsingFamilyDenominator_eval_zero
diamondIsingFamilyNumerator_eval_one
diamondIsingFamilyDenominator_eval_one
diamondIsingFamilyNumerator_X_sq_dvd
diamondIsingFamilyNumerator_secondDerivative_eval_zero
diamondIsingFamilyScalar_noCommonZero
```

In particular Lean proves the physical projective-weight identities

```text
Z_s-Z_d=(2A^2)^b ((1+t^2)^b-(1-t^2)^b),
Z_s+Z_d=(2A^2)^b ((1+t^2)^b+(1-t^2)^b),
```

the exact anchor identities

```text
D_b-N_b=2(1-X^2)^b,
D_b+N_b=2(1+X^2)^b,
```

and

```text
X^2 divides N_b,
(N_b'')(0)=4b.
```

Thus for positive `b` the numerator contact at zero is exactly quadratic.  The complex no-common-
zero theorem proves pointwise noncancellation of the primitive RG numerator and block-normalization
divisor.

## Verification

- Touched-file check:
  `lake env lean GaloisForLFunctions/HTGeometry/DiamondIsingFamilyRG.lean` -- passed.
- Exact cached module build:
  `lake build +GaloisForLFunctions.HTGeometry.DiamondIsingFamilyRG` -- passed.
- Axiom audit of the family reduction, both physical weight identities, quadratic contact, and
  no-common-zero theorem: only `propext`, `Classical.choice`, and `Quot.sound`.
- No numerical certification or broad project build was used.

## Formal boundary

This card does **not** claim that Lean proves the analytic repelling fixed point, Poincare
linearization, Ritt--Becker--Bergweiler classification, beta HT, or DA-scheme invariance.  Those
remain paper-level external mathematics.  They were not introduced as hypotheses, axioms, or
opaque declarations.

The formal contribution is the exact unconditional physical algebra shared by every member of the
branching family, including the normalization divisor that carries the Fisher-zero interpretation.

## Gates

- [x] Existing HTGeometry exact `b=2` module audited before editing.
- [x] Arbitrary-branch physical block weights formalized.
- [x] Arbitrary-branch rational RG map formalized.
- [x] Phase-anchor factors and exact quadratic contact formalized.
- [x] Primitive complex noncancellation formalized.
- [x] Targeted verification and axiom audit passed.
- [ ] Analytic fixed-point theorem formalized.
- [ ] Ritt--Becker--Bergweiler classification formalized.
- [ ] Full HT beta theorem formalized unconditionally.
