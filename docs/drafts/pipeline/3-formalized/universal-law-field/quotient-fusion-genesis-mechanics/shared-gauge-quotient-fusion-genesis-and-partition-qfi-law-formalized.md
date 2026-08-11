# Shared-gauge quotient--fusion genesis and partition-QFI law — Lean certification

- **ID:** `ULF-QFGM-1`
- **Stage:** 3 — formalized in Lean 4
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/quotient-fusion-genesis-mechanics/shared-gauge-quotient-fusion-genesis-and-partition-qfi-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.SharedGaugeQuotientFusion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

Lean certifies the exact denominator-free commutator between quotienting and fusion.  For two
interest--gauge Gram blocks `(c_i,b_i,q_i)`, let

```text
det_i = c_i * q_i - b_i^2.
```

Then

```text
c1*c2*det_fused
  - c2*(c1+c2)*det_1
  - c1*(c1+c2)*det_2
= (c2*b1 - c1*b2)^2.
```

The right side is the cross-multiplied incompatibility of the two locally optimal gauges.
Therefore genesis is nonnegative and vanishes exactly when those gauges agree.  This is a closed
polynomial theorem: no denominator, minimizer, positivity hypothesis, or endpoint assumption is
required.

## Certified declarations

| Mathematical clause | Lean declaration |
|---|---|
| weighted genesis numerator | `quotientFusionGenesisNumerator` |
| pairwise slope-mismatch reconstruction | `quotientFusionGenesisNumerator_eq_pairwise` |
| centered common-gauge form | `capA_mul_quotientFusionGenesisNumerator_eq_centered` |
| binary quotient--fusion conservation | `binaryQuotientFusionGenesis` |
| unconditional nonnegativity | `binaryQuotientFusionGenesis_nonneg` |
| exact zero/compatibility classification | `binaryQuotientFusionGenesis_eq_zero_iff` |
| parity--clock Gram determinant | `booleanClockGramDet_eq` |
| binary partition-QFI conservation | `binaryPartitionTransverseInformationConservation` |
| full closed capstone | `sharedGaugeQuotientFusion_capstone` |

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/SharedGaugeQuotientFusion.lean
lake build GaloisForLFunctions.HTGeometry.SharedGaugeQuotientFusion
lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
python3 scripts/formal_tools.py lint --check-generated
```

Direct leaf elaboration and foreground leaf build pass.  Umbrella source elaboration passes after
the leaf object is built.  Axiom prints for every declaration in the table report only
`propext`, `Classical.choice`, and `Quot.sound`.

No computation certificate, `sorry`, `admit`, project `axiom`, `opaque`, `unsafe` declaration,
RH premise, Xi specialization, divisor endpoint, or cofinal completion is used.

## Exact boundary

Lean certifies the finite algebraic kernel and QFI normalization.  The finite-dimensional Hilbert
projection interpretation, general partition-tree formulation, and cofinal closed-range/admission
extension remain paper or Stage-1 work.  No source theorem yet forces the common gauge needed for
an RH selector.
