# Exponent-zero Euler-gauge foliation core

- **ID:** `exponent-zero-euler-gauge-foliation-core`
- **Stage:** 3-formalized
- **Type:** THEOREM / FORMAL BRIDGE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW IN ISOLATION]`
- **Parent:**
  `../../2-fully-proven/needs-audit/exponent-zero-euler-gauge-foliation-reflection-transversal.md`

## Statement

For an arbitrary prime index type `P`, let `PrimePhase P=P -> Circle`.  Given any nonnegative
family of coordinate weights, phases are equivalent when their relative phase has summable
weighted distance from the identity for every weight.  This is an equivalence relation.  Every
equivalence class contains every finite modification of each of its points, hence is dense in the
full product topology.  The coinduced topology on the quotient is indiscrete.

Specializing the weights to

```text
exp(-sigma log p),       sigma>0,
```

gives the canonical exponent-zero Euler-gauge relation and the same dense-class and indiscrete-
quotient conclusions.

## Proof

The unit-circle estimates

```text
abs(1-omega psi) <= abs(1-omega)+abs(1-psi),
abs(1-omega^(-1))=abs(1-omega)
```

prove closure under products and inverses.  Finite modifications have finitely supported gauge
cost and are therefore summable for every weight.  The existing product-topology theorem makes
finite modifications dense.  Each gauge class is consequently dense, and the existing dense-
fiber quotient theorem makes the coinduced topology indiscrete.

## Formal theorem surface

Implementation:
`formal/GaloisForLFunctions/HTGeometry/ExponentZeroEulerGaugeFoliation.lean`.

The public declarations are:

- `PrimePhase`;
- `IsWeightedEulerGauge`;
- `norm_one_sub_circle_mul_le` and `norm_one_sub_circle_inv`;
- `isWeightedEulerGauge_one`, `isWeightedEulerGauge_mul`, and
  `isWeightedEulerGauge_inv`;
- `weightedEulerGaugeSubgroup`;
- `isWeightedEulerGauge_of_finiteModification_one`;
- `weightedEulerGaugeSetoid`, `weightedEulerGaugeQuotient`, and
  `weightedEulerGaugeClass`;
- `weightedEulerGaugeClass_eq_iff` and `primePhase_mul_eq_self_iff`;
- `weightedEulerGaugeClass_fiber_dense`;
- `weightedEulerGaugeQuotient_coinduced_eq_indiscrete`;
- `PositiveExponent`, `exponentZeroWeight`, `IsExponentZeroEulerGauge`, and
  `exponentZeroEulerGaugeSubgroup`;
- `exponentZeroEulerGaugeSetoid`, `exponentZeroEulerGaugeQuotient`, and
  `exponentZeroEulerGaugeClass`;
- `exponentZeroEulerGaugeClass_eq_iff`;
- `exponentZeroEulerGaugeClass_fiber_dense`;
- `exponentZeroEulerGaugeQuotient_coinduced_eq_indiscrete`.

## Scientific role

Dense subgroup classes and indiscrete quotients are standard topology.  The new-science candidate
is the parent theorem's combined arithmetic geometry: these exact classes preserve continued
Euler divisors, contain maximal differential-rank HT frames, and meet a fixed completed reflection
class transversally.  This card certifies the new group/topology component without claiming that
the component is novel by itself.

## Gates

- [x] weighted phase gauges form an equivalence relation
- [x] every finite modification belongs to the relative gauge class
- [x] every weighted gauge class is dense
- [x] weighted gauge quotient topology is indiscrete
- [x] exponent-zero specialization defined and proved positive
- [x] exponent-zero classes proved dense
- [x] exponent-zero quotient topology proved indiscrete
- [x] direct module check
- [x] theorem-area build
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] project lint and generated-index check
