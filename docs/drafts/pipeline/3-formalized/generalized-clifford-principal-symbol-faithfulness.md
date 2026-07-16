# Generalized Clifford principal-symbol faithfulness

- **ID:** `generalized-clifford-principal-symbol-faithfulness`
- **Stage:** 3-formalized
- **Type:** THEOREM / PRINCIPAL SYMBOL / LIE COMMUTATOR / DIFFERENTIAL FIELD
- **Scientific status:** `[LEAN-PROVEN] [AXIOM-AUDITED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.GeneralizedCliffordPrincipalSymbolFaithfulness`

## Claim

Let `K` be a characteristic-zero field, `M` an internal state space, `V` a law space, and

```text
symbol : V -> End_K(M)
```

a linear principal-symbol pencil.  Suspend each internal endomorphism by one unilateral grade
shift, extend it to a derivation of the symmetric observable algebra, and then extend by the
quotient rule to the rational observable field.

The exterior derivation-commutator map factors exactly as

```text
exterior^2 V
  -- internal commutator --> End_K(M)
  -- double grade shift --> End_K(N -> M)
  -- observable Lie lift --> Der_K(L).
```

The double shift and observable Lie lift are injective.  Consequently

```text
ker(differential-field commutator map) = ker(internal commutator map),
```

and the differential-field map is injective if and only if the internal map is injective.
Pairwise commutativity is likewise reflected exactly: two induced field derivations commute if
and only if their internal endomorphisms commute.

## Formal theorem surface

- `symmetricAlgebra_ι_injective`
- `symmetricAlgebraDerivation_commutator`
- `generalizedCliffordObservableFieldLieHom`
- `generalizedCliffordObservableFieldLieHom_injective`
- `endomorphismCommutatorMap`
- `generalizedCliffordShiftOperator_commutator`
- `generalizedCliffordDoubleShiftOperatorLinearMap_injective`
- `generalizedCliffordField_derivationCommutatorMap_factorization`
- `generalizedCliffordField_derivationCommutatorMap_ker_eq`
- `generalizedCliffordField_derivationCommutatorMap_injective_iff`
- `generalizedCliffordShiftFieldDerivation_commute_iff`

## Verification

- Direct touched-file Lean check passed.
- Narrow cached build of
  `+GaloisForLFunctions.HTGeometry.GeneralizedCliffordPrincipalSymbolFaithfulness` passed.
- Axiom audit for all main theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- The formal lint scan reports no proof debt or reachability error for this module.  Its remaining
  reachability failures belong to unrelated concurrently edited modules.

## Significance and novelty boundary

The faithful Lie lift is algebraically natural and is not promoted as new science by itself.  Its
role is exact: it proves that shift suspension and rational observables introduce no artificial
loss of the antisymmetric generalized-Clifford symbol.  Therefore every later commutator kernel,
rank, or discriminant theorem can be proved internally and transported to the differential field
without weakening.

The scientific novelty question belongs to the resulting hypertranscendence-horizon theory and
the Ulrich commutator discriminant, not to this bridge in isolation.

## RH impact

The theorem is a source-fidelity result.  It guarantees that a distinguished arithmetic internal
symbol would retain its full commutator data after passage to the HT field, but it neither supplies
such a symbol for Xi nor implies RH.
