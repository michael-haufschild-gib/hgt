# Trace-dual fractional ideals have discriminant norms

- **ID:** number-field-trace-duals-have-discriminant-norms
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Dual Hecke unfolding](hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
- **Statement:** For every fractional ideal `I` of a number field, `Norm(dual(I))=(|disc K| Norm(I))⁻¹`, including the zero ideal under the standard totalized inverse.

## Proof

The different is the inverse of the trace dual of the unit ideal.
Mathlib proves that its ideal norm is the absolute field discriminant.
Multiplicativity of the fractional-ideal norm, including compatibility
with inverses, gives `Norm(dual(1))=|disc K|⁻¹`.

The trace-dual identity `dual(I)=dual(1)*I⁻¹` then gives the asserted
formula directly. There is no nonzero-ideal premise and no assumed
discriminant normalization.

## Lean

Module: `GaloisForLFunctions.HTGeometry.NumberFieldTraceDualsHaveDiscriminantNorms`.
Namespace: `GaloisForLFunctions.HTGeometry`.

- `absNorm_numberField_codifferent`
- `absNorm_numberField_traceDual`

The transitive axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`. Final direct source audit passed without warnings:

```
lake --old env lean GaloisForLFunctions/HTGeometry/NumberFieldTraceDualsHaveDiscriminantNorms.lean
```

Wired into `HTGeometry.lean`; the umbrella was not compiled.
