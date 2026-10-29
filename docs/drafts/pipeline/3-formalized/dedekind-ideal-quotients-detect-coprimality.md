# Dedekind ideal quotients detect coprimality

- **ID:** dedekind-ideal-quotients-detect-coprimality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke Gauss sums](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** For a nonzero ideal `m` in a Dedekind domain and any ideal `I`, `(m:I)=m` if and only if `m+I=(1)`.

## Proof

Put `J=m+I`. Since `m` is nonzero, so is `J`. The fractional ideal
`N=mJ⁻¹` lies inside the unit ideal because `m≤J`, hence is an integral
ideal. It satisfies `NJ=m` and `NI≤m`. If `(m:I)=m`, then every element
of `N` belongs to `m`, so `mJ⁻¹≤m`. Multiplying by `m⁻¹` gives `J⁻¹≤1`.
A nonzero proper integral ideal has nonintegral inverse, so `J=(1)`.

Conversely, write `1=x+y`, with `x∈m` and `y∈I`. If `rI⊆m`, then
`r=rx+ry∈m`. The reverse inclusion `m≤(m:I)` always holds.

The proof also covers the zero ideal `I`; only the stated nonzero
condition on `m` is necessary. The fraction field is constructed
canonically, with no additional arithmetic premise.

## Lean

Module: `GaloisForLFunctions.HTGeometry.DedekindIdealQuotientsDetectCoprimality`.
Declaration:
`GaloisForLFunctions.HTGeometry.ideal_colon_eq_self_iff_sup_eq_top`.

The transitive `#print axioms` audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Scratch verification and the final
direct source audit pass without warnings:

```
lake --old env lean GaloisForLFunctions/HTGeometry/DedekindIdealQuotientsDetectCoprimality.lean
```

Wired into `HTGeometry.lean`; the umbrella was not compiled.
The Hecke consumer uses this criterion to identify primitive trace
frequencies with ideals coprime to the finite modulus.
