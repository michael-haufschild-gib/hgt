# Literal base-Cauchy nuclear synthesis

- **ID:** ULF-LBCNS-001
- **Stage:** 3-formalized
- **Lean:** `RHTower.RoutePPrimitiveBurnolBaseNuclearSynthesis`
- **Paper:** `2-fully-proven/universal-law-field/direct-subunit-anchor/literal-base-cauchy-nuclear-synthesis.md`

Lean constructs the vector-valued counting-measure `L2` field containing every zero-clock
prime-depth P-G186 Burnol column and its Bochner synthesis `A_base`.  It proves

```text
||f_alpha||^2 = baseCauchyWeight(alpha),
||A_base||_HS^2 = B_base,
A_base A_base* is Schatten-1,
Re Tr(A_base A_base*) = B_base < 1.
```

No divisor and no adjustable normalization occur.  P-G186 supplies the complete off-diagonal
prime-mixed Gram.  This is the source-side positive survivor of retired ULF-INHD-001; it is not an
identification with the integral horizon projector and does not prove RH.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
