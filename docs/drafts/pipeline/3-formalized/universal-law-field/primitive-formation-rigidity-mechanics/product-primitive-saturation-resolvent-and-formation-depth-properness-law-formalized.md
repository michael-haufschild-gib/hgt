# Product primitive saturation and formation-depth properness — Lean certificate

- **ID:** ULF-PFRM-2-LEAN
- **Stage:** 3 — formalized in Lean 4
- **Paper parent:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/primitive-formation-rigidity-mechanics/product-primitive-saturation-resolvent-and-formation-depth-properness-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutivePrimitiveFormationProperness`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-FORMALIZED] [PRODUCT SATURATION] [DIVIDED-DIFFERENCE CONSERVATION]`
  `[SHARP FORMATION DEPTH] [NO SORRY] [NOT RH]`

## Certified theorem surface

1. `weightedPolynomialInterpolant_eval` — every finite observer packet is reconstructed exactly by
   one weighted polynomial formation.
2. `weightedPolynomialOrbit_denseRange` — for an injective clock and unit source weights, the
   weighted polynomial orbit is dense in the complete product observer.
3. `packetDividedDifference_polynomial_eq_coeff` — the top packet divided difference is the top
   polynomial coefficient.
4. `packetDividedDifference_polynomial_eq_zero_of_natDegree_lt` — every formation below packet
   depth is annihilated.
5. `resolventDividedDifference_eq` and `resolventDividedDifference_ne_zero` — the resolvent packet's
   conserved divided difference is the nonzero reciprocal nodal product.
6. `resolventPacket_not_mem_range_lowDepthPacketMap` — an `N + 1` point resolvent packet is outside
   the image of every formation of degree `< N`.
7. `resolventPacket_mem_range_atMostDepthPacketMap` — the same packet lies in the image at degree
   `≤ N`.

The last two declarations give the exact minimal formation depth. Injectivity is encoded by
`Function.Embedding`; nonvanishing weights are encoded by units; the resolvent pole exclusion is
encoded by a subtype. The sharp theorems therefore have no external hypotheses.

No `sorry`, `admit`, added axiom, `opaque`, `unsafe`, or numerical computation is used.

## Paper boundary

Lean certifies the cyclic full-support saturation and exact finite-packet properness core. The
paper's multi-source active-support closure is a direct finite sum of the certified interpolation
construction but has not yet been given a separate named Lean declaration. The arithmetic
prime-power specialization uses the already formalized rotated logarithmic coefficient law.
