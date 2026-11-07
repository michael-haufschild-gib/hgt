# Gradient energy controls translations

- **ID:** euclidean-gradient-translation-bound
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [local Sobolev compactness](cubic-kernel-local-sobolev-compactness.md)
- **Statement:** `‖τ_a u−u‖₂≤‖a‖‖∇u‖₂` on the complete Euclidean energy graph.

For compactly supported `C¹` functions, integrate the directional derivative
along `x+t a`, `0≤t≤1`. Cauchy–Schwarz bounds the squared increment by
`‖a‖²` times the segment's gradient energy. Tonelli and translation invariance
remove the translated argument from the spatial integral. Taking square
roots yields the bound. Both sides are continuous in the graph norm, so the
inequality extends to the graph closure.

The construction works for complete real inner-product spaces with a
right-invariant, s-finite Borel measure finite on compact sets. In finite
dimension the actual Lebesgue measure meets these conditions.

Lean: `Sobolev/EuclideanEnergy.lean`, `EuclideanTranslations.lean`, and
`TranslationEnergyBound.lean`; endpoints `norm_translateL2_sub_toL2_le` and
`norm_translateL2_sub_h1ToL2_le`. All three direct source checks passed.
Transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

Source: Adam Benenson, rellich-kondrachov commit
`70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`, Euclidean `H1`, `Translation`,
`TranslationEstimate`, `TranslationEstimateL2`, and `TranslationEstimateH1`.
This classical analytic input does not itself give arithmetic cancellation.
