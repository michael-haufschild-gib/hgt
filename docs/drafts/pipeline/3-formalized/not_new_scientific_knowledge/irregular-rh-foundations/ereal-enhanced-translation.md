# Extended-real enhanced translation action

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Topological action underlying enhanced-sheaf convolution and
exponential translation.

## Target

Extend every finite real translation to a proper homeomorphism of `EReal`, lift it over `X`, and
prove compatibility with compactification, projection, and addition of translation parameters.

## Dependency-closed paper proof

For `c ∈ Real`, define `τ_c(t)=t+c` on finite points and fix both infinities. Extended-real
addition by a finite element is continuous at every point; its inverse is addition by `-c`, using
the extended-real cancellation identities. Hence `τ_c` is a homeomorphism and therefore proper.
It fixes `±∞`, restricts to ordinary translation on `Real`, satisfies `τ_0=id` and
`τ_d∘τ_c=τ_{c+d}`. Taking the product with `id_X` gives a proper homeomorphism of
`X × EReal`. First projection is unchanged, and the open inclusion `X × Real → X × EReal`
intertwines finite and compactified translations.

## Lean status

`StokesERealTranslation` formalizes the extended-real translation homeomorphism and additive action
laws, product translation, properness, projection invariance, fixed boundary, and bordered-interior
equivariance. Direct Lean check and targeted module build passed. All declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-24 — paper proof closed; Lean formalization started
- 2026-08-24 — compactified enhanced translation action formalized and axiom-audited
