# Finite localized spectral-support recurrence law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteLocalizedSpectralSupportRecurrenceLaw`
- **Scientific role:** localization-volume recurrence bridge

## Result

Let \(p_i\ge0\), \(\sum_i p_i=1\), and let \(S\) be a nonempty selected
spectral support. Synchronize the clique on \(S\) and leave every omitted
sector isolated. Then
\[
  d-\#\pi_0(G_S)=|S|-1.
\]
For survival-history coefficients \(c_{ij}=p_ip_j\), selected directed mass
is at most one and omitted directed mass is at most
\[
  2\alpha_S,\qquad
  \alpha_S=\sum_{i\notin S}p_i.
\]
Consequently, whenever \(\alpha_S\le\alpha\), some positive integer \(n\)
satisfies
\[
  n\le(Q+1)^{|S|-1},
  \qquad
  \Delta(n)\le4\alpha+\frac{4\pi}{Q+1}.
\]
At this same budget, either the history never exits or an exit is followed
strictly later by a return before the same graph deadline.

## Formal declarations

- `finiteLocalizedSpectralSupportGraph`
- `finiteLocalizedSpectralSupportGraph_componentCard`
- `finiteLocalizedSpectralSupportGraph_rank`
- `finiteLocalizedSubsetTail`
- `finiteLocalizedSpectral_selectedMass_le_one`
- `finiteLocalizedSpectral_omittedMass_le_two_tail`
- `finiteLocalizedSpectral_omittedMass_le_two_alpha`
- `exists_finiteLocalizedSpectralSupport_recurrence`
- `exists_finiteLocalizedSpectralSupport_recurrence_exactTail`
- `finiteLocalizedSpectralSupport_neverExits_or_postExit_return`

## Verification

```text
lake env lean \
  GaloisForLFunctions/RHTower/FiniteLocalizedSpectralSupportRecurrenceLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/FiniteLocalizedSpectralSupportRecurrenceLaw.olean
```

passed. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Boundary

This theorem is deterministic and finite. It does not prove that a
Hamiltonian has localized eigenfunctions or provide a spectral-tail bound.
It becomes an Anderson-locality statement only after a separate
model-specific localization theorem supplies such a bound.
