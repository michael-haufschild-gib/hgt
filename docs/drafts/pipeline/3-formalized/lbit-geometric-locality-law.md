# L-bit geometric-locality law

- **ID:** `lbit-geometric-locality-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/LBitGeometricLocalityLaw.lean`

## Exact law

On an \(n\)-site binary l-bit chain, let \(\mathcal S_{n,R}\) be the
nonempty supports whose active-site diameter is at most \(R\). If every
coefficient outside this family vanishes, then
\[
  \boxed{\tau(J)\le|\mathcal S_{n,R}|.}
\]
The bound is sharp: rationally independent coefficients on the allowed
supports give equality. For every \(\delta>0\), an exactly \(R\)-local
coefficient family with \(|J_S|<\delta\) attains the ceiling while the
Hamiltonian remains diagonal and every l-bit charge remains conserved.

Every such support lies in the interval beginning at its leftmost site, so
the formally proved explicit bound is
\[
  |\mathcal S_{n,R}|\le n\,2^{R+1},
  \qquad
  \boxed{\tau(J)\le n\,2^{R+1}.}
\]
Thus fixed-range commuting localized interactions have temporal dimension
linear in system size.

The sharper still-unformalized elementary closed count is
\[
  |\mathcal S_{n,R}|=(n-R+1)2^R-1
  \qquad (R<n).
\]
It cannot be used as a theorem until its exact combinatorial identity is
formalized; the proved dimension-linear bound is sufficient for the
locality separation.

## Formal declarations

- `LBitSupportRangeAtMost`;
- `lbitGeometricSupports`;
- `lbitTemporalRank_le_geometricSupports`;
- `lbitTemporalRank_eq_geometricSupports_card`;
- `exists_small_geometricLBit_maximalLocalRank`;
- `lbitGeometricSupports_subset_windowSupports`;
- `card_lbitGeometricSupports_le_linear`;
- `lbitTemporalRank_le_geometric_linear`.

## Scope

This is a commuting diagonal l-bit locality theorem. It is false as a
blanket ceiling for generic noncommuting local Hamiltonians.

## Verification

Direct target compilation passed with:

```text
lake env lean GaloisForLFunctions/HTGeometry/LBitGeometricLocalityLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/LBitGeometricLocalityLaw.olean
```

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Final `lake build` audit is reserved for publication audit.
