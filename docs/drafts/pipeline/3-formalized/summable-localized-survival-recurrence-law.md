# Countably infinite localized survival recurrence law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.SummableLocalizedSurvivalRecurrenceLaw`
- **Claim class:** `[LEAN-PROVED] [LOCALIZATION TRANSFER]`

## Result

For every normalized nonnegative countable pure-point spectral packet, any
proved tail certificate
\[
 \sum_{j=0}^{\infty}p_{M+j}\le\alpha
\]
gives survival budget
\[
 B^{\mathrm{loc}}_{M,Q}=
 \left(\frac{2\pi}{Q+1}\right)^2
   \sum_{k=1}^{M-1}p_k+4\alpha.
\]
If the visible head contains \(M\le V\) modes, either survival loss never
exceeds this budget, or an exit is followed strictly later by a return with
\[
 1\le n\le(Q+1)^{V-1}.
\]

This composes genuine countably infinite survival recurrence with a
localization-volume certificate: countable ambient support affects only the
tail error, while visible volume controls the temporal exponent.

## Formal declarations

- `summablePurePointSurvivalRecurrenceBudget_le_localized`
- `exists_summableLocalizedSurvival_recurrence`
- `exists_summableLocalizedSurvival_volume_recurrence`
- `summableLocalizedSurvival_neverExits_or_postExit_return`

## Verification

Direct foreground compilation passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

The theorem consumes a proved spectral-tail bound. It does not itself prove
Anderson localization for a named random Hamiltonian or handle continuous
spectral mass.
