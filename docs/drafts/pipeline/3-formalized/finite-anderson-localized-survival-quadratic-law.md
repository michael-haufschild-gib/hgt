# Quadratic Anderson-localized survival recurrence law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteAndersonLocalizedSurvivalQuadraticLaw`
- **Claim class:** `[LEAN-PROVED] [LOCALIZATION TRANSFER] [SHARPENING]`

## Result

For arbitrary normalized nonnegative finite Born weights, survival loss is
exactly half the squared Hilbert–Schmidt displacement of the corresponding
weighted pure-state density matrix. For a nonempty retained localized set
\(S\) with exterior spectral mass at most \(\alpha\),
\[
 n\le(Q+1)^{|S|-1},\qquad
 1-S_p(n)\le
 4\alpha+2\left(\frac{2\pi}{Q+1}\right)^2.
\]
The same quadratic budget obeys a never-exits/post-exit-return law.

Exponential site-weight decay and shell growth replace \(\alpha\) by the
explicit geometric localization tail. If
\(|S_N|\le V(N+1)^\nu\) and \(Q=2^N-1\), then
\[
 n\le2^{N(V(N+1)^\nu-1)}
\]
and
\[
 1-S_p(n)\le
 4\,\mathrm{GeometricTail}(N)
 +2\left(\frac{2\pi}{2^N}\right)^2.
\]

This removes the earlier linear phase-resolution remainder without changing
the localization-volume exponent.

## Formal declarations

- `finiteWeightedPureObserverUnionWeight`
- `finiteSpectralSurvivalDeviation_eq_half_weightedPureObserverDistanceSq`
- `exists_finiteLocalizedSurvival_quadratic_recurrence`
- `finiteLocalizedSurvival_quadratic_neverExits_or_postExit_return`
- `exists_finiteAndersonLocalizedSurvival_quadratic_recurrence`
- `finiteAndersonLocalizedSurvival_quadratic_neverExits_or_postExit_return`
- `exists_finiteAndersonLocalizedSurvival_quadratic_volume_recurrence`
- `exists_finiteAndersonLocalizedSurvival_quadratic_resolutionScale_recurrence`
- `finiteAndersonLocalizedSurvival_quadratic_resolutionScale_neverExits_or_postExit_return`

## Verification

Direct foreground compilation passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

The theorem is a deterministic transfer from explicit finite spectral
localization and shell-growth certificates. It does not assert that every
Anderson ensemble supplies them or prove a thermodynamic-limit localization
theorem.
