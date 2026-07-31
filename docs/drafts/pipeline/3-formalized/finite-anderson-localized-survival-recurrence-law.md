# Finite Anderson-localized survival recurrence law

- **Status:** formalized deterministic capstone
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteAndersonLocalizedSurvivalRecurrenceLaw`
- **Claim class:** `[LEAN-PROVED] [BRIDGE]`

## Result

Let \(p_i\ge0\), \(\sum_i p_i=1\), label each spectral mode by a distance
\(r_i\) from a local observer, and assume
\[
  p_i\le C e^{-2\mu r_i},\qquad
  \#\{i:r_i=m\}\le AB^m,\qquad
  B e^{-2\mu}<1.
\]
For the localization ball \(S_R=\{i:r_i\le R\}\), define
\[
  \beta_R=
  AC\frac{(B e^{-2\mu})^{R+1}}{1-B e^{-2\mu}}.
\]
If \(S_R\ne\varnothing\), then some positive integer \(n\) satisfies
\[
  n\le(Q+1)^{|S_R|-1},
  \qquad
  |S_p(n)-1|\le4\beta_R+\frac{4\pi}{Q+1},
\]
where
\[
  S_p(t)=\left|\sum_i p_i e^{itE_i}\right|^2
\]
is local survival probability. If \(|S_R|\le V_{\rm eff}\), the deadline is
at most \((Q+1)^{V_{\rm eff}-1}\).

The same budget obeys an exhaustive escape–return law: either local
survival never leaves the guaranteed neighborhood, or an exit is followed
strictly later by a return before the localization-volume deadline.

## Formal declarations

- `finiteLocalizationBall`
- `finiteLocalizationGeometricTailBound`
- `finiteLocalizedSubsetTail_localizationBall_eq`
- `finiteLocalizedSpectralDeviation_eq_survivalDeviation`
- `exists_finiteAndersonLocalizedSurvival_recurrence`
- `exists_finiteAndersonLocalizedSurvival_volume_recurrence`
- `finiteAndersonLocalizedSurvival_neverExits_or_postExit_return`

## Verification

```text
lake env lean \
  GaloisForLFunctions/RHTower/FiniteAndersonLocalizedSurvivalRecurrenceLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/FiniteAndersonLocalizedSurvivalRecurrenceLaw.olean
```

passed. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Scientific meaning

Spatial localization compresses the phase network a local observer must
resynchronize. Accuracy is paid by exponentially small spectral tail;
deadline is paid by modes inside localization volume, not total system
size.

## Boundary

This capstone does not prove that a standard Anderson ensemble supplies the
site-labelled eigenbasis and uniform decay constants in its hypotheses.
Until such a model-specific theorem is formalized, manuscript wording must
be “localized eigensystems” or “deterministic Anderson-localization
interface,” not “all Anderson Hamiltonians.”
