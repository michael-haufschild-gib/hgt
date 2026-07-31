# Anderson-localized resolution-scale recurrence law

- **Status:** formalized deterministic bridge
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteAndersonLocalizedResolutionScaleLaw`
- **Claim class:** `[LEAN-PROVED] [BRIDGE]`

## Result

At spatial scale \(N\), suppose the localization ball contains at most
\[
 |S_N|\le V(N+1)^\nu
\]
spectral sectors and the exponential localization and shell-growth
certificates of the finite localized survival law hold. Setting phase
resolution \(Q=2^N-1\) gives an exhaustive never-exits or strictly
post-exit-return alternative with
\[
 n\le 2^{N\left(V(N+1)^\nu-1\right)}
\]
and survival deviation
\[
 1-S_p(t_{\rm ret})\le
 4\,\mathrm{GeometricTail}(C,\mu,A,B,N)+\frac{4\pi}{2^N}.
\]

Thus error decreases exponentially in resolution scale, while the binary
logarithm of the certified deadline has explicit degree-\(\nu+1\)
polynomial growth. Neither expression contains ambient spectral dimension.

## Formal declarations

- `exists_finiteAndersonLocalizedSurvival_resolutionScale_recurrence`
- `finiteAndersonLocalizedSurvival_resolutionScale_neverExits_or_postExit_return`

## Verification

Direct foreground compilation passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

The theorem is unconditional as a deterministic implication from explicit
localization and shell certificates. It does not prove those certificates
for a named random Anderson ensemble.
