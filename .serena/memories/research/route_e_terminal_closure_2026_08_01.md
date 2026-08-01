# Route E terminal closure (2026-08-01)

Route E is closed as an independent finite/local mechanism, not as a proof of RH.

## New formal theorems

- `formal/GaloisForLFunctions/RHTower/MobiusFinitePrimeApertureSourceConsumption.lean`: any finite aperture covering primes through `N` exactly recovers Möbius coefficients, Mertens partial sums, and Mertens self-convolution at `N`; canonical aperture second-Cesàro subpower upper bound is iff the existing open source law and therefore implies RH.
- `formal/GaloisForLFunctions/RHTower/MobiusGammaHankelTransverseEscapeCone.lean`: nonempty right-half Xi divisor forces Gamma--Hankel covariance escape throughout the maximal strict cone below `1/2 + xiRightTransverseSup`; frequent bounded returns at `sigma` force `xiRightTransverseSup <= sigma - 1/2`.

Both modules are imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Cards

Promoted to Stage 3:
- `docs/drafts/pipeline/3-formalized/route-e-finite-prime-aperture-source-consumption.md`
- `docs/drafts/pipeline/3-formalized/route-e-gamma-hankel-transverse-escape-cone.md`

Frontier map marks Route E `[CLOSED AS INDEPENDENT MECHANISM]`. Remaining source lies outside this mechanism: a genuinely nonlocal all-prime signed cancellation theorem, which is RH-strength through existing consumers.

## Verification

Both direct `lake env lean` checks passed. Targeted module builds passed at 8962/8962 and 9008/9008. Load-bearing `#print axioms` outputs contain only `propext`, `Classical.choice`, and `Quot.sound`; no sorry/admit/axiom/opaque/unsafe. User stopped and prohibited full builds, so no completed umbrella build. Non-build global lint reached Route E cleanly but exited on four unrelated concurrent un-wired modules plus stale generated indexes.