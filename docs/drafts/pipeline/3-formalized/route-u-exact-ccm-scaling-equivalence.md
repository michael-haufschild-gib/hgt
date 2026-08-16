# Route U exact CCM scaling equivalence

- **ID:** `route-u-exact-ccm-scaling-equivalence`
- **Stage:** 3-formalized
- **Type:** THEOREM / exact source-form equivalence and obstruction classification
- **Routes:** U primary; CCM restricted-Weil bridge
- **Source:** Route-U hard-edge density, Suzuki logarithmic form domain, exact CCM source formula

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Result

Put `c=2*pi`. Normalized spectral dilation by `c` is a continuous linear equivalence from the
complete Route-U logarithmic form domain at angular-frequency aperture `a` onto the complete CCM
archimedean form domain at physical aperture `c*a`. It is onto, not merely an embedding.

For every Route-U form vector `f`, all three literal source blocks scale by the same factor two:

```text
CCM_arch(c*a, D_c f)   = 2 RouteU_arch(a,f),
CCM_prime(c*a, D_c f)  = 2 RouteU_prime(a,f),
CCM_polar(c*a, D_c f)  = 2 RouteU_polar(a,f).
```

Consequently the exact closed source quadratics satisfy

```text
ccmRestrictedWeilSourceQuadratic(c*a, D_c f)
  = 2 routeUClosedSourceQuadratic(a,f).                    (U-CCM)
```

The Route-U quadratic is also exactly its literal hard-edge density plus polar carrier:

```text
routeUClosedSourceQuadratic(a,f)
  = integral routeUHardEdgeDensity(c*a,x) |g_f(x)|^2 dx
      + (c/2) routeUClosedPolarQuadratic(a,f).              (U-DENS)
```

No smoothing, asymptotic source, or privileged test subspace occurs. Surjectivity upgrades
`(U-CCM)` to global equivalences:

```text
(forall f, RouteU(a,f) >= 0)
  iff (forall q in complete CCM domain at c*a, CCM(c*a,q) >= 0),

(exists f, RouteU(a,f) < 0)
  iff (exists q in complete CCM domain at c*a, CCM(c*a,q) < 0).
```

Thus incoming Route-U PSD is exactly full restricted-Weil positivity after forced normalization.
It cannot be obtained by treating Route U as a smaller benign source class.

## Heavy conjecture loop

### U-C1 — Route U and CCM differ only cosmetically

**Conjecture.** Replacing angular frequency by ordinary Fourier frequency aligns prime shifts but
leaves incompatible archimedean or polar normalizations.

**Attack.** Track normalized dilation through Fourier inversion, logarithmic translation, Gamma
phase density, and both polar evaluation vectors. Prime translations move from
`log n/(2*pi)` to `log n`; archimedean Jacobian and both polar vectors each produce factor two.

**Verdict:** false as an obstruction. Every block has one common factor, giving `(U-CCM)`.

### U-C2 — scaling lands only in a special CCM subspace

**Conjecture.** Even with pointwise energy equality, Route U might test only a proper CCM sector,
so its positivity wall could remain weaker.

**Attack.** Construct inverse logarithmic Fourier dilation by `2*pi`, prove both compositions are
identity, and compose with existing CCM/log-form equivalence.

**Verdict:** false. Scaling is a continuous linear equivalence onto whole complete form domain.

### U-C3 — exact hard-edge density is still only heuristic shorthand

**Conjecture.** Finite von Mangoldt translations cannot be reassembled into literal Route-U
density without an unproved exchange or integrability premise.

**Attack.** Aperture makes prime range finite. Prove Gamma and cosine-weighted `L1` bounds from
the logarithmic form domain, exchange only finite sums, and use exact Fourier-translation cosine
identity.

**Verdict:** false. `(U-DENS)` is a closed Lean theorem.

## Higher universal principle

**Route U is a coordinate chart of restricted Weil positivity, not a separate positivity
mechanism.** Its apparent half-log prime wall is the shadow of using angular rather than ordinary
Fourier frequency. The forced `2*pi` dilation simultaneously aligns aperture, prime translations,
Gamma density, and polar evaluations.

This reclassifies open core. Entire-root factorization and literal compact admission remain useful
for producing a distinguished vector, but unrestricted incoming PSD cannot be proved from local
hard-edge geometry alone: it is already full CCM/Weil wall. A viable Route-U advance must exploit
additional structure of actual root-quotient sequence to obtain strictness or pre-wall exclusion,
not attempt generic form positivity.

## Lean closure

Module:

- `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeCCMScalingBridge.lean`.

Capstones:

- `routeUCCMHlogFormEquiv` and `routeUCCMFormEquiv`;
- `routeUClosedSourceQuadratic_eq_density`;
- `ccmRestrictedWeilSourceQuadratic_routeUToCCMFormVector`;
- `routeUClosedSourceQuadratic_nonnegative_everywhere_iff_ccm`;
- `routeUClosedSourceQuadratic_negative_exists_iff_ccm`.

Direct `lake env lean` passed. Exact leaf `lake build
GaloisForLFunctions.RHTower.XiShiftedHardEdgeCCMScalingBridge` passed. Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is imported by `RHTower.lean`; no umbrella
build was run.

## Gates

- [x] 0 -> 1: normalization, surjectivity, and density conjectures attacked
- [x] 1 -> 2: dependency-closed proof and corpus collision audit
- [x] 2 -> 3: direct Lean check, exact leaf build, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Log

- 2026-08-16 — Forced `2*pi` aperture and spectral dilation constructed.
- 2026-08-16 — Prime, archimedean, and polar blocks proved to share exact factor two.
- 2026-08-16 — Scaling proved onto complete CCM form domain.
- 2026-08-16 — Global PSD and negative-witness equivalences formalized.
- 2026-08-16 — Literal hard-edge density identity formalized.
