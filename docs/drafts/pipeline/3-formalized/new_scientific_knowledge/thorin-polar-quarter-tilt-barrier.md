# Thorin polar-quarter tilt barrier

- **ID:** `thorin-polar-quarter-tilt-barrier`
- **Stage:** 3-formalized
- **Type:** `[NEW SCIENTIFIC KNOWLEDGE] [NO-GO THEOREM] [SOURCE-ROUTE CLASSIFICATION]`
- **Source:** `completed-seam-thorin-subordinator-rh.md`; Nicholas G. Polson,
  *Riemann, Thorin, van Dantzig Pairs, Wald Couples and Hadamard Factorisation*,
  arXiv:1804.10043v8 (29 April 2026), Theorems 23 and 25
- **Statement:** In every square-radius auxiliary continuation based at
  `1/2 + sqrt(r)`, `r > 1/4`, separating the completed polar factor as a positive
  Thorin atom produces an exponential component of rate `r - 1/4`, while transport
  to the critical center requires exponential tilt by `r`. The required tilted mass
  diverges, with invariant deficit exactly `1/4`. Hence pole--zeta cancellation must
  occur before any positive Thorin decomposition.

## Goal

Audit a claimed right-to-left closure of the critical Thorin condition and isolate
the strongest reusable survivor. This card does not prove RH. It rules out a
specific positivity-preserving continuation mechanism and narrows open cores A--C
of `completed-seam-thorin-subordinator-rh.md` to a coupled completion construction.

## Exact setup

For `r > 1/4`, put

```text
phi_r(s) = xi(1/2 + sqrt(r)) / xi(1/2 + sqrt(r+s)).
```

The elementary completed polar factor in the denominator is

```text
(r - 1/4) / (r + s - 1/4),
```

the Laplace transform of `X_r ~ Exp(r - 1/4)`. Reflection from the
Euler-safe radius `r` to the critical center replaces `s` by `r-s`; on a
probabilistic representation this is exponential tilting by `r` and requires

```text
E[exp(r X_r)] < infinity.
```

But

```text
E[exp(theta X_r)]
  = integral_0^infinity (r-1/4) exp((theta-(r-1/4))x) dx
```

is finite exactly when `theta < r-1/4`. At `theta=r` the exponent is
`x/4`, so the integral diverges. Equivalently,

```text
required tilt - polar rate = r - (r - 1/4) = 1/4.
```

The obstruction is independent of aperture `r`.

## Hostile audit of the 2026 claim

At `r=1`, Theorem 23 of arXiv:1804.10043v8 explicitly assigns the auxiliary
Thorin measure an atom `delta_(3/4)`. Therefore the proposed auxiliary GGC
contains an independent `Exp(3/4)` component. Theorem 25 then defines a critical
law by density proportional to `exp(x)` and asserts
`M = E[exp(H_star)] < infinity`. The atom alone gives

```text
E[exp(H_star)] >= E[exp(Exp(3/4))] = infinity.
```

The paper's integrability sentence overlooks its own atom below the tilt:
`3/4 < 1`. Its alternative identification of `M` by evaluating the derived
identity at `s=0` is circular because that identity was obtained only on the
open strip and its direct Mellin integral already diverges for
`Re(s) >= 3/4`.

There is a second source-side check. The apparent pole at `s=-3/4` is canceled
in the completed xi ratio by the zeta pole at argument `1`; the completed ratio
is finite there. Treating the rational polar factor and zeta factor as separate
positive Thorin pieces destroys precisely this cancellation. This agrees with
the corpus theorem that divided prime and archimedean singularities must be
coupled before positivity is tested.

## Paper proof

1. For `a>0`, the exponentially tilted `Exp(a)` density is
   `a exp((theta-a)x)` on `(0,infinity)`.
2. The integral of `exp(c x)` on `(0,infinity)` is finite iff `c<0`:
   for `c<0`, integrate the decaying exponential; for `c>=0`, the integrand is
   at least `1` and the half-line has infinite Lebesgue measure.
3. Hence the tilted exponential mass is finite iff `theta<a`.
4. Set `a=r-1/4` and `theta=r`. Since `r-a=1/4>0`, the tilted mass diverges.
5. The identity is aperture-independent, so no larger Euler-safe base radius
   repairs the separated-factor construction.

No RH input, zero divisor, estimate, or numerical computation occurs.

## No-go closure

- **Exact killing theorem/mechanism:** separated positive polar atom has rate
  `r-1/4`, strictly below the tilt `r` needed to reach the critical center; its
  exponential moment diverges.
- **Strongest positive survivor:** any viable Thorin source construction must
  combine the polar factor with the zeta-pole channel before taking a positive
  measure. Equivalently, its positive Thorin measure cannot retain the raw
  polar atom `delta_(r-1/4)` as an independent summand.
- **New insight:** failure is a fixed completion invariant `1/4`, not a weak
  growth estimate and not a poor choice of aperture. The surviving open core is
  a completion-sensitive mass transfer across this quarter-gap.
- **Status:** paper proof dependency-closed and formalized axiom-clean in
  `formal/GaloisForLFunctions/RHTower/ThorinPolarQuarterTiltBarrier.lean`.

## Gates

- [x] 0 → 1 in-progress: exact claim, source passport, hostile audit, and
      positive survivor stated
- [x] 1 → 2 fully-proven: dependency-closed paper proof above
- [x] 2 → 3 formalized: Lean theorems
      `integrableOn_thorinExponentialTiltKernel_Ioi_iff`,
      `centerTilt_sub_completedPolarRate`,
      `not_integrableOn_completedPolarCenterTilt`, and
      `not_integrableOn_threeQuarterPolarUnitTilt`; direct Lean check passed,
      final module audit pending
- [ ] 3 → 4 publication-ready: standalone note pending

## Literature classification

- Polson's April 2026 revision states the auxiliary atom and the critical tilt
  but does not detect their incompatible moment domains.
- General GGC/Thorin theory makes exponential tilting conditional on finiteness;
  it does not supply the missing moment.
- Classification: `[NEW]` as an explicit audit theorem for this critical-Xi
  continuation scheme; underlying exponential-moment calculation is classical.

## Log

- 2026-07-22 — created during backward RH-chain audit; exact `1/4` obstruction
  extracted from the latest claimed critical-Thorin closure.
