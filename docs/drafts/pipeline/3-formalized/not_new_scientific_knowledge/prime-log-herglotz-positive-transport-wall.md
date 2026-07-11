# Prime-log Herglotz features fail every positive exponential transport

- **ID:** `prime-log-herglotz-positive-transport-wall`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Source:** `PrimeLogHerglotz.lean` and
  `euler-log-prime-power-herglotz-half-weight-law.md`
- **Statement:** For every positive transport width `b` and every finite cancellation order `m`,
  the prime-log Herglotz feature mass
  `p^(2b-1)/(1+(log p)^2)^m` is not summable over the primes.

## Goal

Certify the exact analytic wall encountered when a positive prime-log Cauchy carrier is transported
toward the critical center. This is a source-side obstruction theorem, not an RH criterion.

## Proof

For `b>0` and `m>0`, put `beta=b/m`. The elementary bound

```text
log p <= p^(beta/2)/(beta/2)
```

gives a constant `C_beta>0` such that

```text
1+(log p)^2 <= C_beta p^beta.
```

Raising to the `m`-th power gives

```text
(1+(log p)^2)^m <= C_beta^m p^b.
```

Therefore

```text
p^(2b-1)/(1+(log p)^2)^m >= C_beta^(-m) p^(b-1).
```

The prime power series `sum_p p^r` converges exactly when `r < -1`. Here `r=b-1>-1`, so the lower
bound is nonsummable and hence so is the transported feature mass. The case `m=0` is the direct
prime-power-series threshold.

## Route consequence

The prime-log pole set and positive residues provide a genuine Herglotz carrier, but no positive
exponential conjugation of its canonical Cauchy features is defined at the Hilbert level. More
strongly, no finite rational cancellation order at infinity repairs the transported feature.
Combined with the paper theorem
`prime-log-cauchy-seam-infinite-renormalization-rank.md`, this is the analytic core forcing every
additive prime-side repair of the complete Cauchy family to have infinite-dimensional correction
range. A successful route must use an infinite prime--Gamma coupling, a relative covariance, or
another source-sewn carrier rather than finite-rank continuation of the positive prime facet.

## Gates

- [x] 0 -> 1: all finite cancellation-order masses isolated from the prime-log carrier
- [x] 1 -> 2: uniform finite-order comparison with a nonsummable prime power proved
- [x] 2 -> 3: formalized as
  `GaloisForLFunctions.HTGeometry.not_summable_primeLogHerglotzTransportMassOrder_of_pos`; the
  original one-denominator theorem remains available as
  `GaloisForLFunctions.HTGeometry.not_summable_primeLogHerglotzTransportMass_of_pos`
- [ ] 3 -> 4: not publication-targeted; standard prime-series boundary theory

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/PrimeLogHerglotz.lean` -- pass
- `lake build GaloisForLFunctions.HTGeometry.PrimeLogHerglotz` -- pass
- theorem axioms: `[propext, Classical.choice, Quot.sound]`

## Scientific status

The formal analytic estimate uses the standard logarithm-versus-power bound and the classical
convergence threshold for prime power series. It is not new scientific knowledge by itself. Its
value is to certify the all-orders input to the novelty-unverified quotient-rank theorem and to
prevent finite cancellations from being mistaken for a critical-line transport.

## Log

- 2026-07-11 -- formalized from the `PrimeLogHerglotz.lean:211` route audit.
- 2026-07-11 -- strengthened from one Cauchy denominator to every finite cancellation order.
