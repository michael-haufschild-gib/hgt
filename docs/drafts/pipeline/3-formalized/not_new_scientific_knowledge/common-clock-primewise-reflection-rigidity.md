# Common-clock primewise reflection rigidity

- **ID:** `common-clock-primewise-reflection-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / RH ROUTE COMPONENT
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeEulerCommonClockRigidity.lean`
- **Statement:** Independent neutral phases exist at each prime, but one nonzero phase clock
  `tau*log p` cannot keep every prime Euler denominator reflected-modulus neutral at a genuine
  strip displacement.

## Theorem

Let `0<=epsilon<1/2`, `tau>0`, and assume logarithmic prime-window supply at length
`pi/(2*tau)`. If every prime `p` satisfies

```text
|1-p^(-1/2+epsilon) exp(i tau log p)|
  = |1-p^(-1/2-epsilon) exp(i tau log p)|,
```

then `epsilon=0`.

The prime-window hypothesis is discharged in Lean by Bertrand whenever

```text
log 2 < pi/(2*tau).
```

For arbitrary `tau>0`, it is the standard short-log-window consequence of the prime number
theorem, isolated by the existing `PrimeWindowSupply` interface.

## Proof mechanism

Squaring the local modulus equality gives the exact identity

```text
cos(tau log p)
  = (p^(-1/2+epsilon)+p^(-1/2-epsilon))/2.                 (1)
```

If `epsilon<1/2`, the right side tends to zero as `p` tends to infinity. Logarithmic prime-window
supply produces arbitrarily large primes with

```text
cos(tau log p) >= sqrt(2)/2,
```

contradicting `(1)` when `epsilon>0`.

## Positive reading

The single-prime neutrality theorem is not merely an obstruction. Together with this theorem it
gives a sharp synchronization law:

```text
independent prime phases permit off-line neutrality;
one common prime clock plus cofinal prime recurrence pins the critical displacement.
```

Thus an RH-capable Euler source need not manufacture a new scalar local inequality. It must
positively upgrade its global completed balance to primewise balance while retaining the common
vertical clock. The missing information is cross-prime synchronization, not another one-prime
estimate.

## Top-down chain

The resulting fringe chain is

```text
source Gram/incidence law producing primewise common-clock neutrality
  -> common-clock primewise reflection rigidity
  -> approximant zeros have zero horizontal displacement
  -> closed zero-locus transfer
  -> RH.
```

Only the first arrow is open. The second arrow is formalized here; the last two are already
formalized in `LocallyUniformZeroTransfer.lean` and `PrimeEnergyZeroTransfer.lean`.

This is not the rejected scalar-modulus route. Scalar equality with a separately chosen phase at
each prime remains flexible. The theorem uses the non-product constraint that all phases arise
from the same clock.

## Lean certificates

- `cos_eq_radius_average_of_norm_one_sub_mul_eq`
- `cos_primeClock_eq_of_reflected_localFactor_modulus_neutral`
- `exists_prime_cos_pos_of_supply`
- `epsilon_eq_zero_of_cofinal_prime_reflected_modulus_neutral`
- `epsilon_eq_zero_of_cofinal_prime_reflected_modulus_neutral_of_log_two_lt_window`

The named capstones build successfully and use only `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] exact phase-cosine law formalized
- [x] cofinal positive-cosine prime steering formalized from `PrimeWindowSupply`
- [x] common-clock rigidity formalized
- [x] Bertrand low-clock hypothesis discharge formalized
- [ ] PNT-grade `PrimeWindowSupply L` formalized for every `L>0`
- [ ] source construction upgrading completed balance to primewise common-clock neutrality
- [ ] composition with a source-defined locally uniform approximant family

## Scientific status

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The ingredients are elementary local-factor algebra and standard
prime-gap consequences of PNT. The project value is the exact synchronization interface and its
formal separation from the false independent-phase mechanism.
