# A reflected Euler factor is modulus-neutral off the critical line

- **ID:** `prime-euler-reflected-modulus-neutrality`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SCALAR SOURCE NO-GO
- **Scientific status:** `[PROVED HERE] [BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeEulerReflectedModulusNeutrality.lean`
- **Statement:** At every prime and every nonzero reflection displacement inside the critical
  strip, there is a unit phase for which the two reflected local Euler denominators have exactly
  equal modulus.

## Exact law

For `0<r_-<r_+<1`, put

```text
c=(r_++r_-)/2,
theta=arccos(c).
```

Then

```text
|1-r_+ exp(i theta)|^2=1+r_+^2-2r_+ cos(theta),
|1-r_- exp(i theta)|^2=1+r_-^2-2r_- cos(theta),
```

and substitution of `cos(theta)=c` makes the two expressions equal.  Hence their nonnegative
square roots are equal.

For a prime `p` and `0<epsilon<1/2`, take

```text
r_+=p^(-1/2+epsilon),
r_-=p^(-1/2-epsilon).
```

These satisfy `0<r_-<r_+<1`, so there is a phase `theta` with

```text
|1-p^(-1/2+epsilon) exp(i theta)|
  =|1-p^(-1/2-epsilon) exp(i theta)|.                      (1)
```

## Top-down consequence

The finite-prime theta screen has two reflected scalar flanks.  At a zero of their even sum, the
flanks have equal modulus.  Equation `(1)` proves that such scalar modulus balance cannot force
`epsilon=0`, even locally at one prime.  It therefore cannot imply the phase-independent reflected
prime energy used by `PrimeEnergyZeroTransfer.lean`.

The missing RH-bearing source theorem must retain more than one scalar flank.  It needs a faithful
prime-coordinate or positive vector coupling which turns scalar divisor cancellation into control
of the reflected prime displacement.  This agrees with the periodic-pencil dimension obstruction:
a nonpure prime/reflection relation cannot be carried by one scalar analytic clock.

## Lean certificate

```text
RHTower.norm_one_sub_real_mul_exp_mul_I_sq
RHTower.exists_phase_norm_one_sub_mul_eq
RHTower.exists_prime_reflected_localFactor_modulus_neutral
```

## Gates

- [x] exact unit-circle norm formula
- [x] neutral phase for arbitrary `0<r_-<r_+<1`
- [x] prime reflected-factor specialization
- [x] scalar theta-screen modulus route excluded
- [ ] construct a two-direction source-divisor coupling

## Positive common-clock sequel (2026-07-11)

The independent-phase flexibility disappears when all prime phases come from one vertical clock.
`PrimeEulerCommonClockRigidity.lean` proves that cofinal primewise reflected-modulus neutrality with
phase `tau*log p` forces the strip displacement to vanish. Thus the positive resource missing from
the scalar local theorem is cross-prime clock synchronization. See
`common-clock-primewise-reflection-rigidity.md`.
