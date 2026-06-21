# C-2026-06-18-039 Proof Attempt: Two-Variable Kernel

Source: `docs/consolidated/08-conjectures-required.md` §4.

Claim status: `[CONJECTURE]`.

## Target Claim

```text
K_MS(s,w) ~ (1 - phi(s) conj(phi(w))) / (s + conj(w) - 1),
phi = Theta,
RH <=> K_MS in N_0.
```

## Attempt

This is a generalized Nevanlinna/Pick-kernel route. The desired theorem is that
the number of negative squares of `K_MS` equals the number of off-line zero
pairs. Then membership in `N_0` means zero negative squares, hence RH.

## Weakened Theorem

If a Hermitian kernel `K` has negative-square index

```text
sq_-(K) = # off-line zero pairs,
```

then `K in N_0` is equivalent to RH.

## Obstruction

The kernel is only sketched. The denominator suggests a half-plane
de Branges-Rovnyak or Pick kernel, but the function `phi`, domain, boundary
normalization, and exact negative-square theorem are not supplied.

## Missing

Define `K_MS`, prove it is Hermitian on the relevant half-plane, identify its
negative squares with the faithful carrier, and show this construction is
source-built rather than zero-fed.
