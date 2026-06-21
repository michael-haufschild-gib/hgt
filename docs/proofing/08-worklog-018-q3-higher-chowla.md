# C-2026-06-18-018 Proof Attempt: Q3 / Higher-Chowla Discriminator

Source: `docs/consolidated/08-conjectures-required.md` §4.

Claim status: `[CONJECTURE]`.

## Target Claim

The leading Loewner PSD object `Q_1` is fake-blind; the first discriminator is
`Q_3`, a higher-cumulant or higher-Chowla source control whose readout is
`kappa_-`.

## Attempt

The plausible proof chain is:

```text
Q_3(source data) = faithful third-order response
sign/negative squares of Q_3 = kappa_-
kappa_- = # off-line zero pairs.
```

The reason to move from `Q_1` to `Q_3` is that first-order/PSD data can be
matched by fakes; a higher cumulant may see non-Gaussian source structure.

## Weakened Theorem

If a source-built `Q_3` has negative-square index equal to `kappa_-`, then
positivity of `Q_3` implies RH.

## Obstruction

No formula connects `Q_3` to the explicit-formula faithful index. Higher-order
statistics can be more discriminating, but discrimination is not proof unless
the readout is tied to divisor charge.

## Missing

Define `Q_3`, prove fake-family separation, and prove its index equals the
off-line zero count.
