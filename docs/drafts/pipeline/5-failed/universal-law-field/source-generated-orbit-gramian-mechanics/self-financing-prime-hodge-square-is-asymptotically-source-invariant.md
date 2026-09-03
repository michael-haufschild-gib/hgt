# Self-financing prime--Hodge square is asymptotically source-invariant

- **ID:** ULF-SGOGM-FAIL-005
- **Stage:** 5-failed
- **Status:** `[FALSIFIED]`
- **Positive survivor:** ULF-PCOB-001 cubic boundary covariance

## Claim

The exact finite-capital defect `mathsf D_d=mathsf T_d^2` should become approximately invariant
under the prime-clock generator `I tensor L` as aperture `d` closes, allowing direct use of the
orbit-Gramian properness selector.

## Countertheorem

The normalized prime weights have the PNT scaling limit

```text
d log p -> y,   mu_d ->2exp(-2y)dy.
```

The cubic coherence depends only on ratios of prime clocks and stays uniformly positive on any
two fixed positive `y`-blocks.  Choosing separated blocks for `p` and `q`, with an intermediate
block for the convolution index in `A_d^2`, gives

```text
||[L,A_d^2]||_HS^2>=c/d^2.
```

Therefore

```text
||[I tensor L,mathsf T_d^2]||_HS->infinity.
```

The finite-capital square is not an almost-invariant defect; the failure is divergent, not a
missing estimate.

## Positive survivor

`mathsf T` is an inhomogeneous formation current with exact law

```text
S_(I tensor L)^3(mathsf T_d)=8Phi tensor |b_d><b_d|.
```

Future completion arguments must transport this source charge covariantly.  Requiring ordinary
commutation would delete the mechanism that forms the object.
