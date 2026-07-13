# Finite graded-spectrum cancellation leaves positive cohomology

- **ID:** `finite-graded-spectrum-positive-cohomology`
- **Stage:** 3-formalized
- **Type:** `[POSITIVE SUCCESSOR TO A NO-GO] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/GradedSpectrumCancellation.lean`
- **Parent:** `../../1-in-progress/prime-arch-koszul-spectral-quotient-cancellation-rh.md`

## Statement

Let a finite graded real spectrum have even multiset

```text
E=R+P
```

and odd multiset `O=P`, where `P` is the paired spectrum and `R` the unpaired residual spectrum.
Then for every `n`,

```text
Str(T^n)=sum_(lambda in E) lambda^n-sum_(lambda in O) lambda^n
         =sum_(lambda in R) lambda^n.                    (1)
```

If every residual eigenvalue is nonnegative, every power supertrace in `(1)` is nonnegative.  Thus
a signed virtual spectrum need not itself be a positive moment object: positivity is recovered on
the unpaired cohomology after an explicit equal-spectrum cancellation.

## Positive interpretation

The pointwise-moment-quotient obstruction does not say that graded determinant routes are useless.
It identifies the exact additional theorem they require: construct a differential whose odd modes
are matched by equal even modes, and prove that the unpaired even cohomology is nonnegative.  Only
after that pairing is source-defined may its residual power sums be used in a positive Fredholm
determinant.

## Lean surface

```text
multisetPowerSum
gradedPowerSum
multisetPowerSum_add
gradedPowerSum_common_cancel
multisetPowerSum_nonneg
gradedPowerSum_common_cancel_nonneg
```

## Gates

- [x] finite equal-spectrum cancellation formalized
- [x] nonnegative residual power-sum theorem formalized
- [ ] trace-class cofinal version with a closed differential formalized

