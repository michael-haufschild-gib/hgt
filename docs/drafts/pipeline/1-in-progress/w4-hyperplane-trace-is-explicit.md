# W4 — the hyperplane trace is explicit

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** If `B_m` counts nonzero `m`-tuples with `1+Σx_j=0` over a field of size `q`, then `qB_m=(q−1)^m−(−1)^m`.

## Proof mechanism

The leading coordinate is uniquely forced by the tail and is nonzero exactly when the tail is outside the same hyperplane. Thus `B_{m+1}+B_m=(q−1)^m`, with `B_0=0`. Induction gives the formula. Over extension fields, its binomial expansion is a finite signed trace with eigenvalues integral powers of `q`.

## Role in the global identity

The existing moment identity becomes `M_{m+1}=q²A_m−(q−1)^m+(−1)^m`, where only the double-zero count `A_m` remains unknown. This determines the hyperplane contribution explicitly; it does not supply cohomology or the cancellation estimate for `A_m`, or construct the ζ family.
