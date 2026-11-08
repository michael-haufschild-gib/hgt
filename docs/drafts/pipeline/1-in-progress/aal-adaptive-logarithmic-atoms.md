# Adaptive logarithmic atoms

- **ID:** aal-adaptive-logarithmic-atoms
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Question:** Can atom widths proportional to `1/n` retain arithmetic matrix positivity while replacing the depth-dependent aliasing penalty by an unweighted mass?

## Candidate

The existing common width `c/N` gives local overlap `cn/N` at row `n`, hence aliasing density `aφ(c exp(y))` at logarithmic depth `y=log(n/N)`. Width `c/n` instead gives constant local overlap `c`. For a fixed limiting window, the candidate penalty is then `log(N) aφ(c) ∫H²`, with no exponential depth factor. A uniform lower floor for the actual Weil form could exclude off-line reflected pairs.

## Open steps

The current whole-matrix theorem assumes one common atom profile and width. Its Fourier factorization and prime-row estimates do not apply to variable widths. Establish the mixed-profile archimedean and prime estimates, including the polar term, before asserting positivity. Local width matching alone proves neither a uniform lower floor nor AAL.

## Status

The constant-overlap limit and the necessary positivity estimate are unproved.
