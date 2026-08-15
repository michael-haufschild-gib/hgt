# Li Kernel Is Not Coefficientwise Positive — Lean certificate

- **ID:** `li-kernel-not-coefficient-positive-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `li-kernel-not-coefficient-positive.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Lean module

`GaloisForLFunctions.RHTower.LiReciprocalKernelCoefficientSign`
(umbrella: `GaloisForLFunctions.RHTower`).

## Exact certificates

- `liReciprocalKernel` is the literal real reciprocal-seam kernel
  `2 - 2 * T_n ((4-y)/(4+y))`, with mathlib's first-kind Chebyshev polynomial
  `Polynomial.Chebyshev.T`.
- `liReciprocalTaylorCoeff` is defined by the actual Taylor formula
  `iteratedDeriv k liReciprocalKernel 0 / k!`.
- `liReciprocalTaylorCoeff_one` proves
  `c_(n,1) = n^2`; `liReciprocalTaylorCoeff_two` proves
  `c_(n,2) = -n^2 (n^2 + 2) / 12` for every natural `n`.
- `liReciprocalTaylorCoeff_one_pos` and `liReciprocalTaylorCoeff_two_neg`
  establish the strict signs for every `n >= 1`.
- `liReciprocalKernel_not_coefficientwise_nonnegative` gives the resulting
  reciprocal-moment obstruction.
- Closed capstone `liReciprocalKernel_coefficient_sign_obstruction` packages
  both coefficient identities, both signs, and the contradiction in one
  universal declaration.
- `liReciprocalKernel_one` and
  `liReciprocalKernel_one_first_two_coefficients` certify the paper's
  `n = 1` identity `4y/(4+y)` and coefficients `1`, `-1/4`.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/LiReciprocalKernelCoefficientSign.lean`
  — clean.
- `lake build GaloisForLFunctions.RHTower.LiReciprocalKernelCoefficientSign`
  — green.
- `#print axioms` for the universal capstone and the `n = 1` coefficient
  certificate: `[propext, Classical.choice, Quot.sound]` only.
- Source declaration scan found no forbidden proof-debt declaration.

## Scope boundary

This certifies exactly the coefficientwise sign obstruction.  It does not
assert Li positivity, RH, or a new positivity-preserving bridge; instead it
rules out the specified coefficientwise-positive reciprocal-moment shortcut.
