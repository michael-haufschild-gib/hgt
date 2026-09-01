# HCF Fixed Positive Shift

- **ID:** HCF-FIXED-SHIFT
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** Fixed positive boundary shifts are exact transverse-strip censuses, not HCF upper-bound statistics.

## No-go closure

- **Exact killing theorem:** For `η>0`, a conjugate pair has full-line kernel mass `−2π` when `|Im ρ|<η`, and `0` when `η<|Im ρ|`.
- **Strongest positive survivor:** Sharp fixed-shift strip-census classification.
- **New insight:** Sending `η→0` restores exactly mass of arbitrarily shallow off-line pairs; no fixed-shift estimate controls that recovery.
- **Status:** `[PROVED HERE]` and Lean-formalized as `integral_conjPairKernel_eq_neg_two_pi_of_abs_im_lt` / `integral_conjPairKernel_eq_zero_of_lt_abs_im` in `HTGeometry/BoundaryCauchyKernel.lean`; targeted build and axiom audit pass.

## Proof

Write pair kernel as two Cauchy kernels of signed scales `η−Im ρ` and `η+Im ρ`. Each integrates to `−π` for positive scale and `+π` for negative scale. Signs agree inside strip and cancel outside.
