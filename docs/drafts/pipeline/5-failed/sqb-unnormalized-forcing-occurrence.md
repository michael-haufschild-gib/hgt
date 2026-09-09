# SQB unnormalized forcing smallness as occurrence

Status: proposed inference excluded; positive survivor paper-proved and audited in Lean.

## Excluded inference

For actual unit native forcing vectors f_n, vanishing of the unnormalized
entire residual `||R_e f_n−(2+mu)C R_e f_n||` does not establish normalized
spectral occurrence. The actual response norm must remain in the comparison.

The original pre-divisor cusp packets construct one unit family with
`||B f_n||≤2/(n+1)`. For every actual Xi resolvent, its complete response and
entire covariance response both tend to zero. The unnormalized residual tends
to zero at every complex target, including i. Every normalized response at i
has residual at least one. This rules out the inference without assuming any
off-critical Xi zero exists.

This does not retire the full SQB interface or exclude every normalized
source family. The normalized residual of this forcing family at general
actual Xi targets is not classified.

## Strongest positive survivor

The exact bounded identity `R_e=(I+e R_e)B` transfers covariance disappearance
to full resolvent disappearance. The construction supplies actual unit vectors
in the original native graph domain, a quantitative covariance bound, all
complex-target numerator limits, positive normalization denominators, and
the exact normalized residual quotient.

Independently, the continuous approximate-kernel theorem proves that every
successful bounded entire family must concentrate in the original native
covariance fibre. Actual unit entire approximate families yield native-domain
unit approximate families differing from them by a norm error tending to zero.

The [dependency-closed proof and Lean audit](../3-formalized/sqb-native-spectral-concentration.md)
contains the full statements and retained hypotheses. The survivor is
formalized in `SelbergScatteringForcingEscape`; the concentration law is in
`CfcApproximateKernel` and `SelbergScatteringSpectralConcentration`.
